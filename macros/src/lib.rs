extern crate macro_state;

use proc_macro::TokenStream;
use std::collections::hash_map::RandomState;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::ops::RangeInclusive;

use convert_case::{Case, Casing};
use darling::ast::NestedMeta;
use darling::{Error, FromAttributes, FromMeta};
use macro_state::*;
use quote::{format_ident, quote, ToTokens};
use syn::punctuated::Punctuated;
use syn::{
    parse_macro_input, Attribute, Block, Expr, ExprLit, Field, Fields, FnArg, GenericParam, Ident,
    ImplItem, ImplItemType, ItemEnum, ItemFn, ItemImpl, ItemStruct, Pat, PatIdent, PatType,
    PathSegment, Token, Type, TypeParamBound, TypePath, TypeTuple, Variant, Visibility,
};

const VERSION_KEY: &str = "diachrony-protocol-version";
/// Prefix for the key of the state keeping all the messages removed in a version.
const REMOVED_MESSAGES_PREFIX: &str = "diachrony-message-removal";
/// Prefix for the key of the state keeping all the messages added in a version.
const ADDED_MESSAGES_PREFIX: &str = "diachrony-message-addition";
const VERSION_DISPATCH_ARG_NAME: &str = "diachrony_added_version_arg";

type Version = u16;

#[derive(Default, Debug)]
struct VersionChange {
    // TODO: for removed fields, we probably don't need the field object, just the name.
    pub removed_fields: HashSet<Field>,
    pub new_fields: HashSet<Field>,
}

#[derive(Debug, FromMeta)]
struct MessageMacroArgs {
    group: Option<Ident>,
    from_version: Version,
    until_version: Option<Version>,
}

#[derive(Debug, FromMeta, Default)]
struct OptionalVersionRangeMacroArgs {
    from_version: Option<Version>,
    until_version: Option<Version>,
    // TODO: maybe a better interface would allow to just specify that word and not require also
    //       writing `=true` next to it.
    versioned: Option<bool>,
}

#[derive(Debug, FromMeta)]
struct SuperGroupMacroArgs {
    handler: Ident,
    from_version: Option<Version>,
    until_version: Option<Version>,
}

#[derive(Debug, FromMeta)]
struct HandlerMacroArgs {
    message_group: syn::Path,
    from_version: Option<Version>,
    until_version: Option<Version>,
}

impl FromAttributes for OptionalVersionRangeMacroArgs {
    fn from_attributes(attrs: &[Attribute]) -> darling::Result<Self> {
        Ok(attrs
            .iter()
            .find(|attr| {
                // TODO: is_ident is not good, because we also want to match diachrony::field (and we
                //  don't want to match `field` if it's not imported form diachrony.
                attr.path().is_ident("field")
            })
            .map(|attr| {
                // TODO: unwrap
                OptionalVersionRangeMacroArgs::from_meta(&attr.meta).unwrap()
            })
            .unwrap_or_default())
    }
}

#[proc_macro]
pub fn current_version(arg: TokenStream) -> TokenStream {
    let expr_lit = parse_macro_input!(arg as ExprLit);
    let syn::Lit::Int(ref lit_int) = expr_lit.lit else {
        panic!("Expected int literal (version) for current_version.");
    };
    let version = lit_int.to_string();
    proc_write_state(VERSION_KEY, &version).unwrap(); // TODO: unwrap?
    TokenStream::new()
}

// TODO: doctests are failing.
/// Generate different structs for different versions of this message (according to attributes over
/// its fields) and add it to all message Enums it should exist in (according to attribute
/// arguments).
///
/// E.g. for:
/// ```
/// use diachrony::{current_version, message, message_group};
///
/// current_version!(2);
///
/// #[message(group = IncomingMessage, from_version = 1)]
/// pub struct MyMessage {
///     field_a: u8,
///     #[field(from_version=2)]
///     field_b: u8
/// }
///
/// message_group!(IncomingMessage);
/// ```
///
/// Generate `MyMessage1` and `MyMessage2` and add a `MyMessage(MyMessage1)` variant to the
/// `IncomingMessageV1` enum and a `MyMessage(MyMessage2)` to the `IncomingMessageV2` Enum.
#[proc_macro_attribute]
pub fn message(args: TokenStream, item: TokenStream) -> TokenStream {
    versionization_macro(args, item)
}

#[proc_macro_attribute]
pub fn versionize(args: TokenStream, item: TokenStream) -> TokenStream {
    versionization_macro(args, item)
}

fn versionization_macro(args: TokenStream, item: TokenStream) -> TokenStream {
    let message_struct = parse_macro_input!(item as ItemStruct);

    let args = match parse_macro_args::<MessageMacroArgs>(args) {
        Ok(args) => args,
        Err(error_token_stream) => return error_token_stream,
    };

    let mut version_changes = BTreeMap::new();
    let mut message_fields = HashSet::new();
    let mut versioned_fields = HashSet::new();

    let fields = message_struct.fields.clone();
    let name = message_struct.ident.to_string();

    'fields: for field in fields {
        for (i, field_attr) in field.attrs.iter().enumerate() {
            // TODO: is_ident is not good, because we also want to match diachrony::field (and we
            //  don't want to match `field` if it's not imported form diachrony.
            if field_attr.path().is_ident("field") {
                let mut field = field.clone();
                field.attrs.remove(i);
                let field_args =
                    OptionalVersionRangeMacroArgs::from_meta(&field_attr.meta).unwrap();
                if field_args.versioned.unwrap_or_default() {
                    // This field is itself versioned, so it should have a different type in each
                    // version of this struct.
                    versioned_fields.insert(field.ident.clone().unwrap());
                }
                // TODO: validate that until_version is strictly greater than from_version, if
                //  they're both specified.
                if let Some(until_version) = field_args.until_version {
                    // TODO: verify that the until_version of this field is lower than the
                    //  until_version of the message (if there).

                    let version_change = version_changes.entry(until_version).or_default();
                    let VersionChange { removed_fields, .. } = version_change;
                    removed_fields.insert(field.clone());
                }
                if let Some(from_version) = field_args.from_version {
                    // TODO: verify that the from_version of this field is higher than the
                    //  from_version of the message (if there).
                    let version_change = version_changes.entry(from_version).or_default();
                    let VersionChange { new_fields, .. } = version_change;
                    new_fields.insert(field);
                } else {
                    message_fields.insert(field.clone());
                    version_changes
                        .entry(args.from_version)
                        .or_default()
                        .new_fields
                        .insert(field);
                }
                continue 'fields;
            }
        }
        // No `field` attribute.
        message_fields.insert(field.clone());
        version_changes
            .entry(args.from_version)
            .or_default()
            .new_fields
            .insert(field);
    }
    // TODO: calculate capacity (the code changed).
    let mut struct_versions = Vec::<TokenStream>::with_capacity(version_changes.len());

    let next_version = proc_read_state(VERSION_KEY).map(|v: String| {
        v.parse::<Version>()
            .expect("Couldn't parse current version to int")
            + 1
    });
    // the first version of the group that does not contain this message.
    let until_version = match (args.until_version, next_version) {
        (Some(message_deprecation_version), Ok(next_version)) => std::cmp::min(message_deprecation_version, next_version),
        (Some(message_deprecation_version), Err(_)) => message_deprecation_version,
        (None, Ok(next_version)) => next_version,
        (None, Err(_)) => panic!("Did not get either an until_version for the message or a current_version! for the crate."),
    };

    // Create a new struct type for each version of this message struct.
    for version in args.from_version..until_version {
        let mut changed = false;
        // If there are any fields added or removed in this version - do that.
        if let Some(version_change) = version_changes.get(&version) {
            changed = true;
            message_fields = &message_fields - &version_change.removed_fields;
            message_fields = message_fields
                .union(&version_change.new_fields)
                // TODO: can avoid cloning?
                .cloned()
                .collect();
        }
        let versionized = versionize_fields(&message_fields, &versioned_fields, version);
        changed |= versionized.is_some();
        let version_struct = if changed {
            let version_fields = versionized.unwrap_or(message_fields.iter().cloned().collect());
            make_struct_version(&message_struct, version, version_fields)
                .into_token_stream()
                .into()
        } else {
            generate_alias(&name, version)
        };
        struct_versions.push(version_struct);
    }

    // This codes saves macro state (sketchy) in order to tell the group macro about this member -
    // when it was added and when it was removed.
    // That way when we generate different enums for different versions of the group, we know in
    // which ones to include this message and in which ones not to.
    // If group is not specified the struct with this attribute
    if let Some(group) = args.group {
        let group_str = group.to_string();
        let removed_messages_state_key =
            format!("{REMOVED_MESSAGES_PREFIX}-{}-{until_version}", &group_str);
        proc_append_state(&removed_messages_state_key, &name).unwrap(); // unwrap?
        let added_messages_state_key = format!(
            "{ADDED_MESSAGES_PREFIX}-{}-{}",
            group_str, args.from_version
        );
        proc_append_state(&added_messages_state_key, &name).unwrap(); // unwrap?
    }

    TokenStream::from_iter(struct_versions)
}

fn generate_alias(message_name: &String, version: Version) -> TokenStream {
    let last_version = version - 1;
    let last_version_name = format_ident!("{message_name}V{last_version}");
    let alias_name = format_ident!("{message_name}V{version}");
    let type_alias = quote! {
        type #alias_name = #last_version_name;
    };
    // into: convert from proc_macro2's TokenStream to standard TokenStream.
    type_alias.into_token_stream().into()
}

fn generate_aliases(
    struct_versions: &mut Vec<TokenStream>,
    message_name: &String,
    last_version: Version,
    next_changed_version: Version,
) {
    let last_version_name = format_ident!("{message_name}V{last_version}");
    for alias_version in last_version + 1..next_changed_version {
        let alias_name = format_ident!("{message_name}V{alias_version}");
        let type_alias = quote! {
            type #alias_name = #last_version_name;
        };
        // convert from proc_macro2 TokenStream to standard TokenStream. Not sure whether this is my fault or not.
        let alias_token_stream = TokenStream::from(type_alias.into_token_stream());
        struct_versions.push(alias_token_stream)
    }
}

/// If any of the fields is versioned (is itself of a type that has versions) then return some
/// vector of the fields where the versioned fields are versionized (if `x: X` is versioned, then
/// change it to `x: XV0` or whatever version). Else `None`.
fn versionize_fields(
    fields: &HashSet<Field>,
    versioned_fields: &HashSet<Ident>,
    version: Version,
) -> Option<Vec<Field>> {
    let mut versionized = false;
    let fields: Vec<Field> = fields
        .iter()
        .cloned()
        .map(|mut field| {
            if let Some(ident) = field.ident.as_mut() {
                // possible optimization: we check if the field is versioned on each message version
                // we could refactor to only check once.
                if versioned_fields.contains(ident) {
                    versionized = true;
                    versionize_type(&mut field.ty, version);
                }
            }
            field
        })
        .collect();
    versionized.then_some(fields)
}

/// Create a TokenStream of a message struct of the given version with the given fields.
fn make_struct_version(
    message_struct: &ItemStruct,
    version: Version,
    fields: Vec<Field>,
) -> ItemStruct {
    let mut message_struct = message_struct.clone();
    message_struct.ident = format_ident!("{}V{version}", message_struct.ident);
    match &mut message_struct.fields {
        Fields::Named(named) => named.named = Punctuated::from_iter(fields),
        Fields::Unnamed(_) => {}
        Fields::Unit => {}
    }
    message_struct
}

#[proc_macro_attribute]
pub fn field(_args: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn group(_args: TokenStream, item: TokenStream) -> TokenStream {
    item
}

fn get_current_version() -> Version {
    proc_read_state(VERSION_KEY)
        .expect("current_version!() not set")
        .parse::<Version>()
        .expect("Couldn't parse current version to int")
}

fn parse_macro_args<A: FromMeta>(args: TokenStream) -> Result<A, TokenStream> {
    let attr_args = NestedMeta::parse_meta_list(args.into())
        .map_err(|e| TokenStream::from(Error::from(e).write_errors()))?;

    A::from_list(&attr_args).map_err(|e| TokenStream::from(e.write_errors()))
}

/// Parses arguments to an attribute, and also removes that attribute.
fn parse_attr_args<T>(attrs: &mut Vec<Attribute>, attr_name: &str) -> Option<T>
where
    T: FromMeta,
{
    let index = attrs
        .iter()
        .position(|attr| attr.path().is_ident(attr_name));
    index.map(|index| {
        let attr = attrs.remove(index);
        T::from_meta(&attr.meta).expect(&format!(
            "Parsing the argument to the #[{attr_name}] attribute failed."
        ))
    })
}

#[proc_macro_attribute]
pub fn super_group(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = match parse_macro_args::<SuperGroupMacroArgs>(args) {
        Ok(args) => args,
        Err(error_token_stream) => return error_token_stream,
    };
    let current_version = get_current_version();
    let super_group_version_range =
        get_version_range(args.from_version, args.until_version, current_version);

    let mut super_group_enum = parse_macro_input!(item as ItemEnum);

    let super_group_ident = &super_group_enum.ident;
    let trait_ident = super_group_ident.clone();
    let all_variants = super_group_enum.variants.clone();
    let types = all_variants.iter().map(|variant| &variant.ident);
    let handler_ident = args.handler.clone();

    let trait_associated_types = types.clone();
    let super_group_trait = quote! {
        pub trait #trait_ident: HandleWith {
            #(type #trait_associated_types: #trait_associated_types;)*
            type SuperHandler: #handler_ident<SuperGroup=Self>;
        }
    };

    let message_ident = super_group_ident.clone();
    let handler_ident = args.handler.clone();

    let mut present_variants = HashSet::with_capacity(super_group_enum.variants.len());
    let mut new_variants: HashMap<Version, HashSet<(Variant, Ident)>> =
        HashMap::with_capacity(super_group_version_range.len());
    let mut removed_variants: HashMap<Version, HashSet<(Variant, Ident)>> =
        HashMap::with_capacity(super_group_version_range.len());

    // TODO: recheck capacity
    let mut output_items =
        Vec::with_capacity(super_group_enum.variants.len() + super_group_version_range.len() + 3);

    output_items.push(super_group_trait.clone().into_token_stream().into());

    let mut all_handlers = Vec::with_capacity(super_group_enum.variants.len());

    for variant in super_group_enum.variants.iter_mut() {
        let args: SuperGroupMacroArgs = parse_attr_args(&mut variant.attrs, "group").unwrap();
        all_handlers.push(args.handler.clone());
        output_items.push(make_message_group(
            &variant.ident,
            args.from_version,
            args.until_version,
        ));
        if let Some(v) = args.from_version {
            new_variants
                .entry(v)
                .or_default()
                .insert((variant.clone(), args.handler.clone()));
        } else {
            // Variant that doesn't have `from_version` and is therefore present in first version.
            present_variants.insert((variant.to_owned(), args.handler.clone()));
        }
        if let Some(v) = args.until_version {
            removed_variants
                .entry(v)
                .or_default()
                .insert((variant.clone(), args.handler));
        }
    }

    let arg_types = types.clone();
    let func_arg_types = arg_types.clone();

    let arg_names = all_handlers
        .iter()
        .map(|ident| format_ident!("{}", ident.to_string().to_case(Case::Snake)));
    let func_arg_names = arg_names.clone();

    let from_all_handlers_sig = quote! {
        fn from_all_handlers(
                #(#func_arg_names: <<Self::SuperGroup as #message_ident>::#func_arg_types as #func_arg_types>::Handler,)*
            ) -> Self
    };

    let sig = from_all_handlers_sig.clone();

    let super_handler_trait = quote! {
        pub trait #handler_ident: HandleMessage<Message=Self::SuperGroup> {
            type SuperGroup: #message_ident<SuperHandler=Self>;
            #sig;
        }
    };
    output_items.push(super_handler_trait.clone().into_token_stream().into());

    let super_handler_ident = args.handler;

    for version in super_group_version_range {
        // Super-group enum of this version e.g. `enum ClientMessageV0 { ... }`
        let mut next_version = super_group_enum.clone();

        // Update which variants (message groups) are present in this version.
        if let Some(removed) = removed_variants.get(&version) {
            present_variants = &present_variants - removed;
        }
        if let Some(added) = new_variants.remove(&version) {
            present_variants.extend(added.into_iter());
        }

        // Split into separate iters (had to keep them together for same order, but in separate
        // iterators, for the quote!).
        let variants = present_variants.iter().map(|tup| &tup.0);
        let handlers = present_variants.iter().map(|tup| &tup.1);

        let present_variant_names: HashSet<Ident, RandomState> =
            HashSet::from_iter(variants.clone().map(|variant| variant.ident.clone()));

        // Field names of the super-handler, which are the handlers for the different variants
        // (message groups).
        let handler_fields = handlers
            .clone()
            .map(|handler_type| format_ident!("{}", handler_type.to_string().to_case(Case::Snake)));

        let versionized_variants = variants.cloned().map(|mut variant| {
            verionize_variant(&mut variant, version);
            variant
        });

        next_version.variants = Punctuated::from_iter(versionized_variants.clone()); // cloning iter, not all

        let super_handler_versioned_ident = format_ident!("{super_handler_ident}V{version}");
        // TODO: pub?
        let struct_handler_fields = handler_fields.clone();
        let struct_handler_field_types = handlers
            .clone()
            .map(|ident| get_versionized_ident(ident, version));
        let super_handler = quote! {
            pub struct #super_handler_versioned_ident {
                #(#struct_handler_fields: #struct_handler_field_types,)*
            }
        };
        output_items.push(super_handler.into_token_stream().into());

        versionize_ident(&mut next_version.ident, version);
        let variant_names = versionized_variants.clone().map(|variant| variant.ident);

        let versionized_enum_ident = &next_version.ident;

        let self_handler_fields = handler_fields.clone();
        let constructor_handler_fields = handler_fields.clone();
        let sig = from_all_handlers_sig.clone();
        let handler_impls = quote! {
            impl diachrony::HandleMessage for #super_handler_versioned_ident {
                type Message = #versionized_enum_ident;
                fn handle(&self, message: Self::Message) {
                    match message {
                        #(#versionized_enum_ident::#variant_names(message) => self.#self_handler_fields.handle(message),)*
                    }
                }
            }

            impl diachrony::HandleWith for #versionized_enum_ident {
                type Handler = #super_handler_versioned_ident;
            }

            impl #super_handler_ident for #super_handler_versioned_ident {
                type SuperGroup = #versionized_enum_ident;
                #sig {
                    Self {
                        #(#constructor_handler_fields,)*
                    }
                }
            }
        };

        // TODO: this is inefficient.
        let associated_types = all_variants.iter().map(|variant| {
            if present_variant_names.contains(&variant.ident) {
                let ty = get_first_unnamed_field_type(variant);
                Type::Path(TypePath {
                    qself: None,
                    path: get_versionized_path(&get_type_path(ty).path, version),
                })
            } else {
                Type::Tuple(TypeTuple {
                    paren_token: Default::default(),
                    elems: Default::default(),
                })
            }
        });
        let trait_associated_types = types.clone();
        let message_trait_impl = quote! {
            impl #super_group_ident for #versionized_enum_ident{
                #(type #trait_associated_types = #associated_types;)*
                type SuperHandler = #super_handler_versioned_ident;
            }
        };

        output_items.push(handler_impls.into_token_stream().into());
        output_items.push(next_version.into_token_stream().into());
        output_items.push(message_trait_impl.into_token_stream().into());
    }

    TokenStream::from_iter(output_items)
}

fn versionize_ident(ident: &mut Ident, version: Version) {
    *ident = format_ident!("{}V{version}", ident);
}

fn get_versionized_ident(ident: &Ident, version: Version) -> Ident {
    format_ident!("{}V{version}", ident)
}

fn get_first_unnamed_field_type(variant: &Variant) -> &Type {
    let Fields::Unnamed(ref unnamed_fields) = variant.fields else {
        panic!("Expected tuple variant for message group {}.", variant.ident.to_string());
    };
    &unnamed_fields
        .unnamed
        .first()
        .unwrap_or_else(|| {
            panic!(
                "Missing unnamed field for tuple variant {}.",
                variant.ident.to_string()
            )
        })
        .ty
}

fn get_first_unnamed_field_type_mut(variant: &mut Variant) -> &mut Type {
    let Fields::Unnamed(ref mut unnamed_fields) = variant.fields else {
        panic!("Expected tuple variant for message group {}.", variant.ident.to_string());
    };
    &mut unnamed_fields
        .unnamed
        .first_mut()
        .unwrap_or_else(|| {
            panic!(
                "Missing unnamed field for tuple variant {}.",
                variant.ident.to_string()
            )
        })
        .ty
}

fn verionize_variant(variant: &mut Variant, version: Version) {
    versionize_ident(&mut variant.ident, version);
    let variant_field_type = get_first_unnamed_field_type_mut(variant);
    versionize_type(variant_field_type, version);
}

fn get_version_range(
    from_version: Option<Version>,
    until_version: Option<Version>,
    current_version: Version,
) -> RangeInclusive<Version> {
    from_version.unwrap_or_default()
        ..=until_version
            .map(|v| std::cmp::min(v - 1, current_version))
            .unwrap_or(current_version)
}

fn make_message_group(
    group_name_ident: &Ident,
    from_version: Option<Version>,
    until_version: Option<Version>,
) -> TokenStream {
    let group_name = group_name_ident.to_string();

    let mut version_enums = Vec::new();
    let current_version = get_current_version();

    let mut message_types = BTreeSet::new();

    let version_range = get_version_range(from_version, until_version, current_version);

    for version in version_range {
        let added_messages_key = format!("{ADDED_MESSAGES_PREFIX}-{group_name}-{version}");
        let new_messages_in_this_version = proc_read_state_vec(&added_messages_key);
        let removed_messages_key = format!("{REMOVED_MESSAGES_PREFIX}-{group_name}-{version}");
        let removed_messages_in_this_version = proc_read_state_vec(&removed_messages_key);
        let removed_messages_in_this_version =
            BTreeSet::from_iter(removed_messages_in_this_version.into_iter());
        message_types = message_types
            .difference(&removed_messages_in_this_version)
            .cloned()
            .collect();
        message_types.extend(new_messages_in_this_version);
        let variants = message_types
            .iter()
            .map(|type_name| format_ident!("{type_name}"));
        let enum_name = format_ident!("{group_name}V{version}");
        let message_names = message_types
            .iter()
            .map(|message_name| format_ident!("{message_name}V{version}"));
        let message_group_enum = quote! {
            pub enum #enum_name { // set the struct to public
                #(#variants(#message_names)),*
            }
        };
        // convert from proc_macro2 TokenStream to standard TokenStream.
        let group_enum = TokenStream::from(message_group_enum.into_token_stream());
        version_enums.push(group_enum);
    }
    TokenStream::from_iter(version_enums)
}

#[proc_macro]
pub fn message_group(args: TokenStream) -> TokenStream {
    let items = parse_macro_input!(args with Punctuated<Expr, Token![,]>::parse_terminated);
    let mut exprs = items.iter();
    let group_name = exprs.next().unwrap(); // TODO: unwrap
    let Expr::Path(group_name) = group_name else {
        // TODO: panic?
        panic!("First argument of message_group! should be the group name (enum name).")
    };
    let group_name_ident = group_name.path.get_ident().unwrap(); // TODO: unwrap
    make_message_group(group_name_ident, None, None)
}

#[proc_macro_attribute]
pub fn handler_struct(args: TokenStream, struct_def: TokenStream) -> TokenStream {
    let mut struct_def = parse_macro_input!(struct_def as ItemStruct);
    let args = match parse_macro_args::<OptionalVersionRangeMacroArgs>(args) {
        Ok(args) => args,
        Err(error_token_stream) => return error_token_stream,
    };

    let Fields::Named(ref mut fields_named) = struct_def.fields else {
        panic!("Expected handler struct to be a struct with named fields")
    };

    let handler_ident = &struct_def.ident;

    let current_version = get_current_version();
    let version_range = get_version_range(args.from_version, args.until_version, current_version);
    // TODO: check capacity.
    let mut output_items = Vec::with_capacity(version_range.len() + 1);

    let all_fields = fields_named.clone();
    let all_field_names = all_fields.named.iter().map(|field| &field.ident);
    let all_field_types = all_fields.named.iter().map(|field| &field.ty);

    let params = all_field_names.clone();

    let trait_method_sig = quote!(
        fn from_all_state(#(#params: #all_field_types,)*) -> Self
    );

    let handler_trait: TokenStream = quote! {
        pub trait #handler_ident {
            #trait_method_sig;
        }

        impl #handler_ident for () {
            #trait_method_sig {
                ()
            }
        }
    }
    .into_token_stream()
    .into();

    output_items.push(handler_trait);

    // TODO: I repeated the whole present, added, removed collecting loop logic a lot. Could be
    //       Extracted to a (generic?) function.
    // Which fields are present in the currently processed version, initially first version.
    let mut present_fields = HashSet::with_capacity(fields_named.named.len());

    // for each version, which fields are new in that version.
    let mut added_fields = HashMap::<Version, HashSet<Field>>::new();

    // for each version, which fields are no longer present in that version.
    let mut removed_fields = HashMap::<Version, HashSet<Field>>::new();

    for field in fields_named.named.iter_mut() {
        let args: Option<OptionalVersionRangeMacroArgs> =
            parse_attr_args(&mut field.attrs, "handler_field");
        if let Some(args) = args {
            if let Some(v) = args.from_version {
                added_fields.entry(v).or_default().insert(field.clone());
            } else {
                // No from - means the field is there from the first version.
                present_fields.insert(field.clone());
            }
            if let Some(v) = args.until_version {
                removed_fields.entry(v).or_default().insert(field.clone());
            }
        } else {
            // No attr - so field is just always there.
            present_fields.insert(field.clone());
        }
    }

    for version in version_range {
        // TODO: also this loop code is repeated for many macros.
        // Super-group enum of this version e.g. `enum ClientMessageV0 { ... }`
        let next_version = struct_def.clone();

        // Update which variants (message groups) are present in this version.
        if let Some(removed) = removed_fields.get(&version) {
            present_fields = &present_fields - removed;
        }
        if let Some(added) = added_fields.remove(&version) {
            present_fields.extend(added.into_iter());
        }
        let next_struct = make_struct_version(
            &next_version,
            version,
            present_fields.iter().cloned().collect(),
        );
        let struct_ident = &next_struct.ident;
        let fields = present_fields.iter().map(|field| &field.ident);
        let trait_impl = quote! {
            impl #handler_ident for #struct_ident {
                #trait_method_sig {
                    Self {
                        #(#fields,)*
                    }
                }
            }
        }
        .into_token_stream()
        .into();
        output_items.push(next_struct.into_token_stream().into());
        output_items.push(trait_impl);
    }

    TokenStream::from_iter(output_items)
}

// Change MyHandler to MyHandlerV0 (, ...V1, ...).
fn versionize_path(path: &mut syn::Path, version: Version) {
    let last_segment = path.segments.last_mut().unwrap();
    let last_ident = &last_segment.ident;
    last_segment.ident = format_ident!("{last_ident}V{version}");
}

// Change MyHandler to MyHandlerV0 (, ...V1, ...).
fn get_versionized_path(path: &syn::Path, version: Version) -> syn::Path {
    let mut path = path.clone();
    versionize_path(&mut path, version);
    path
}

fn versionize_type(ty: &mut Type, version: Version) {
    versionize_path(&mut get_type_path_mut(ty).path, version)
}

fn get_type_path_mut(ty: &mut Type) -> &mut TypePath {
    let Type::Path(ref mut type_path) = ty else {
        panic!("Expected a type path, got {}.", ty.into_token_stream().to_string());
    };
    type_path
}

fn get_type_path(ty: &Type) -> &TypePath {
    let Type::Path(ref type_path) = ty else {
        panic!("Expected a type path, got {}.", ty.into_token_stream().to_string());
    };
    type_path
}

#[proc_macro_attribute]
pub fn handler(args: TokenStream, impl_block: TokenStream) -> TokenStream {
    let args = match parse_macro_args::<HandlerMacroArgs>(args) {
        Ok(args) => args,
        Err(error_token_stream) => return error_token_stream,
    };
    let mut impl_block = parse_macro_input!(impl_block as ItemImpl);
    let handler_type = (*impl_block.self_ty).clone();

    let current_version = get_current_version();
    let mut funcs: Vec<Vec<ImplItem>> = vec![Vec::new(); current_version as usize + 1];
    let mut func_names: Vec<Vec<Ident>> = vec![Vec::new(); current_version as usize + 1];
    let mut variants: Vec<Vec<syn::Path>> = vec![Vec::new(); current_version as usize + 1];

    impl_block.items = impl_block
        .items
        .into_iter()
        .filter(|item| {
            if let ImplItem::Fn(func) = item {
                if let Some(macro_args) = func.attrs.iter().find_map(|attr| {
                    attr.path()
                        .is_ident("handle") // TODO: deal a path like diachrony::handle?
                        .then(|| OptionalVersionRangeMacroArgs::from_meta(&attr.meta).unwrap())
                }) {
                    let from = macro_args.from_version.unwrap_or(0);
                    let until = macro_args
                        .until_version
                        .map(|v| std::cmp::min(v, current_version + 1))
                        .unwrap_or(current_version + 1);

                    for v in from..until {
                        let mut func_ver = item.clone();
                        let func_arg_type = get_func_arg_type_path(&mut func_ver);
                        variants[v as usize].push(func_arg_type.clone()); // E.g. MyMessage
                        versionize_path(func_arg_type, v);
                        funcs[v as usize].push(func_ver); // E.g. MyMessageV1
                        func_names[v as usize].push(func.sig.ident.clone());
                    }
                }
                false // remove all functions from impl_block;
            } else {
                true
            }
        })
        .collect();

    // TODO: code was changed, so recalculate capacity.
    let mut output_items: Vec<TokenStream> = Vec::with_capacity(current_version as usize);

    let message_group_path = args.message_group.clone();

    let group_trait = quote! {
        trait #message_group_path: HandleWith {
            type Handler: #handler_type;
        }

        impl #message_group_path for () {
            type Handler = ();
        }

    }
    .into_token_stream()
    .into();
    output_items.push(group_trait);

    let version_range = get_version_range(args.from_version, args.until_version, current_version);
    for version in version_range {
        let mut impl_block = impl_block.clone();
        versionize_path(
            &mut get_type_path_mut(impl_block.self_ty.as_mut()).path,
            version,
        );
        let mut message_handler_trait_impl = impl_block.clone();
        let type_path = get_type_path_mut(impl_block.self_ty.as_mut());
        // let type_path = get_gen_arg_type_path(&mut impl_block);
        // versionize_path(&mut type_path.path, version);
        // {
        //     let type_path = get_gen_arg_type_path(&mut message_handler_trait_impl);
        //     versionize_path(&mut type_path.path, version);
        // }
        let segments = Punctuated::from_iter(vec![
            PathSegment {
                ident: format_ident!("diachrony"),
                arguments: Default::default(),
            },
            PathSegment {
                ident: format_ident!("HandleMessage"),
                arguments: Default::default(),
            },
        ]);
        message_handler_trait_impl.trait_ = Some((
            None,
            syn::Path {
                leading_colon: None,
                segments,
            },
            Default::default(),
        ));
        let message_group_path = args.message_group.clone();
        let mut message_group_path_versionized = message_group_path.clone();
        versionize_path(&mut message_group_path_versionized, version);
        message_handler_trait_impl
            .items
            .push(ImplItem::Type(ImplItemType {
                attrs: vec![],
                vis: Visibility::Inherited,
                defaultness: None,
                type_token: Default::default(),
                ident: format_ident!("Message"),
                generics: Default::default(),
                eq_token: Default::default(),
                ty: Type::Path(TypePath {
                    qself: None,
                    path: message_group_path_versionized.clone(),
                }),
                semi_token: Default::default(),
            }));
        message_handler_trait_impl
            .items
            .push(make_general_handle_function(
                args.message_group.clone(),
                &func_names[version as usize],
                &variants[version as usize],
                version,
            ));
        let type_path = type_path.clone();

        // TODO: eliminate the cloning here, use a collection that allows moving out for `funcs`.
        impl_block.items.extend(funcs[version as usize].clone());
        output_items.push(impl_block.into_token_stream().into());
        output_items.push(message_handler_trait_impl.into_token_stream().into());

        let handle_with_impl_for_version = quote! {
            impl diachrony::HandleWith for #message_group_path_versionized {
                type Handler = #type_path;
            }
            impl #message_group_path for #message_group_path_versionized {
                type Handler = #type_path;
            }
        };
        output_items.push(handle_with_impl_for_version.into_token_stream().into());
    }
    TokenStream::from_iter(output_items)
}

/// Create the `handle` function that gets an enum object, matches it and calls the appropriate function.
fn make_general_handle_function(
    mut enum_path: syn::Path,
    func_names: &Vec<Ident>,
    variants: &Vec<syn::Path>,
    version: Version,
) -> ImplItem {
    versionize_path(&mut enum_path, version);
    let token_stream = quote!(
        fn handle(&self, message: Self::Message) {
            match message {
                #(#enum_path::#variants(exact_message) => self.#func_names(exact_message)),*
            }
        }
    )
    .into();
    syn::parse(token_stream).unwrap()
}

fn get_func_arg_type_path(func: &mut ImplItem) -> &mut syn::Path {
    let ImplItem::Fn(func) = func else {
        unreachable!()
    };
    for arg in func.sig.inputs.iter_mut() {
        if let FnArg::Typed(arg) = arg {
            let Type::Path(path) = arg.ty.as_mut() else {
                panic!("Expected simple path type for message argument for handler")
            };
            return &mut path.path;
        }
    }
    panic!("No message argument found for handler function.");
}

#[proc_macro_attribute]
pub fn handle(_args: TokenStream, func: TokenStream) -> TokenStream {
    func
}

/// Transforms a function that is generic over a message version type to function that takes a
/// version and calls the original function of that version of the message.
// TODO: Example
#[proc_macro_attribute]
pub fn version_dispatch(_args: TokenStream, func: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(func as ItemFn);
    let mut inner_func = func.clone();
    inner_func.vis = Visibility::Inherited;
    let last_gen_type = &func.sig.generics.params.iter_mut().filter_map(|gen_param| {
        if let GenericParam::Type(type_param) = gen_param {
            Some(type_param)
        } else {
            None
        }
    }).last().expect("version_dispatched func should have a message group name as a generic parameter. E.g. my_func<M: ClientMessage>().");
    let Some(TypeParamBound::Trait(bound )) = last_gen_type.bounds.first() else {
        panic!("`version_dispatch`ed function's generic argument should have a trait bound, E.g. my_func<M: ClientMessage>().");
    };
    let message_path = &bound.path;

    let name = &inner_func.sig.ident;
    let inner_name = format_ident!("versionized_{name}");
    inner_func.sig.ident = inner_name.clone();

    let call_args = func.sig.inputs.iter().filter_map(|fn_arg| {
        match fn_arg {
            FnArg::Receiver(_receiver) => None,
            FnArg::Typed(typed) => {
                let Pat::Ident(PatIdent{
                                   ident, ..
                               }) = typed.pat.as_ref() else {
                    panic!("unsupported function argument {}", typed.into_token_stream().to_string())
                };
                Some(ident)
            }
        }
    });

    let current_version = get_current_version();
    let versions = 0..=current_version;
    // FIXME: this does not preserve the other generic arguments.
    let types = versions
        .clone()
        .map(|v| get_versionized_path(message_path, v));
    // TODO: this does not use `Version` :(
    let versions = versions.map(|v| proc_macro2::Literal::u16_suffixed(v));

    let version_arg = format_ident!("{VERSION_DISPATCH_ARG_NAME}");

    let call_args = quote!(#(#call_args),*);

    let dispatcher_code = quote! {
        {
            match #version_arg {
                #(
                   #versions => #inner_name::<#types>(#call_args)
                ),*,
                _ => panic!("Unsupported version!") // TODO: ?
            }
        }
    }
    .into_token_stream()
    .into();

    *func.block = parse_macro_input!(dispatcher_code as Block);

    let segments = Punctuated::from_iter(vec![PathSegment {
        // TODO: this does not use `Version` :(
        ident: format_ident!("u16"),
        arguments: Default::default(),
    }]);
    func.sig.inputs.insert(
        0,
        FnArg::Typed(PatType {
            attrs: vec![],
            pat: Box::new(Pat::Ident(PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: None,
                ident: format_ident!("{VERSION_DISPATCH_ARG_NAME}"),
                subpat: None,
            })),
            colon_token: Default::default(),
            ty: Box::new(Type::Path(TypePath {
                qself: None,
                path: syn::Path {
                    leading_colon: None,
                    segments,
                },
            })),
        }),
    );
    func.sig.generics.params.pop();
    TokenStream::from_iter::<Vec<TokenStream>>(vec![
        inner_func.into_token_stream().into(),
        func.into_token_stream().into(),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(None, None, 5, 0..=5)] // no limits: all versions from 0 to current.
    #[case(Some(1), None, 5, 1..=5)] // Only `from` limit: all versions from `from` to current.
    #[case(None, Some(2), 5, 0..=1)] // Only `until` limit: all versions from 0 to until, excl.
    #[case(Some(1), Some(4), 5, 1..=3)] // Both `from` and `until`: versions between, excl.
    #[case(Some(1), Some(7), 5, 1..=5)] // `until` is higher than current: versions until current.
    #[case(Some(1), Some(6), 5, 1..=5)] // Here `until` and current both limit to 5.
    fn version_range(
        #[case] from_version: Option<Version>,
        #[case] until_version: Option<Version>,
        #[case] current_version: Version,
        #[case] expected_range: RangeInclusive<Version>,
    ) {
        assert_eq!(
            get_version_range(from_version, until_version, current_version),
            expected_range
        );
    }
}
