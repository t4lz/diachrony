extern crate macro_state;

use proc_macro::TokenStream;
use std::collections::{BTreeMap, BTreeSet, HashSet};

use darling::ast::NestedMeta;
use darling::{Error, FromAttributes, FromMeta};
use macro_state::*;
use quote::{format_ident, quote, ToTokens};
use syn::punctuated::Punctuated;
use syn::token::{Gt, Lt};
use syn::{
    parse_macro_input, AngleBracketedGenericArguments, Attribute, Block, Expr, ExprLit, Field,
    FieldMutability, Fields, FnArg, GenericArgument, GenericParam, Generics, Ident, ImplItem,
    ImplItemType, ItemFn, ItemImpl, ItemStruct, Pat, PatIdent, PatType, PathArguments, PathSegment,
    Token, Type, TypeParam, TypePath, Visibility,
};

const VERSION_KEY: &str = "diachrony-protocol-version";
/// Prefix for the key of the state keeping all the messages removed in a version.
const REMOVED_MESSAGES_PREFIX: &str = "diachrony-message-removal";
/// Prefix for the key of the state keeping all the messages added in a version.
const ADDED_MESSAGES_PREFIX: &str = "diachrony-message-addition";
const VERSION_DISPATCH_ARG_NAME: &str = "diachrony_added_version_arg";

#[derive(Default, Debug)]
struct VersionChange {
    // TODO: for removed fields, we probably don't need the field object, just the name.
    pub removed_fields: HashSet<Field>,
    pub new_fields: HashSet<Field>,
}

#[derive(Debug, FromMeta)]
struct MessageMacroArgs {
    group: Ident,
    from_version: u16,
    until_version: Option<u16>,
}

#[derive(Debug, FromMeta, Default)]
struct FieldMacroArgs {
    from_version: Option<u16>,
    until_version: Option<u16>,
}

impl FromAttributes for FieldMacroArgs {
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
                FieldMacroArgs::from_meta(&attr.meta).unwrap()
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
    let mut message_struct = parse_macro_input!(item as ItemStruct);

    let attr_args = match NestedMeta::parse_meta_list(args.into()) {
        Ok(v) => v,
        Err(e) => {
            return TokenStream::from(Error::from(e).write_errors());
        }
    };

    let args = match MessageMacroArgs::from_list(&attr_args) {
        Ok(v) => v,
        Err(e) => {
            return TokenStream::from(e.write_errors());
        }
    };

    let mut version_changes = BTreeMap::new();
    let mut message_fields = HashSet::new();

    let fields = message_struct.fields.clone();
    let name = message_struct.ident.to_string();

    'fields: for field in fields {
        for (i, field_attr) in field.attrs.iter().enumerate() {
            // TODO: is_ident is not good, because we also want to match diachrony::field (and we
            //  don't want to match `field` if it's not imported form diachrony.
            if field_attr.path().is_ident("field") {
                // TODO: unwrap
                let mut field = field.clone();
                field.attrs.remove(i);
                let field_args = FieldMacroArgs::from_meta(&field_attr.meta).unwrap();
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
                }
                continue 'fields;
            }
        }
        // No `field` attribute.
        message_fields.insert(field.clone());
    }
    let mut struct_versions = Vec::with_capacity(version_changes.len());

    struct_versions.push(make_struct_version(
        &mut message_struct,
        &name,
        args.from_version,
        &message_fields,
    ));

    let mut last_version = args.from_version;

    for (version, version_change) in version_changes {
        generate_aliases(&mut struct_versions, &name, last_version, version);
        message_fields = &message_fields - &version_change.removed_fields;
        message_fields = message_fields
            .union(&version_change.new_fields)
            // TODO: can avoid cloning?
            .cloned()
            .collect();
        struct_versions.push(make_struct_version(
            &mut message_struct,
            &name,
            version,
            &message_fields,
        ));
        last_version = version;
    }

    let next_version = proc_read_state(VERSION_KEY).map(|v: String| {
        v.parse::<u16>()
            .expect("Couldn't parse current version to int")
            + 1
    });
    let until_version = match (args.until_version, next_version) {
        (Some(message_deprecation_version), Ok(next_version)) => std::cmp::min(message_deprecation_version, next_version),
        (Some(message_deprecation_version), Err(_)) => message_deprecation_version,
        (None, Ok(next_version)) => next_version,
        (None, Err(_)) => panic!("Did not get either an until_version for the message or a current_version! for the crate."),
    };
    let removed_messages_state_key = format!(
        "{REMOVED_MESSAGES_PREFIX}-{}-{until_version}",
        args.group.to_string()
    );
    proc_append_state(&removed_messages_state_key, &name).unwrap(); // unwrap?
    let added_messages_state_key = format!(
        "{ADDED_MESSAGES_PREFIX}-{}-{}",
        args.group.to_string(),
        args.from_version
    );
    proc_append_state(&added_messages_state_key, &name).unwrap(); // unwrap?

    generate_aliases(&mut struct_versions, &name, last_version, until_version);

    TokenStream::from_iter(struct_versions)
}

fn generate_aliases(
    struct_versions: &mut Vec<TokenStream>,
    message_name: &String,
    last_version: u16,
    next_changed_version: u16,
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

/// Create a TokenStream of a message struct of the given version with the given fields.
fn make_struct_version(
    message_struct: &mut ItemStruct,
    base_name: &str,
    version: u16,
    fields: &HashSet<Field>,
) -> TokenStream {
    let struct_name = format!("{base_name}V{}", version);
    message_struct.ident = Ident::new(&struct_name, message_struct.ident.span());
    match &mut message_struct.fields {
        Fields::Named(named) => named.named = Punctuated::from_iter(fields.clone()),
        Fields::Unnamed(_) => {}
        Fields::Unit => {}
    }
    TokenStream::from(message_struct.clone().into_token_stream())
}

#[proc_macro_attribute]
pub fn field(_args: TokenStream, item: TokenStream) -> TokenStream {
    item
}

fn get_current_version() -> u16 {
    proc_read_state(VERSION_KEY)
        .expect("current_version!() not set")
        .parse::<u16>()
        .expect("Couldn't parse current version to int")
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
    let group_name = group_name_ident.to_string();

    let mut version_enums = Vec::new();
    let current_version = get_current_version();

    let mut message_types = BTreeSet::new();

    let group_trait = quote! {
        trait #group_name_ident {}
    }
    .into_token_stream()
    .into();
    version_enums.push(group_trait);

    for version in 0..=current_version {
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

#[proc_macro_attribute]
pub fn handler_struct(_: TokenStream, struct_def: TokenStream) -> TokenStream {
    let mut struct_def = parse_macro_input!(struct_def as ItemStruct);
    if struct_def.generics.lt_token.is_none() {
        struct_def.generics = Generics {
            lt_token: Some(Lt::default()),
            params: Default::default(),
            gt_token: Some(Gt::default()),
            where_clause: None,
        }
    }
    let available_param_name =
        struct_def
            .generics
            .params
            .iter()
            .fold("T".to_string(), |acc, param| {
                if let GenericParam::Type(param) = param {
                    acc + param.ident.to_string().as_str()
                } else {
                    acc
                }
            });

    // Add new generic type parameter to struct.
    struct_def
        .generics
        .params
        .push(GenericParam::Type(TypeParam {
            attrs: vec![],
            ident: format_ident!("{available_param_name}"),
            colon_token: None,
            bounds: Default::default(),
            eq_token: None,
            default: None,
        }));

    let Fields::Named(ref mut fields_named) = struct_def.fields else {
        panic!("Expected handler struct to be a struct with named fields")
    };
    let phantom_type = format!("std::marker::PhantomData<{available_param_name}>");
    fields_named.named.push(Field {
        attrs: vec![],
        vis: Visibility::Inherited,
        mutability: FieldMutability::None,
        ident: Some(format_ident!("message_type")),
        colon_token: None,
        ty: Type::Path(TypePath::from_string(&phantom_type).unwrap()),
    });

    struct_def.into_token_stream().into()
}

// Change MyHandler to MyHandlerV0 (, ...V1, ...).
fn versionize_path(path: &mut syn::Path, version: u16) {
    let last_segment = path.segments.last_mut().unwrap();
    let last_ident = &last_segment.ident;
    last_segment.ident = format_ident!("{last_ident}V{version}");
}

fn get_type_path(impl_block: &mut ItemImpl) -> &mut TypePath {
    if let Type::Path(ref mut type_path) = *impl_block.self_ty {
        return type_path;
    };
    panic!("Unexpected handler type. Expected a type path.")
}

fn get_path_arguments(impl_block: &mut ItemImpl) -> &mut PathArguments {
    &mut get_type_path(impl_block)
        .path
        .segments
        .last_mut()
        .unwrap()
        .arguments
}

fn get_gen_arg_type_path(impl_block: &mut ItemImpl) -> &mut TypePath {
    let args = get_path_arguments(impl_block);
    let PathArguments::AngleBracketed(generic_args) = args else {
        unreachable!() // We set it before the loop.
    };
    let Some(GenericArgument::Type(Type::Path(type_path))) = generic_args.args.last_mut() else {
        unreachable!() // We push it before the loop.
    };
    type_path
}

fn make_generic_arg_from_path(path: syn::Path) -> GenericArgument {
    GenericArgument::Type(Type::Path(TypePath { qself: None, path }))
}

#[proc_macro_attribute]
pub fn handler(args: TokenStream, impl_block: TokenStream) -> TokenStream {
    let message_group_path = parse_macro_input!(args as syn::Path);
    let mut impl_block = parse_macro_input!(impl_block as ItemImpl);
    let message_group_generic_arg = make_generic_arg_from_path(message_group_path.clone());
    let handler_name = get_type_path(&mut impl_block).to_owned();

    let generic_arguments = get_path_arguments(&mut impl_block);
    match generic_arguments {
        PathArguments::None => {
            let mut args = Punctuated::new();
            args.push(message_group_generic_arg);
            *generic_arguments = PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                colon2_token: None,
                lt_token: Default::default(),
                args,
                gt_token: Default::default(),
            });
        }
        PathArguments::AngleBracketed(generic_args) => {
            generic_args.args.push(message_group_generic_arg)
        }
        PathArguments::Parenthesized(_) => {
            panic!("Unexpected")
        }
    }

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
                        .is_ident("handle") // TODO: deal a path like diachrony::handle
                        .then(|| FieldMacroArgs::from_meta(&attr.meta).unwrap())
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
    let mut handler_impls: Vec<TokenStream> = Vec::with_capacity(current_version as usize);

    // Trait that has to be implemented for all message group versions.
    // TODO: probably just export those 2 traits and not generate them in a macro.
    let handle_with_trait = quote! {
        trait HandleWith: Sized {
            type Handler: HandleMessage<Message=Self>;
            fn handle_with(self, handler: Self::Handler) {
                handler.handle(self)
            }
        }
    };
    let message_handler_trait = quote! {
        trait HandleMessage: Default {
            type Message;
            fn handle(&self, m: Self::Message);
        }
    };
    handler_impls.push(handle_with_trait.into_token_stream().into());
    handler_impls.push(message_handler_trait.into_token_stream().into());

    for version in 0..=current_version {
        let mut impl_block = impl_block.clone();
        let mut message_handler_trait_impl = impl_block.clone();
        let type_path = get_gen_arg_type_path(&mut impl_block);
        versionize_path(&mut type_path.path, version);
        {
            let type_path = get_gen_arg_type_path(&mut message_handler_trait_impl);
            versionize_path(&mut type_path.path, version);
        }
        let segments = Punctuated::from_iter(vec![PathSegment {
            ident: format_ident!("HandleMessage"),
            arguments: Default::default(),
        }]);
        message_handler_trait_impl.trait_ = Some((
            None,
            syn::Path {
                leading_colon: None,
                segments,
            },
            Default::default(),
        ));
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
                ty: Type::Path(type_path.clone()),
                semi_token: Default::default(),
            }));
        message_handler_trait_impl
            .items
            .push(make_general_handle_function(
                message_group_path.clone(),
                &func_names[version as usize],
                &variants[version as usize],
                version,
            ));
        let type_path = type_path.clone();

        // TODO: eliminate the cloning here, use a collection that allows moving out for `funcs`.
        impl_block.items.extend(funcs[version as usize].clone());
        handler_impls.push(impl_block.into_token_stream().into());
        handler_impls.push(message_handler_trait_impl.into_token_stream().into());

        let handle_with_impl_for_version = quote! {
            impl HandleWith for #type_path {
                type Handler = #handler_name<#type_path>;
            }
        };
        handler_impls.push(handle_with_impl_for_version.into_token_stream().into());
    }
    TokenStream::from_iter(handler_impls)
}

/// Create the `handle` function that gets an enum object, matches it and calls the appropriate function.
fn make_general_handle_function(
    mut enum_path: syn::Path,
    func_names: &Vec<Ident>,
    variants: &Vec<syn::Path>,
    version: u16,
) -> ImplItem {
    versionize_path(&mut enum_path, version);
    let token_stream = quote!(
        fn handle(&self, message: #enum_path) {
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
    }).last().expect("version_dispatched func should have a message group name as a generic parameter. E.g. my_func<ClientMessage>().");
    let generic_ident = &last_gen_type.ident;

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
    let types = versions
        .clone()
        .map(|v| format_ident!("{generic_ident}V{v}"));
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
