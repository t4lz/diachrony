extern crate macro_state;

use proc_macro::TokenStream;
use std::collections::{BTreeMap, BTreeSet, HashSet};

use darling::ast::NestedMeta;
use darling::{Error, FromAttributes, FromMeta};
use macro_state::*;
use quote::{format_ident, quote, ToTokens};
use syn::punctuated::Punctuated;
use syn::Expr::Path;
use syn::{parse_macro_input, Attribute, Expr, ExprLit, Field, Fields, Ident, ItemStruct, Token};

const VERSION_KEY: &str = "diachrony-protocol-version";
/// Prefix for the key of the state keeping all the messages removed in a version.
const REMOVED_MESSAGES_PREFIX: &str = "diachrony-message-removal";
/// Prefix for the key of the state keeping all the messages added in a version.
const ADDED_MESSAGES_PREFIX: &str = "diachrony-message-addition";

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
/// struct MyMessage {
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
    println!("attr: \"{}\"", args.to_string());
    println!("item: \"{}\"", item.to_string());
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
        println!("processing field {:?}", field.clone().ident.unwrap()); // TODO: remove
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
                    println!("from_version: {from_version}");
                    // TODO: verify that the from_version of this field is higher than the
                    //  from_version of the message (if there).
                    let version_change = version_changes.entry(from_version).or_default();
                    let VersionChange { new_fields, .. } = version_change;
                    new_fields.insert(field);
                    println!(
                        "inserted field into version change. Version change: {:?}",
                        version_changes.get(&from_version).unwrap()
                    );
                } else {
                    message_fields.insert(field.clone());
                }
                println!("field_args: {field_args:#?}");
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
        println!("generating version {version}"); // TODO: delete.
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
pub fn field(args: TokenStream, item: TokenStream) -> TokenStream {
    println!("attr: \"{}\"", args.to_string());
    println!("item: \"{}\"", item.to_string());
    item
}

#[proc_macro]
pub fn message_group(args: TokenStream) -> TokenStream {
    let items = parse_macro_input!(args with Punctuated<Expr, Token![,]>::parse_terminated);
    let mut exprs = items.iter();
    let group_name = exprs.next().unwrap(); // TODO: unwrap
    let Path(group_name) = group_name else {
        // TODO: panic?
        panic!("First argument of message_group! should be the group name (enum name).")
    };
    let group_name = group_name.path.get_ident().unwrap().to_string(); // TODO: unwrap

    // let mut version_enums = Vec::with_capacity((to_version - from_version) as usize);
    let mut version_enums = Vec::new();
    let current_version = proc_read_state(VERSION_KEY)
        .expect("current_version!() not set")
        .parse::<u16>()
        .expect("Couldn't parse current version to int");

    let mut message_types = BTreeSet::new();

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
            enum #enum_name { // set the struct to public
                #(#variants(#message_names)

                ),*
            }
        };
        println!("generated enum: {}", message_group_enum.to_string());
        // convert from proc_macro2 TokenStream to standard TokenStream.
        let group_enum = TokenStream::from(message_group_enum.into_token_stream());
        version_enums.push(group_enum);
    }
    TokenStream::from_iter(version_enums)
}

fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
