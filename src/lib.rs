use darling::ast::NestedMeta;
use darling::{Error, FromAttributes, FromMeta};
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use std::collections::{BTreeMap, HashSet};
use syn;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, Attribute, Field, Fields, FieldsNamed, Ident, ItemStruct};

#[derive(Default, Debug)]
struct VersionChange {
    // TODO: for removed fields, we probably don't need the field object, just the name.
    pub removed_fields: HashSet<Field>,
    pub new_fields: HashSet<Field>,
}

#[derive(Debug, FromMeta)]
struct MessageMacroArgs {
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

/// Generate different structs for different versions of this message (according to attributes over
/// its fields) and add it to all message Enums it should exist in (according to attribute
/// arguments).
///
/// E.g. for:
/// ```
/// use diachrony::message;
///
/// #[message(version_from=1)]
/// struct MyMessage {
///     field_a: u8,
///     #[field(version_from=2)]
///     field_b: u8
/// }
/// ```
///
/// Generate `MyMessage1` and `MyMessage2` and add a `MyMessage(MyMessage1)` variant to the
/// `Message1` enum and a `MyMessage(MyMessage2)` to the `Message2` Enum.
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

    for (version, version_change) in version_changes {
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
    }

    TokenStream::from_iter(struct_versions)
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
