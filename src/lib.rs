use darling::ast::NestedMeta;
use darling::{Error, FromAttributes, FromMeta};
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use std::collections::{BTreeMap, HashSet};
use syn::punctuated::Punctuated;
use syn::Expr::{Lit, Path};
use syn::{parse_macro_input, Attribute, Expr, Field, Fields, Ident, ItemStruct, Token};

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

// TODO: doctests are failing.
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

    let last_version = args.from_version;

    for (version, version_change) in version_changes {
        let last_version_name = format!("{name}V{last_version}");
        for alias_version in last_version + 1..version {
            let alias_name = format!("{name}V{alias_version}");
            let type_alias = quote! {
                type #alias_name = #last_version_name;
            };
            // convert from proc_macro2 TokenStream to standard TokenStream. Not sure whether this is my fault or not.
            let alias_token_stream = TokenStream::from(type_alias.into_token_stream());
            struct_versions.push(alias_token_stream)
        }
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
        let last_version = version;
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

// struct MessageGroupMacroArgs {
//     group_name: String,
//     version_range: Range<u16>,
//     message_types: Vec<String>,
// }
//
// impl Parse for MessageGroupMacroArgs {
//     fn parse(input: ParseStream) -> Result<Self, syn::Error> {
//         let group_name: String = input.parse()?;
//         let _: _ = input.
//     }
// }

// TODO: should this be a declarative macro? Was too lazy to start a new crate.
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
    let from_version = exprs.next().unwrap(); // TODO: unwrap
    let Lit(from_version) = from_version else {
        panic!("Expected version literal at second argument for message_group {group_name}.") // TODO?
    };
    let syn::Lit::Int(ref lit_int) = from_version.lit else {
        panic!("Expected int literal (version) at second argument for message_group {group_name}.") // TODO?
    };
    let from_version = lit_int.base10_parse::<u16>().unwrap();
    let to_version = exprs.next().unwrap(); // TODO: unwrap
    let Lit(to_version) = to_version else {
        panic!("Expected version literal at second argument for message_group {group_name}.") // TODO?
    };
    let syn::Lit::Int(ref lit_int) = to_version.lit else {
        panic!("Expected int literal (version) at second argument for message_group {group_name}.") // TODO?
    };
    let to_version = lit_int.base10_parse::<u16>().unwrap();
    let message_types: Vec<String> = exprs
        .map(|expr| {
            let Path(expr_path) = expr else {
            panic!("Unexpected expression type in message_group {group_name} message types. Should be identifier (message name).") // TODO?
        };
            expr_path.path.get_ident().unwrap().to_string() // TODO: unwrap
        })
        .collect();

    let mut version_enums = Vec::with_capacity((to_version - from_version) as usize);

    for version in from_version..=to_version {
        let enum_name = format!("{group_name}V{version}");
        let message_names = message_types
            .iter()
            .cloned()
            .map(|message_name| format!("{message_name}V{version}"));
        let message_group_enum = quote! {
            enum #enum_name { // set the struct to public
                #(#message_types(#message_names),)*
            }
        };
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
