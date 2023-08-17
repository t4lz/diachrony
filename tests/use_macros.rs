use diachrony::{field, message};

#[message(from_version = 0)]
struct AddedField {
    field_a: u8,
    #[field(from_version = 1)]
    field_b: u8,
}

#[message(from_version = 1)]
struct AddedMessage {
    field_a: u8,
}

#[message(from_version = 0, until_version = 2)]
struct RemovedMessage {
    field_a: u8,
}

#[message(from_version = 1, until_version = 2)]
struct AddedAndRemovedMessage {
    field_a: u8,
}

#[test]
fn construct() {
    // TODO: AddedField should not exist, only versions.
    let af = AddedField {
        field_a: 0,
        field_b: 42,
    };
    let am = AddedMessage { field_a: 0 };
    let am = RemovedMessage { field_a: 0 };
}
