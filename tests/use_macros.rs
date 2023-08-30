use diachrony::{current_version, message, message_group};

current_version!(4);

#[message(group = ClientMessage, from_version = 0)]
pub struct AddedField {
    field_a: u8,
    #[field(from_version = 1)]
    field_b: u8,
}

#[message(group = ClientMessage, from_version = 1)]
pub struct AddedMessage {
    field_a: u8,
}

#[message(group = ClientMessage, from_version = 0, until_version = 2)]
pub struct RemovedMessage {
    field_a: u8,
}

#[message(group = ClientMessage, from_version = 1, until_version = 2)]
pub struct AddedAndRemovedMessage {
    field_a: u8,
}

message_group!(ClientMessage);

#[test]
fn construct() {
    // TODO: don't use generated version structs.
    let af = AddedFieldV0 { field_a: 0 };
    let af = AddedFieldV1 {
        field_a: 0,
        field_b: 42,
    };
    let am = AddedMessageV1 { field_a: 0 };
    let am = RemovedMessageV0 { field_a: 0 };
}
