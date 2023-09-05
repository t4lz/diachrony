use diachrony::{current_version, handle, handler, handler_struct, message, message_group};

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

#[handler_struct]
struct MessageHandler {
    state1: u8,
    state2: bool,
}

#[handler(ClientMessage)]
impl MessageHandler {
    #[handle(from_version = 0)]
    fn handle_added_field_v0(&self, message: AddedField) {}

    #[handle(from_version = 0)]
    fn handle_added_field_v1(&self, message: AddedField) {}
}

// let handler = MessageHandler<T>::default();
// let client_message: T = get_next_message<T>();
// handler.handle(client_message);

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
