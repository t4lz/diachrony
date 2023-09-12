use diachrony::{
    current_version, handle, handler, handler_struct, message, message_group, version_dispatch,
};
use std::net::TcpStream;

current_version!(4);

#[message(group = ClientMessage, from_version = 0)]
#[derive(Debug)]
pub struct AddedField {
    pub field_a: u8,
    #[field(from_version = 1)]
    pub field_b: u8,
}

#[message(group = ClientMessage, from_version = 1)]
#[derive(Debug)]
pub struct AddedMessage {
    pub field_a: u8,
}

#[message(group = ClientMessage, from_version = 0, until_version = 2)]
#[derive(Debug)]
pub struct RemovedMessage {
    pub field_a: u8,
}

#[message(group = ClientMessage, from_version = 1, until_version = 2)]
#[derive(Debug)]
pub struct AddedAndRemovedMessage {
    pub field_a: u8,
}

message_group!(ClientMessage);

#[handler_struct]
pub struct MessageHandler {
    state1: u8,
    state2: bool,
}

#[handler(ClientMessage)]
impl MessageHandler {
    #[handle(from_version = 0, until_version = 1)]
    fn handle_added_field_v0(&self, message: AddedField) {
        println!("v0 handler");
        println!("message: {message:?}");
    }

    #[handle(from_version = 1)]
    fn handle_added_field_v1(&self, message: AddedField) {
        println!("v1 handler");
        println!("message: {message:?}");
    }

    #[handle(from_version = 1)]
    fn handle_added_added_message_v1(&self, message: AddedMessage) {
        println!("v1 handler");
        println!("message: {message:?}");
    }

    #[handle(from_version = 0, until_version = 2)]
    fn handle_removed_message(&self, message: RemovedMessage) {
        println!("v0 handler");
        println!("message: {message:?}");
    }

    #[handle(from_version = 1, until_version = 2)]
    fn handle_added_and_removed_message(&self, message: AddedAndRemovedMessage) {
        println!("v1 handler");
        println!("message: {message:?}");
    }
}

impl<T> Default for MessageHandler<T> {
    fn default() -> Self {
        Self {
            state1: Default::default(),
            state2: Default::default(),
            message_type: Default::default(),
        }
    }
}

#[version_dispatch]
pub fn wrap_raw_connection<ClientMessage: HandleWith>(stream: TcpStream) {
    let handler = <ClientMessage as HandleWith>::Handler::default();
    let client_message: ClientMessage = todo!();
    client_message.handle_with(handler);
}

#[test]
fn construct() {
    wrap_raw_connection(1, todo!());
}
