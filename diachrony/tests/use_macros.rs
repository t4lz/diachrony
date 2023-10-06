use diachrony::*;
use std::net::TcpStream;

current_version!(3);

#[message(group = ExampleMessageGroup, from_version = 0)]
#[derive(Debug)]
pub struct AddedField {
    pub field_a: u8,
    #[field(from_version = 1)]
    pub field_b: u8,
}

#[message(group = ExampleMessageGroup, from_version = 1)]
#[derive(Debug)]
pub struct AddedMessage {
    pub field_a: u8,
}

#[message(group = ExampleMessageGroup, from_version = 0, until_version = 2)]
#[derive(Debug)]
pub struct RemovedMessage {
    pub field_a: u8,
}

#[message(group = ExampleMessageGroup, from_version = 1, until_version = 2)]
#[derive(Debug)]
pub struct AddedAndRemovedMessage {
    pub field_a: u8,
}

// message_group!(ExampleMessageGroup);

#[message(group = SecondMessageGroup, from_version = 2)]
#[derive(Debug)]
pub struct WhateverMessage {
    pub field_a: u8,
    pub field_b: u8,
}

// Generates a super-handler that has all the handlers and calls the appropriate handler.
#[super_group(handler = ClientMessageSuperHandler)]
pub enum ClientMessage {
    #[group(handler = ExampleMessageHandler, from_version = 0)]
    ExampleMessageGroup(ExampleMessageGroup),
    #[group(handler = SecondHandler, from_version = 2)]
    SecondMessageGroup(SecondMessageGroup),
}

#[handler_struct]
#[derive(Default)]
pub struct ExampleMessageHandler {
    state1: u8,
    state2: bool,
}

#[handler(message_group=ExampleMessageGroup)]
impl ExampleMessageHandler {
    #[handle(from_version = 0, until_version = 1)]
    fn handle_added_field_v0(&self, message: AddedField) {
        println!("v0 handler");
        println!("message: {message:?}");
        // let x = message.field_a(); // TODO
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

#[handler_struct(from_version = 2)]
#[derive(Default)]
pub struct SecondHandler {
    state_bool: bool,
}

#[handler(message_group = SecondMessageGroup, from_version = 2)]
impl SecondHandler {
    #[handle(from_version = 2)]
    fn handle_whatever(&self, message: WhateverMessage) {
        println!("v2 handler");
        println!("message: {message:?}");
    }
}

#[version_dispatch]
pub fn wrap_raw_connection<M: ClientMessage>(stream: TcpStream) {
    let example_handler = M::ExampleHandler::from_all_state(42, false);
    let second_handler = M::SecondHandler::from_all_state(true);
    let super_handler = M::Handler::from_all_handlers(example_handler, second_handler);
    let client_message: ClientMessage = todo!();
    super_handler.handle(client_message);
}

// #[version_dispatch]
// pub fn wrap_raw_connection1<T: ClientMessageSuperHandler>(stream: TcpStream) {
//     // let handler = <ClientMessage as diachrony::HandleWith>::Handler::default();
//     // let client_message: ExampleMessageGroup = todo!();
//     // client_message.handle_with(handler);
// }

#[test]
fn construct() {
    let version = 1; // Some number that is only determined in runtime.
    wrap_raw_connection(version, todo!());
}
