use diachrony::*;
use std::net::TcpStream;

current_version!(4);

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
enum ClientMessage {
    #[group(handler = ExampleMessageHandler, from_version = 0)]
    ExampleMessageGroup(ExampleMessageGroup),
    #[group(handler = SecondHandler, from_version = 2)]
    SecondMessageGroup(SecondMessageGroup),
}

#[handler_struct]
pub struct ExampleMessageHandler {
    state1: u8,
    state2: bool,
}

#[handler(ExampleMessageGroup)]
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

// TODO: generate this
impl<T> Default for ExampleMessageHandler<T> {
    fn default() -> Self {
        Self {
            state1: Default::default(),
            state2: Default::default(),
            message_type: Default::default(),
        }
    }
}

#[handler_struct]
pub struct SecondHandler {
    state_bool: bool,
}

#[handler(SecondMessageGroup)]
impl SecondHandler {
    #[handle(from_version = 2)]
    fn handle_whatever(&self, message: WhateverMessage) {
        println!("v2 handler");
        println!("message: {message:?}");
    }
}

// TODO: generate this
impl<T> Default for SecondHandler<T> {
    fn default() -> Self {
        Self {
            state_bool: Default::default(),
            message_type: Default::default(),
        }
    }
}

#[version_dispatch]
pub fn wrap_raw_connection<ExampleMessageGroup: diachrony::HandleWith>(stream: TcpStream) {
    let handler = <ExampleMessageGroup as diachrony::HandleWith>::Handler::default();
    let client_message: ExampleMessageGroup = todo!();
    client_message.handle_with(handler);
}

#[test]
fn construct() {
    wrap_raw_connection(1, todo!());
}
