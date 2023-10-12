pub use diachrony_macros::*;

/// A trait message handlers need to implement.
pub trait HandleMessage {
    type Message: HandleWith<Handler = Self>;
    fn handle(&self, m: Self::Message);
}

/// The macros generate an empty implementation of this trait for each message group type.
/// TODO: explain why.
pub trait HandleWith: Sized {
    type Handler: HandleMessage<Message = Self>;
    fn handle_with(self, handler: Self::Handler) {
        handler.handle(self)
    }
}

impl HandleMessage for () {
    type Message = ();

    fn handle(&self, _m: Self::Message) {}
}

impl HandleWith for () {
    type Handler = ();

    fn handle_with(self, _handler: Self::Handler) {}
}
