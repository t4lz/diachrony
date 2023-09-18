pub use diachrony_macros::*;

/// A trait message handlers need to implement.
pub trait HandleMessage: Default {
    type Message;
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
