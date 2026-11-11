impl InputSource {
    fn close(self) {
        match self {
            Self::File(reader) => paste_trusted::close_input(reader),
            Self::StandardInput(reader) => ::std::mem::drop(reader),
        }
    }
}
