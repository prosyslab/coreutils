use std::iter::Cycle;
use std::slice::Iter;
use vstd::prelude::*;
pub mod library {
    use std::cell::{OnceCell, RefCell};
    use std::fs::File;
    use std::io::{BufRead, BufReader, Read, Stdin};
    use std::rc::Rc;
    use vstd::prelude::*;
    pub fn new_cache<T>() -> OnceCell<T> {
        OnceCell::new()
    }
    pub fn cached<'a, T, F: FnOnce() -> T>(cell: &'a OnceCell<T>, init: F) -> &'a T {
        cell.get_or_init(init)
    }
    pub fn clone_rc<T>(value: &Rc<T>) -> Rc<T> {
        value.clone()
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn stdin_handle() -> Stdin {
        std::io::stdin()
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn open_file(name: &std::ffi::OsString) -> std::io::Result<File> {
        let io_result = { File::open(name) };
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof! { if io_result is Ok { let ghost before = state @ ; let ghost path = crate :: filesystem :: os_bytes (name) ; let ghost fd = crate :: filesystem :: descriptor (& io_result -> Ok_0) ; before . open_valid (path , fd) ; * state = Ghost (before . open_file (path , fd)) ; } }
        io_result
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn buffered<R: Read>(reader: R) -> BufReader<R> {
        BufReader::new(reader)
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn lock_stdin(stdin: &Rc<RefCell<Stdin>>) -> std::io::StdinLock<'static> {
        stdin.try_borrow().unwrap().lock()
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn read<R: Read>(reader: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof_decl! { let ghost io_fd = crate :: filesystem :: descriptor (& * reader) ; }
        let io_result = { reader.read(buf) };
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof! { if io_result is Ok { let ghost before = state @ ; before . advance_valid (io_fd , io_result -> Ok_0 as nat) ; * state = Ghost (before . advance (io_fd , io_result -> Ok_0 as nat)) ; assert (crate :: trusted_common :: fd :: read (before , state @ , io_fd , buf @ . len () , buf @ . take (io_result -> Ok_0 as int))) ; } }
        io_result
    }
    # [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
    pub fn read_until<R: BufRead>(
        reader: &mut R,
        byte: u8,
        buf: &mut Vec<u8>,
    ) -> std::io::Result<usize> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof_decl! { let ghost io_fd = crate :: filesystem :: descriptor (& * reader) ; }
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof_decl! { let ghost io_buffer_len = buf @ . len () ; }
        let io_result = { reader.read_until(byte, buf) };
        #[cfg(verus_keep_ghost)]
        vstd::prelude::proof! { if io_result is Ok { let ghost before = state @ ; before . advance_valid (io_fd , io_result -> Ok_0 as nat) ; * state = Ghost (before . advance (io_fd , io_result -> Ok_0 as nat)) ; assert (crate :: trusted_common :: fd :: read (before , state @ , io_fd , before . remaining (io_fd) . len () , buf @ . skip (io_buffer_len as int))) ; } }
        io_result
    }
    pub fn read_stdin() -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        std::io::stdin().read_to_end(&mut bytes)?;
        Ok(bytes)
    }
    pub fn read_file(name: &std::ffi::OsString) -> std::io::Result<Vec<u8>> {
        std::fs::read(name)
    }
}
pub fn filename_is_stdin(filename: &std::ffi::OsString) -> bool {
    filename == "-"
}
pub fn encoded_bytes(name: &std::ffi::OsString) -> &[u8] {
    name.as_encoded_bytes()
}
pub fn character_length(bytes: &[u8]) -> usize {
    uucore::i18n::charmap::mb_char_len(bytes)
}
pub fn delimiter_error() -> std::io::Error {
    std::io::Error::other("delimiter list ends with an unescaped backslash")
}
pub fn boxed_slice<T>(value: Vec<T>) -> Box<[T]> {
    value.into_boxed_slice()
}
pub fn box_bytes(value: &[u8]) -> Box<[u8]> {
    Box::from(value)
}
pub fn box_byte(value: u8) -> Box<[u8]> {
    box_bytes(&[value])
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub fn write_all<W: std::io::Write>(writer: &mut W, bytes: &[u8]) -> std::io::Result<()> {
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result = crate::trusted_common::io::write_state(writer, bytes);
        io_result
    }
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub fn lock_stdout(output: &std::io::Stdout) -> std::io::StdoutLock<'static> {
    output.lock()
}
pub fn open_file(filename: &std::ffi::OsString) -> std::io::Result<std::fs::File> {
    let path = std::path::Path::new(filename);
    std::fs::File::open(path)
}
pub fn delimiter_cycle(delimiters: &[Box<[u8]>]) -> Cycle<Iter<'_, Box<[u8]>>> {
    delimiters.iter().cycle()
}
pub fn delimiter_next<'a>(iter: &mut Cycle<Iter<'a, Box<[u8]>>>) -> Option<&'a Box<[u8]>> {
    iter.next()
}
pub fn pop_if_eq(output: &mut Vec<u8>, byte: u8) -> Option<u8> {
    output.pop_if(|last| *last == byte)
}
#[allow(dead_code)]
pub fn strip_last(bytes: &[u8], byte: u8) -> &[u8] {
    bytes.strip_suffix(&[byte]).unwrap_or(bytes)
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub fn close_input<R>(reader: R) {
    #[cfg(verus_keep_ghost)]
    vstd::prelude::proof_decl! { let ghost io_fd = crate :: filesystem :: descriptor (& reader) ; }
    let io_result = {
        ::std::mem::drop(reader);
    };
    #[cfg(verus_keep_ghost)]
    vstd::prelude::proof! { let ghost before = state @ ; before . close_valid (io_fd) ; * state = Ghost (before . close_file (io_fd)) ; }
    io_result
}
