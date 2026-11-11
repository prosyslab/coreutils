use std::iter::Cycle;
use std::slice::Iter;
pub mod library {
    use std::cell::{OnceCell, RefCell};
    use std::fs::File;
    use std::io::{BufRead, BufReader, Read, Stdin};
    use std::rc::Rc;
    pub fn new_cache<T>() -> OnceCell<T> {
        OnceCell::new()
    }
    pub fn cached<'a, T, F: FnOnce() -> T>(cell: &'a OnceCell<T>, init: F) -> &'a T {
        cell.get_or_init(init)
    }
    pub fn clone_rc<T>(value: &Rc<T>) -> Rc<T> {
        value.clone()
    }
    pub fn stdin_handle() -> Stdin {
        std::io::stdin()
    }
    pub fn open_file(name: &std::ffi::OsString) -> std::io::Result<File> {
        File::open(name)
    }
    pub fn buffered<R: Read>(reader: R) -> BufReader<R> {
        BufReader::new(reader)
    }
    pub fn lock_stdin(stdin: &Rc<RefCell<Stdin>>) -> std::io::StdinLock<'static> {
        stdin.try_borrow().unwrap().lock()
    }
    pub fn read<R: Read>(reader: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
        reader.read(buf)
    }
    pub fn read_until<R: BufRead>(
        reader: &mut R,
        byte: u8,
        buf: &mut Vec<u8>,
    ) -> std::io::Result<usize> {
        reader.read_until(byte, buf)
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
pub fn write_all<W: std::io::Write>(writer: &mut W, bytes: &[u8]) -> std::io::Result<()> {
    writer.write_all(bytes)
}
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
