use std::io::{BufRead, BufReader, Read};

pub fn fill_buf<R: Read>(reader: &mut BufReader<R>) -> std::io::Result<&[u8]> {
    reader.fill_buf()
}

pub fn consume<R: Read>(reader: &mut BufReader<R>, count: usize) {
    reader.consume(count);
}

pub fn position_eq(bytes: &[u8], byte: u8) -> Option<usize> {
    bytes.iter().position(|b| *b == byte)
}

pub fn last_whitespace(bytes: &[u8]) -> Option<usize> {
    bytes.iter().rposition(|b| b.is_ascii_whitespace() && *b != b'\r')
}

pub fn drain_prefix(bytes: &mut Vec<u8>, count: usize) {
    bytes.drain(..count);
}
