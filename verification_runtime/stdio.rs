use std::io::{Read, Write};

pub fn read<R: Read>(input: &mut R, bytes: &mut [u8]) -> std::io::Result<usize> {
    input.read(bytes)
}

pub fn write_all<W: Write>(output: &mut W, bytes: &[u8]) -> std::io::Result<()> {
    output.write_all(bytes)
}

pub fn strip_suffix<'a>(bytes: &'a [u8], suffix: &[u8]) -> Option<&'a [u8]> {
    bytes.strip_suffix(suffix)
}

pub fn next_line<I: Iterator<Item = std::io::Result<Vec<u8>>>>(lines: &mut I)
    -> Option<std::io::Result<Vec<u8>>>
{
    lines.next()
}
