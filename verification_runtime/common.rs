pub mod filesystem {}
#[allow(unused_macros)]
macro_rules! closure_with_spec {
    (($ ($ spec : tt) *) , $ closure : expr) => {
        $closure
    };
}
pub(crate) use closure_with_spec;
pub fn array_from_fn<T, F: Fn(usize) -> T>(f: F) -> [T; 256] {
    std::array::from_fn(f)
}
pub fn array_map<T, U, F: Fn(T) -> U>(input: [T; 256], f: F) -> [U; 256] {
    input.map(f)
}
pub fn zip_with_repeat<T: Copy, U: Copy>(left: &[T], right: &[U], fallback: U) -> Vec<(T, U)> {
    left.iter()
        .copied()
        .zip(right.iter().copied().chain(std::iter::repeat(fallback)))
        .collect()
}
pub fn enumerated_filter_take<T: Copy, F: Fn(usize, &T) -> bool>(
    input: &[T],
    check: F,
    limit: usize,
) -> Vec<(usize, T)> {
    input
        .iter()
        .enumerate()
        .filter_map(|(i, value)| check(i, value).then_some((i, *value)))
        .take(limit)
        .collect()
}
pub fn count_filtered<T, F: Fn(&T) -> bool>(input: &[T], f: F) -> usize {
    input.iter().filter(|item| f(*item)).count()
}
pub fn split_inclusive(input: &[u8], delimiter: u8) -> Vec<&[u8]> {
    input.split_inclusive(|&byte| byte == delimiter).collect()
}
pub fn strip_suffix<'a>(input: &'a [u8], suffix: &[u8]) -> Option<&'a [u8]> {
    input.strip_suffix(suffix)
}
pub fn extend_mapped<F: Fn(u8) -> u8>(output: &mut Vec<u8>, input: &[u8], f: F) {
    output.extend(input.iter().copied().map(f));
}
pub struct Chunks<'a> {
    inner: std::slice::Chunks<'a, u8>,
}
impl<'a> Iterator for Chunks<'a> {
    type Item = &'a [u8];
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}
pub fn chunks<'a>(input: &'a [u8], size: usize) -> Chunks<'a> {
    Chunks {
        inner: input.chunks(size),
    }
}
pub mod io {
    use std::io::BufRead;
    use std::io::{Read, Write};
    pub fn read<R: Read>(input: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
        input.read(buf)
    }
    pub fn write_all<W: Write>(output: &mut W, bytes: &[u8]) -> std::io::Result<()> {
        output.write_all(bytes)
    }
    pub fn read_all<R: Read>(input: &mut R) -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        input.read_to_end(&mut bytes)?;
        Ok(bytes)
    }
    pub fn reader(input: &[u8]) -> &[u8] {
        input
    }
    pub fn writer(initial: &Vec<u8>) -> Vec<u8> {
        initial.clone()
    }
    pub fn finish(output: Vec<u8>) -> Vec<u8> {
        output
    }
}
