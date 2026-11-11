pub use super::trusted_common::chunks;
pub use crate::tr_trusted::make_keep_table;
pub fn count_kept(input: &[u8], keep: &[bool; 256]) -> usize {
    super::trusted_common::count_filtered(input, |byte: &u8| keep[*byte as usize])
}
pub fn search_new(byte: u8, input: &[u8]) -> memchr::Memchr<'_> {
    memchr::memchr_iter(byte, input)
}
pub fn search_next(it: &mut memchr::Memchr<'_>) -> Option<usize> {
    it.next()
}
pub fn single_delete(keep: &[bool; 256]) -> Option<u8> {
    let matches = crate::trusted_common::enumerated_filter_take(
        keep,
        |i: usize, value: &bool| -> bool { !*value },
        2,
    );
    if matches.len() == 1 {
        Some(matches[0].0 as u8)
    } else {
        None
    }
}
