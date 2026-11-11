pub use crate::tr_trusted::make_translation_table;
pub fn count(input: &[u8], byte: u8) -> usize {
    bytecount::count(input, byte)
}
pub fn single_change(table: &[u8; 256]) -> Option<(u8, u8)> {
    crate::simd::find_single_change(table, |i: usize, value: &u8| *value != i as u8)
}
