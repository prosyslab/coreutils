pub fn set_to_bitmap(set: &[u8]) -> [bool; 256] {
    let mut bitmap = [false; 256];
    for byte in set {
        let byte = *byte;
        bitmap[byte as usize] = true;
    }
    bitmap
}
pub fn make_keep_table(delete_set: &[u8]) -> [bool; 256] {
    crate::trusted_common::array_map(set_to_bitmap(delete_set), |delete: bool| -> bool {
        !delete
    })
}
pub fn make_translation_table(set1: &[u8], set2: &[u8]) -> [u8; 256] {
    let mut translation_table = crate::trusted_common::array_from_fn(|i: usize| -> u8 { i as u8 });
    if let Some(fallback) = set2.last().copied() {
        let pairs = crate::trusted_common::zip_with_repeat(set1, set2, fallback);
        for i in 0..pairs.len() {
            let (from, to) = pairs[i];
            translation_table[from as usize] = to;
        }
    }
    translation_table
}
