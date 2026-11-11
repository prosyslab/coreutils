// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::proof;
use std::cmp::Ordering;
pub fn is_blank(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n')
}
fn filter_char(c: u8, ignore_non_printing: bool, ignore_non_dictionary: bool) -> bool {
    if ignore_non_dictionary && !(c.is_ascii_alphanumeric() || is_blank(c)) {
        return false;
    }
    !(ignore_non_printing && (c.is_ascii_control() || !c.is_ascii()))
}
fn cmp_chars(a: u8, b: u8, ignore_case: bool) -> Ordering {
    if ignore_case {
        { crate::trusted::comparisons::cmp_u8(a.to_ascii_uppercase(), b.to_ascii_uppercase()) }
    } else {
        { crate::trusted::comparisons::cmp_u8(a, b) }
    }
}
pub struct TextFilter {
    pub ignore_non_printing: bool,
    pub ignore_non_dictionary: bool,
}
impl crate::trusted::comparisons::BytePredicate for TextFilter {
    fn test(&self, byte: u8) -> bool {
        filter_char(byte, self.ignore_non_printing, self.ignore_non_dictionary)
    }
}
pub fn custom_str_cmp(
    a: &[u8],
    b: &[u8],
    ignore_non_printing: bool,
    ignore_non_dictionary: bool,
    ignore_case: bool,
) -> Ordering {
    if !(ignore_case || ignore_non_dictionary || ignore_non_printing) {
        {
            return crate::trusted::compare_byte_slices(a, b);
        }
    }
    let mut a_chars = crate::trusted::filter_bytes(
        a,
        TextFilter {
            ignore_non_printing,
            ignore_non_dictionary,
        },
    );
    let mut b_chars = crate::trusted::filter_bytes(
        b,
        TextFilter {
            ignore_non_printing,
            ignore_non_dictionary,
        },
    );
    loop {
        let a_char = a_chars.next();
        let b_char = b_chars.next();
        match (a_char, b_char) {
            (None, None) => return Ordering::Equal,
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (Some(a_char), Some(b_char)) => {
                let ordering = cmp_chars(*a_char, *b_char, ignore_case);
                if !matches!(ordering, Ordering::Equal) {
                    return ordering;
                }
            }
        }
    }
}
