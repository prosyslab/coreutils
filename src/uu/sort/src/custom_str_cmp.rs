// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

//! Custom string comparisons.
//!
//! The goal is to compare strings without transforming them first (i.e. not allocating new strings)

use std::cmp::Ordering;
#[cfg(verus_keep_ghost)]
use crate::proof;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Newlines also act as blanks inside NUL-terminated records.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == proof::ascii_blank(c), no_unwind))]
pub fn is_blank(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n')
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == proof::keep_text(c, ignore_non_dictionary, ignore_non_printing),
    no_unwind
))]
fn filter_char(c: u8, ignore_non_printing: bool, ignore_non_dictionary: bool) -> bool {
    if ignore_non_dictionary && !(c.is_ascii_alphanumeric() || is_blank(c)) {
        return false;
    }
    !(ignore_non_printing && (c.is_ascii_control() || !c.is_ascii()))
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == proof::byte_order(
        seq![if ignore_case { proof::ascii_upper(a) } else { a }],
        seq![if ignore_case { proof::ascii_upper(b) } else { b }]),
    no_unwind
))]
fn cmp_chars(a: u8, b: u8, ignore_case: bool) -> Ordering {
    #[cfg(verus_keep_ghost)]
    proof! {
        proof::byte_order_singleton(if ignore_case { proof::ascii_upper(a) } else { a },
            if ignore_case { proof::ascii_upper(b) } else { b });
    }
    if ignore_case {
        #[cfg(not(verus_keep_ghost))]
        { a.to_ascii_uppercase().cmp(&b.to_ascii_uppercase()) }
        #[cfg(verus_keep_ghost)]
        { crate::trusted::comparisons::cmp_u8(a.to_ascii_uppercase(), b.to_ascii_uppercase()) }
    } else {
        #[cfg(not(verus_keep_ghost))]
        { a.cmp(&b) }
        #[cfg(verus_keep_ghost)]
        { crate::trusted::comparisons::cmp_u8(a, b) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub struct TextFilter { pub ignore_non_printing: bool, pub ignore_non_dictionary: bool }

impl crate::trusted::comparisons::BytePredicate for TextFilter {
    open spec fn model(&self) -> spec_fn(u8) -> bool {
        |byte: u8| proof::keep_text(byte, self.ignore_non_dictionary, self.ignore_non_printing)
    }
    fn test(&self, byte: u8) -> (result: bool)
        ensures result == self.model()(byte),
    { filter_char(byte, self.ignore_non_printing, self.ignore_non_dictionary) }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == proof::byte_order(
        proof::text_bytes(a@, ignore_case, ignore_non_dictionary, ignore_non_printing),
        proof::text_bytes(b@, ignore_case, ignore_non_dictionary, ignore_non_printing)),
    no_unwind
))]
pub fn custom_str_cmp(
    a: &[u8],
    b: &[u8],
    ignore_non_printing: bool,
    ignore_non_dictionary: bool,
    ignore_case: bool,
) -> Ordering {
    if !(ignore_case || ignore_non_dictionary || ignore_non_printing) {
        // There are no custom settings. Fall back to the default strcmp, which is faster.
        #[cfg(not(verus_keep_ghost))]
        return a.cmp(b);
        #[cfg(verus_keep_ghost)]
        {
            proof! { proof::text_identity(a@); proof::text_identity(b@); }
            return crate::trusted::compare_byte_slices(a, b);
        }
    }
    #[cfg(not(verus_keep_ghost))]
    let mut a_chars = a
        .iter()
        .filter(|&&c| filter_char(c, ignore_non_printing, ignore_non_dictionary));
    #[cfg(not(verus_keep_ghost))]
    let mut b_chars = b
        .iter()
        .filter(|&&c| filter_char(c, ignore_non_printing, ignore_non_dictionary));
    #[cfg(verus_keep_ghost)]
    let mut a_chars = crate::trusted::filter_bytes(a, TextFilter { ignore_non_printing, ignore_non_dictionary });
    #[cfg(verus_keep_ghost)]
    let mut b_chars = crate::trusted::filter_bytes(b, TextFilter { ignore_non_printing, ignore_non_dictionary });
    #[cfg(verus_keep_ghost)]
    proof! {
        proof::text_as_filtered(a@, ignore_case, ignore_non_dictionary, ignore_non_printing);
        proof::text_as_filtered(b@, ignore_case, ignore_non_dictionary, ignore_non_printing);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant proof::byte_order(
            proof::text_bytes(a@, ignore_case, ignore_non_dictionary, ignore_non_printing),
            proof::text_bytes(b@, ignore_case, ignore_non_dictionary, ignore_non_printing))
            == proof::byte_order(proof::mapped_case(a_chars.remaining(), ignore_case),
                proof::mapped_case(b_chars.remaining(), ignore_case)),
        decreases a_chars.remaining().len() + b_chars.remaining().len(),
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost left = a_chars.remaining(); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost right = b_chars.remaining(); }
        let a_char = a_chars.next();
        let b_char = b_chars.next();
        match (a_char, b_char) {
            (None, None) => return Ordering::Equal,
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (Some(a_char), Some(b_char)) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    proof::mapped_case_step(left, ignore_case);
                    proof::mapped_case_step(right, ignore_case);
                    proof::byte_order_step(proof::mapped_case(left, ignore_case),
                        proof::mapped_case(right, ignore_case));
                }
                let ordering = cmp_chars(*a_char, *b_char, ignore_case);
                if !matches!(ordering, Ordering::Equal) {
                    return ordering;
                }
            }
        }
    }
}
