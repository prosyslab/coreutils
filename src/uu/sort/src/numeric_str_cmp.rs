// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

// spell-checker:ignore KMGTPEZYRQ

//! Fast comparison for strings representing a base 10 number without precision loss.
//!
//! To be able to short-circuit when comparing, [`NumInfo`] must be passed along with each number
//! to [`numeric_str_cmp`]. [`NumInfo`] is generally obtained by calling [`NumInfo::parse`] and should be cached.
//! It is allowed to arbitrarily modify the exponent afterward, which is equivalent to shifting the decimal point.
//!
//! More specifically, exponent can be understood so that the original number is in `(1..10)*10^exponent`.
//! From that follows the constraints of this algorithm: It is able to compare numbers in ±(1*10^[`i64::MIN`]..10*10^[`i64::MAX`]).

use crate::custom_str_cmp::is_blank;
use std::{cmp::Ordering, ops::Range};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Sign {
    Negative,
    Positive,
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct NumInfo {
    pub exponent: i64,
    pub sign: Sign,
}
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct NumInfoParseSettings {
    pub accept_si_units: bool,
    /// Also accept lowercase SI units, as with `-f`.
    pub fold_si_units: bool,
    pub thousands_separator: Option<u8>,
    pub decimal_pt: Option<u8>,
}

impl Default for NumInfoParseSettings {
    fn default() -> Self {
        Self {
            accept_si_units: false,
            fold_si_units: false,
            thousands_separator: None,
            decimal_pt: Some(b'.'),
        }
    }
}

impl NumInfo {
    /// Parse [`NumInfo`] for this number.
    /// Also returns the range of num that should be passed to [`numeric_str_cmp`] later.
    ///
    /// Leading zeros will be excluded from the returned range. If the number consists of only zeros,
    /// an empty range (idx..idx) is returned so that idx is the char after the last zero.
    /// If the input is not a number (which has to be treated as zero), the returned empty range
    /// will be 0..0.
    #[allow(clippy::cognitive_complexity)]
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires parse_settings.thousands_separator is None,
            parse_settings.decimal_pt == Some(b'.'), num@.len() <= i64::MAX,
        ensures result.1.start <= result.1.end <= num.len(),
            crate::proof::parsing::represents(num@.subrange(result.1.start as int, result.1.end as int),
                result.0.exponent as int, matches!(result.0.sign, Sign::Negative),
                crate::proof::comparisons::decimal_model(num@, parse_settings.accept_si_units, parse_settings.fold_si_units),
                parse_settings.accept_si_units),
    ))]
    pub fn parse(num: &[u8], parse_settings: &NumInfoParseSettings) -> (Self, Range<usize>) {
        let mut exponent = -1;
        let mut had_decimal_pt = false;
        let mut had_digit = false;
        let mut start = None;
        let mut sign = Sign::Positive;

        let mut first_char = true;

        #[cfg(not(verus_keep_ghost))]
        let mut chars = num.iter().enumerate();
        #[cfg(verus_keep_ghost)]
        let mut chars = crate::trusted::parsing::enumerate(num);
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost all_chars = crate::trusted::parsing::remaining(&chars);
            let ghost mut processed = 0int;
            let ghost mut integer = Seq::<u8>::empty();
            let ghost mut fraction = Seq::<u8>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::slice::axiom_spec_len(num);
            crate::proof::parsing::initial(num@);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant 0 <= processed <= num@.len(), num@.len() <= i64::MAX,
                num@.len() <= usize::MAX,
                parse_settings.thousands_separator is None, parse_settings.decimal_pt == Some(b'.'),
                crate::proof::keys::enumeration_matches(num@, all_chars),
                crate::trusted::parsing::remaining(&chars) == all_chars.skip(processed),
                crate::trusted::parsing::remaining(&chars).len() + processed == num@.len(),
                crate::proof::parsing::state(num@, processed, first_char, matches!(sign, Sign::Negative),
                    had_decimal_pt, had_digit, exponent as int, start, integer, fraction),
                start is Some ==> processed > 0 &&
                    (crate::proof::comparisons::is_digit(num@[processed - 1]) || num@[processed - 1] == b'.'),
            ensures processed == num@.len(),
            decreases num@.len() - processed,
        ))]
        while let Some((idx, char)) = chars.next() {
            let char = *char;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost n = processed; }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(idx == n);
                assert(char == num@[n]);
                processed = n + 1;
            }
            if first_char && is_blank(char) {
                #[cfg(verus_keep_ghost)]
                proof! { crate::proof::parsing::skip_blank(num@, n); }
                continue;
            }

            if first_char && char == b'-' {
                sign = Sign::Negative;
                first_char = false;
                #[cfg(verus_keep_ghost)]
                proof! { crate::proof::parsing::skip_sign(num@, n); }
                continue;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::parsing::start_scanning(num@, n, first_char, matches!(sign, Sign::Negative),
                    had_decimal_pt, had_digit, exponent as int, start, integer, fraction);
            }
            first_char = false;

            if parse_settings.thousands_separator == Some(char) {
                continue;
            }

            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous_dot = had_decimal_pt; }
            if Self::is_invalid_char(char, &mut had_decimal_pt, parse_settings) {
                #[cfg(verus_keep_ghost)]
                proof! { assert(crate::proof::parsing::scanned(num@) == (n, integer, fraction)); }
                return if let Some(start) = start {
                    let unit = if parse_settings.fold_si_units {
                        char.to_ascii_uppercase()
                    } else {
                        char
                    };
                    #[cfg(not(verus_keep_ghost))]
                    let has_si_unit =
                        parse_settings.accept_si_units && b"kKMGTPEZYRQ".contains(&unit);
                    #[cfg(verus_keep_ghost)]
                    let has_si_unit = parse_settings.accept_si_units
                        && [b'k', b'K', b'M', b'G', b'T', b'P', b'E', b'Z', b'Y', b'R', b'Q'].contains(&unit);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proof::parsing::unit_membership(unit);
                        assert(has_si_unit == (parse_settings.accept_si_units
                            && crate::proof::parsing::unit_at(num@, n, parse_settings.fold_si_units) > 0));
                        crate::proof::parsing::finish_nonzero(num@, n, matches!(sign, Sign::Negative),
                            previous_dot, had_digit, exponent as int, start, integer, fraction,
                            parse_settings.accept_si_units, parse_settings.fold_si_units);
                    }
                    (
                        Self { exponent, sign },
                        start..if has_si_unit { idx + 1 } else { idx },
                    )
                } else {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proof::parsing::finish_zero(num@, n, integer, fraction,
                            parse_settings.accept_si_units, parse_settings.fold_si_units);
                        crate::proof::parsing::empty_range(num@, n);
                        crate::proof::parsing::empty_range(num@, 0);
                    }
                    (
                        Self {
                            sign: Sign::Positive,
                            exponent: 0,
                        },
                        if had_digit {
                            // In this case there were only zeroes.
                            // For debug output to work properly, we have to match the character after the last zero.
                            idx..idx
                        } else {
                            // This was no number at all.
                            // For debug output to work properly, we have to match 0..0.
                            0..0
                        },
                    )
                };
            }
            if Some(char) == parse_settings.decimal_pt {
                #[cfg(verus_keep_ghost)]
                proof! { crate::proof::parsing::step_dot(num@, n, matches!(sign, Sign::Negative),
                    had_digit, exponent as int, start, integer, fraction); }
                continue;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::parsing::step_digit(num@, n, matches!(sign, Sign::Negative), had_decimal_pt,
                    had_digit, exponent as int, start, integer, fraction);
                if had_decimal_pt { fraction = fraction.push(char); }
                else { integer = integer.push(char); }
            }
            had_digit = true;
            if start.is_none() && char == b'0' {
                if had_decimal_pt {
                    // We're parsing a number whose first nonzero digit is after the decimal point.
                    exponent -= 1;
                } else {
                    // Skip leading zeroes
                    continue;
                }
            }
            if !had_decimal_pt {
                exponent += 1;
            }
            if start.is_none() && char != b'0' {
                start = Some(idx);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::parsing::enumeration_end(num@, all_chars, processed);
            assert(processed == num@.len());
            if first_char {
                crate::proof::parsing::head_bounds(num@, 0);
                assert(crate::proof::parsing::scanned(num@) == (processed, integer, fraction));
            } else {
                assert(crate::proof::parsing::scanned(num@) == (processed, integer, fraction));
            }
        }
        if let Some(start) = start {
            #[cfg(verus_keep_ghost)]
            proof! { crate::proof::parsing::finish_nonzero(num@, processed, matches!(sign, Sign::Negative),
                had_decimal_pt, had_digit, exponent as int, start, integer, fraction,
                parse_settings.accept_si_units, parse_settings.fold_si_units); }
            (Self { exponent, sign }, start..num.len())
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::parsing::finish_zero(num@, processed, integer, fraction,
                    parse_settings.accept_si_units, parse_settings.fold_si_units);
                crate::proof::parsing::empty_range(num@, processed);
                crate::proof::parsing::empty_range(num@, 0);
            }
            (
                Self {
                    sign: Sign::Positive,
                    exponent: 0,
                },
                if had_digit {
                    // In this case there were only zeroes.
                    // For debug output to work properly, we have to claim to match the end of the number.
                    num.len()..num.len()
                } else {
                    // This was no number at all.
                    // For debug output to work properly, we have to claim to match the start of the number.
                    0..0
                },
            )
        }
    }

    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == if Some(c) == parse_settings.decimal_pt { *old(had_decimal_pt) }
                else { !crate::proof::comparisons::is_digit(c) },
            *final(had_decimal_pt) == (*old(had_decimal_pt) || Some(c) == parse_settings.decimal_pt),
    ))]
    fn is_invalid_char(
        c: u8,
        had_decimal_pt: &mut bool,
        parse_settings: &NumInfoParseSettings,
    ) -> bool {
        if Some(c) == parse_settings.decimal_pt {
            if *had_decimal_pt {
                // this is a decimal pt but we already had one, so it is invalid
                true
            } else {
                *had_decimal_pt = true;
                false
            }
        } else {
            !c.is_ascii_digit()
        }
    }
}

/// A lowercase unit other than `k` is only part of the range with `-f`, so it is
/// read as the uppercase one.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::proof::comparisons::native_unit(unit),
    no_unwind
))]
fn get_unit(unit: Option<u8>) -> u8 {
    match unit {
        Some(b'k' | b'K') => 1,
        Some(b'M' | b'm') => 2,
        Some(b'G' | b'g') => 3,
        Some(b'T' | b't') => 4,
        Some(b'P' | b'p') => 5,
        Some(b'E' | b'e') => 6,
        Some(b'Z' | b'z') => 7,
        Some(b'Y' | b'y') => 8,
        Some(b'R' | b'r') => 9,
        Some(b'Q' | b'q') => 10,
        _ => 0,
    }
}

/// Compare two numbers according to the rules of human numeric comparison.
/// The SI-Unit takes precedence over the actual value (i.e. 2000M < 1G).
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::proof::comparisons::native_human_order(left.0@, left.1.exponent as int,
        left.1.sign == Sign::Negative, right.0@, right.1.exponent as int, right.1.sign == Sign::Negative),
    no_unwind
))]
pub fn human_numeric_str_cmp(
    left: (&[u8], &NumInfo),
    right: (&[u8], &NumInfo),
) -> Ordering {
    let (a, a_info) = left;
    let (b, b_info) = right;
    // 1. Sign
    if !matches!((&a_info.sign, &b_info.sign), (Sign::Negative, Sign::Negative) | (Sign::Positive, Sign::Positive)) {
        return if matches!(a_info.sign, Sign::Negative) { Ordering::Less } else { Ordering::Greater };
    }
    // 2. Unit
    #[cfg(not(verus_keep_ghost))]
    let a_unit = get_unit(a.iter().next_back().copied());
    #[cfg(not(verus_keep_ghost))]
    let b_unit = get_unit(b.iter().next_back().copied());
    #[cfg(verus_keep_ghost)]
    let a_unit = get_unit(crate::trusted::comparisons::last_byte(a));
    #[cfg(verus_keep_ghost)]
    let b_unit = get_unit(crate::trusted::comparisons::last_byte(b));
    #[cfg(not(verus_keep_ghost))]
    let ordering = a_unit.cmp(&b_unit);
    #[cfg(verus_keep_ghost)]
    let ordering = crate::trusted::comparisons::cmp_u8(a_unit, b_unit);
    if matches!(ordering, Ordering::Equal) {
        // 3. Number
        numeric_str_cmp((a, a_info), (b, b_info))
    } else if matches!(a_info.sign, Sign::Negative) {
        ordering.reverse()
    } else {
        ordering
    }
}

/// Compare two numbers as strings without parsing them as a number first. This should be more performant and can handle numbers more precisely.
/// [`NumInfo`] is needed to provide a fast path for most numbers.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::proof::comparisons::native_numeric_order(left.0@, left.1.exponent as int,
        left.1.sign == Sign::Negative, right.0@, right.1.exponent as int, right.1.sign == Sign::Negative),
    no_unwind
))]
pub fn numeric_str_cmp(left: (&[u8], &NumInfo), right: (&[u8], &NumInfo)) -> Ordering {
    let (a, a_info) = left;
    let (b, b_info) = right;
    // check for a difference in the sign
    if !matches!((&a_info.sign, &b_info.sign), (Sign::Negative, Sign::Negative) | (Sign::Positive, Sign::Positive)) {
        return if matches!(a_info.sign, Sign::Negative) { Ordering::Less } else { Ordering::Greater };
    }

    // check for a difference in the exponent
    #[cfg(not(verus_keep_ghost))]
    let (a_len, b_len) = (a.len(), b.len());
    #[cfg(verus_keep_ghost)]
    let (a_len, b_len) = (crate::trusted::comparisons::slice_len(a), crate::trusted::comparisons::slice_len(b));
    let ordering = if a_info.exponent != b_info.exponent && a_len > 0 && b_len > 0 {
        #[cfg(not(verus_keep_ghost))]
        { a_info.exponent.cmp(&b_info.exponent) }
        #[cfg(verus_keep_ghost)]
        { crate::trusted::comparisons::cmp_i64(a_info.exponent, b_info.exponent) }
    } else {
        // walk the characters from the front until we find a difference
        #[cfg(not(verus_keep_ghost))]
        let mut a_chars = a.iter().copied().filter(u8::is_ascii_digit);
        #[cfg(not(verus_keep_ghost))]
        let mut b_chars = b.iter().copied().filter(u8::is_ascii_digit);
        #[cfg(verus_keep_ghost)]
        let mut a_chars = crate::trusted::comparisons::digit_bytes(a);
        #[cfg(verus_keep_ghost)]
        let mut b_chars = crate::trusted::comparisons::digit_bytes(b);
        #[cfg(not(verus_keep_ghost))]
        let is_zero = |c| c == b'0';
        let mut result = Ordering::Equal;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost left = a_chars.remaining();
            let ghost right = b_chars.remaining();
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant_except_break crate::proof::comparisons::padded_order(left, right)
                == crate::proof::comparisons::padded_order(a_chars.remaining(), b_chars.remaining()),
            ensures result == crate::proof::comparisons::padded_order(left, right),
            decreases a_chars.remaining().len() + b_chars.remaining().len(),
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost a_before = a_chars.remaining();
                let ghost b_before = b_chars.remaining();
            }
            let a_next = a_chars.next();
            let b_next = b_chars.next();
            #[cfg(verus_keep_ghost)]
            proof! {
                if a_before.len() > 0 { crate::proof::comparisons::zero_sequence_step(a_before); }
                if b_before.len() > 0 { crate::proof::comparisons::zero_sequence_step(b_before); }
            }
            match (a_next, b_next) {
                (None, None) => { result = Ordering::Equal; break; },
                (Some(c), None) => {
                    #[cfg(not(verus_keep_ghost))]
                    let remaining_zero = c == b'0' && a_chars.all(is_zero);
                    #[cfg(verus_keep_ghost)]
                    let remaining_zero = c == b'0' && a_chars.all_zero();
                    result = if remaining_zero {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    };
                    break;
                }
                (None, Some(c)) => {
                    #[cfg(not(verus_keep_ghost))]
                    let remaining_zero = c == b'0' && b_chars.all(is_zero);
                    #[cfg(verus_keep_ghost)]
                    let remaining_zero = c == b'0' && b_chars.all_zero();
                    result = if remaining_zero {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                    break;
                }
                (Some(a_char), Some(b_char)) => {
                    #[cfg(verus_keep_ghost)]
                    proof! { crate::proof::comparisons::padded_step(a_before, b_before); }
                    #[cfg(not(verus_keep_ghost))]
                    let ord = a_char.cmp(&b_char);
                    #[cfg(verus_keep_ghost)]
                    let ord = crate::trusted::comparisons::cmp_u8(a_char, b_char);
                    if !matches!(ord, Ordering::Equal) {
                        result = ord;
                        break;
                    }
                }
            }
        }
        result
    };

    if matches!(a_info.sign, Sign::Negative) {
        ordering.reverse()
    } else {
        ordering
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_exp() {
        let n = b"1";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Positive
                },
                0..1
            )
        );
        let n = b"100";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 2,
                    sign: Sign::Positive
                },
                0..3
            )
        );
        let n = b"1,000";
        assert_eq!(
            NumInfo::parse(
                n,
                &NumInfoParseSettings {
                    thousands_separator: Some(b','),
                    ..Default::default()
                }
            ),
            (
                NumInfo {
                    exponent: 3,
                    sign: Sign::Positive
                },
                0..5
            )
        );
        let n = b"1,000";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Positive
                },
                0..1
            )
        );
        let n = b"1000.00";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 3,
                    sign: Sign::Positive
                },
                0..7
            )
        );
    }
    #[test]
    fn parses_negative_exp() {
        let n = b"0.00005";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: -5,
                    sign: Sign::Positive
                },
                6..7
            )
        );
        let n = b"00000.00005";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: -5,
                    sign: Sign::Positive
                },
                10..11
            )
        );
    }

    #[test]
    fn parses_sign() {
        let n = b"5";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Positive
                },
                0..1
            )
        );
        let n = b"-5";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Negative
                },
                1..2
            )
        );
        let n = b"    -5";
        assert_eq!(
            NumInfo::parse(n, &NumInfoParseSettings::default()),
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Negative
                },
                5..6
            )
        );
    }

    fn test_helper(a: &[u8], b: &[u8], expected: Ordering) {
        let (a_info, a_range) = NumInfo::parse(a, &NumInfoParseSettings::default());
        let (b_info, b_range) = NumInfo::parse(b, &NumInfoParseSettings::default());
        let ordering = numeric_str_cmp(
            (&a[a_range.clone()], &a_info),
            (&b[b_range.clone()], &b_info),
        );
        assert_eq!(ordering, expected);
        let ordering = numeric_str_cmp((&b[b_range], &b_info), (&a[a_range], &a_info));
        assert_eq!(ordering, expected.reverse());
    }
    #[test]
    fn test_single_digit() {
        test_helper(b"1", b"2", Ordering::Less);
        test_helper(b"0", b"0", Ordering::Equal);
    }
    #[test]
    fn test_minus() {
        test_helper(b"-1", b"-2", Ordering::Greater);
        test_helper(b"-0", b"-0", Ordering::Equal);
    }
    #[test]
    fn test_different_len() {
        test_helper(b"-20", b"-100", Ordering::Greater);
        test_helper(b"10.0", b"2.000000", Ordering::Greater);
    }
    #[test]
    fn test_decimal_digits() {
        test_helper(b"20.1", b"20.2", Ordering::Less);
        test_helper(b"20.1", b"20.15", Ordering::Less);
        test_helper(b"-20.1", b"+20.15", Ordering::Less);
        test_helper(b"-20.1", b"-20", Ordering::Less);
    }
    #[test]
    fn test_trailing_zeroes() {
        test_helper(b"20.00000", b"20.1", Ordering::Less);
        test_helper(b"20.00000", b"20.0", Ordering::Equal);
    }
    #[test]
    fn test_invalid_digits() {
        test_helper(b"foo", b"bar", Ordering::Equal);
        test_helper(b"20.1", b"a", Ordering::Greater);
        test_helper(b"-20.1", b"a", Ordering::Less);
        test_helper(b"a", b"0.15", Ordering::Less);
    }
    #[test]
    fn test_multiple_decimal_pts() {
        test_helper(b"10.0.0", b"50.0.0", Ordering::Less);
        test_helper(b"0.1.", b"0.2.0", Ordering::Less);
        test_helper(b"1.1.", b"0", Ordering::Greater);
        test_helper(b"1.1.", b"-0", Ordering::Greater);
    }
    #[test]
    fn test_leading_decimal_pts() {
        test_helper(b".0", b".0", Ordering::Equal);
        test_helper(b".1", b".0", Ordering::Greater);
        test_helper(b".02", b"0", Ordering::Greater);
    }
    #[test]
    fn test_leading_zeroes() {
        test_helper(b"000000.0", b".0", Ordering::Equal);
        test_helper(b"0.1", b"0000000000000.0", Ordering::Greater);
        test_helper(b"-01", b"-2", Ordering::Greater);
    }

    #[test]
    fn minus_zero() {
        // This matches GNU sort behavior.
        test_helper(b"-0", b"0", Ordering::Equal);
        test_helper(b"-0x", b"0", Ordering::Equal);
    }
    #[test]
    fn double_minus() {
        test_helper(b"--1", b"0", Ordering::Equal);
    }
    #[test]
    fn single_minus() {
        let info = NumInfo::parse(b"-", &NumInfoParseSettings::default());
        assert_eq!(
            info,
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Positive
                },
                0..0
            )
        );
    }
    #[test]
    fn invalid_with_unit() {
        let info = NumInfo::parse(
            b"-K",
            &NumInfoParseSettings {
                accept_si_units: true,
                ..Default::default()
            },
        );
        assert_eq!(
            info,
            (
                NumInfo {
                    exponent: 0,
                    sign: Sign::Positive
                },
                0..0
            )
        );
    }
}
