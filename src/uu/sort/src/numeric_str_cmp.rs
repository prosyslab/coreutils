// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::custom_str_cmp::is_blank;
use std::{cmp::Ordering, ops::Range};
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Sign {
    Negative,
    Positive,
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NumInfo {
    pub exponent: i64,
    pub sign: Sign,
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NumInfoParseSettings {
    pub accept_si_units: bool,
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
    #[allow(clippy::cognitive_complexity)]
    pub fn parse(num: &[u8], parse_settings: &NumInfoParseSettings) -> (Self, Range<usize>) {
        let mut exponent = -1;
        let mut had_decimal_pt = false;
        let mut had_digit = false;
        let mut start = None;
        let mut sign = Sign::Positive;
        let mut first_char = true;
        let mut chars = crate::trusted::parsing::enumerate(num);
        while let Some((idx, char)) = chars.next() {
            let char = *char;
            if first_char && is_blank(char) {
                continue;
            }
            if first_char && char == b'-' {
                sign = Sign::Negative;
                first_char = false;
                continue;
            }
            first_char = false;
            if parse_settings.thousands_separator == Some(char) {
                continue;
            }
            if Self::is_invalid_char(char, &mut had_decimal_pt, parse_settings) {
                return if let Some(start) = start {
                    let unit = if parse_settings.fold_si_units {
                        char.to_ascii_uppercase()
                    } else {
                        char
                    };
                    let has_si_unit = parse_settings.accept_si_units
                        && [
                            b'k', b'K', b'M', b'G', b'T', b'P', b'E', b'Z', b'Y', b'R', b'Q',
                        ]
                        .contains(&unit);
                    (
                        Self { exponent, sign },
                        start..if has_si_unit { idx + 1 } else { idx },
                    )
                } else {
                    (
                        Self {
                            sign: Sign::Positive,
                            exponent: 0,
                        },
                        if had_digit { idx..idx } else { 0..0 },
                    )
                };
            }
            if Some(char) == parse_settings.decimal_pt {
                continue;
            }
            had_digit = true;
            if start.is_none() && char == b'0' {
                if had_decimal_pt {
                    exponent -= 1;
                } else {
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
        if let Some(start) = start {
            (Self { exponent, sign }, start..num.len())
        } else {
            (
                Self {
                    sign: Sign::Positive,
                    exponent: 0,
                },
                if had_digit {
                    num.len()..num.len()
                } else {
                    0..0
                },
            )
        }
    }
    fn is_invalid_char(
        c: u8,
        had_decimal_pt: &mut bool,
        parse_settings: &NumInfoParseSettings,
    ) -> bool {
        if Some(c) == parse_settings.decimal_pt {
            if *had_decimal_pt {
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
pub fn human_numeric_str_cmp(left: (&[u8], &NumInfo), right: (&[u8], &NumInfo)) -> Ordering {
    let (a, a_info) = left;
    let (b, b_info) = right;
    if !matches!(
        (&a_info.sign, &b_info.sign),
        (Sign::Negative, Sign::Negative) | (Sign::Positive, Sign::Positive)
    ) {
        return if matches!(a_info.sign, Sign::Negative) {
            Ordering::Less
        } else {
            Ordering::Greater
        };
    }
    let a_unit = get_unit(crate::trusted::comparisons::last_byte(a));
    let b_unit = get_unit(crate::trusted::comparisons::last_byte(b));
    let ordering = crate::trusted::comparisons::cmp_u8(a_unit, b_unit);
    if matches!(ordering, Ordering::Equal) {
        numeric_str_cmp((a, a_info), (b, b_info))
    } else if matches!(a_info.sign, Sign::Negative) {
        ordering.reverse()
    } else {
        ordering
    }
}
#[inline(always)]
pub fn numeric_str_cmp(left: (&[u8], &NumInfo), right: (&[u8], &NumInfo)) -> Ordering {
    let (a, a_info) = left;
    let (b, b_info) = right;
    if !matches!(
        (&a_info.sign, &b_info.sign),
        (Sign::Negative, Sign::Negative) | (Sign::Positive, Sign::Positive)
    ) {
        return if matches!(a_info.sign, Sign::Negative) {
            Ordering::Less
        } else {
            Ordering::Greater
        };
    }
    let (a_len, b_len) = (
        crate::trusted::comparisons::slice_len(a),
        crate::trusted::comparisons::slice_len(b),
    );
    let ordering = if a_info.exponent != b_info.exponent && a_len > 0 && b_len > 0 {
        { crate::trusted::comparisons::cmp_i64(a_info.exponent, b_info.exponent) }
    } else {
        let mut a_chars = crate::trusted::comparisons::digit_bytes(a);
        let mut b_chars = crate::trusted::comparisons::digit_bytes(b);
        let mut result = Ordering::Equal;
        loop {
            let a_next = a_chars.next();
            let b_next = b_chars.next();
            match (a_next, b_next) {
                (None, None) => {
                    result = Ordering::Equal;
                    break;
                }
                (Some(c), None) => {
                    let remaining_zero = c == b'0' && a_chars.all_zero();
                    result = if remaining_zero {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    };
                    break;
                }
                (None, Some(c)) => {
                    let remaining_zero = c == b'0' && b_chars.all_zero();
                    result = if remaining_zero {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                    break;
                }
                (Some(a_char), Some(b_char)) => {
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
