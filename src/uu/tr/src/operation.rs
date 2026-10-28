// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

// spell-checker:ignore (strings) anychar combinator Alnum Punct Xdigit alnum punct xdigit cntrl alpah

#[cfg(not(verus_keep_ghost))]
use crate::unicode_table;
#[cfg(not(verus_keep_ghost))]
use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take, take_till, take_until},
    character::complete::one_of,
    combinator::{map, map_opt, peek, recognize, value},
    multi::many_m_n,
    sequence::{delimited, preceded, separated_pair, terminated},
};
#[cfg(not(verus_keep_ghost))]
use std::{
    char,
    error::Error,
    fmt::{Debug, Display},
    io::{BufRead, Write},
    ops::Range,
};
#[cfg(not(verus_keep_ghost))]
use uucore::error::{FromIo, UError, UResult};
#[cfg(not(verus_keep_ghost))]
use uucore::translate;

#[cfg(not(verus_keep_ghost))]
use uucore::show_warning;

#[cfg(verus_keep_ghost)]
use std::io::{BufRead, Write};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
type UResult<T> = std::io::Result<T>;
#[cfg(verus_keep_ghost)]
use crate::stream_proof::TranslatorModel;
#[cfg(verus_keep_ghost)]
use crate::tr_proof::ChunkModel;
#[cfg(verus_keep_ghost)]
use crate::{io_trusted, stream_proof};
#[cfg(not(verus_keep_ghost))]
pub trait TranslatorModel {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> TranslatorModel for T {}
#[cfg(not(verus_keep_ghost))]
pub trait ChunkModel {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> ChunkModel for T {}
#[cfg(verus_keep_ghost)]
verus! { broadcast use vstd::seq_lib::group_seq_properties; }
#[cfg(not(verus_keep_ghost))]
pub(crate) use crate::simd::trusted_common::io as io_trusted;

/// Common trait for operations that can process chunks of data
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub trait ChunkProcessor: ChunkModel {
    /// Return the bytes to write: `input` itself when it is left unchanged,
    /// `output` otherwise.
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.chunk_valid(), old(output).len() == 0,
        ensures result@ == self.chunk_output(input@),
    ))]
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8];
}

#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Clone)]
pub enum BadSequence {
    MissingCharClassName,
    InvalidCharClass(String),
    MissingEquivalentClassChar,
    MultipleCharRepeatInSet2,
    CharRepeatInSet1,
    InvalidRepeatCount(String),
    EmptySet2WhenNotTruncatingSet1,
    ClassExceptLowerUpperInSet2,
    ClassInSet2NotMatchedBySet1,
    Set1LongerSet2EndsInClass,
    ComplementMoreThanOneUniqueInSet2,
    BackwardsRange { end: u32, start: u32 },
    MultipleCharInEquivalence(String),
}

/// A range endpoint, printed the way the shell would show it: as itself for
/// printable ASCII — backslash-escaped where Rust escapes it, so `\` and the
/// quotes come back doubled — and as an octal escape otherwise.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn range_endpoint_to_string(ut: u32) -> String {
    match char::from_u32(ut) {
        Some(ch @ '\x20'..='\x7E') => ch.escape_default().to_string(),
        _ => format!("\\{ut:03o}"),
    }
}

#[cfg(not(verus_keep_ghost))]
impl Display for BadSequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingCharClassName => {
                write!(f, "{}", translate!("tr-error-missing-char-class-name"))
            }
            Self::InvalidCharClass(class) => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-invalid-char-class", "class" => format!("'{}'", class))
                )
            }
            Self::MissingEquivalentClassChar => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-missing-equivalence-class-char")
                )
            }
            Self::MultipleCharRepeatInSet2 => {
                write!(f, "{}", translate!("tr-error-multiple-char-repeat-in-set2"))
            }
            Self::CharRepeatInSet1 => {
                write!(f, "{}", translate!("tr-error-char-repeat-in-set1"))
            }
            Self::InvalidRepeatCount(count) => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-invalid-repeat-count", "count" => format!("'{count}'"))
                )
            }
            Self::EmptySet2WhenNotTruncatingSet1 => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-empty-set2-when-not-truncating")
                )
            }
            Self::ClassExceptLowerUpperInSet2 => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-class-except-lower-upper-in-set2")
                )
            }
            Self::ClassInSet2NotMatchedBySet1 => {
                write!(f, "{}", translate!("tr-error-class-in-set2-not-matched"))
            }
            Self::Set1LongerSet2EndsInClass => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-set1-longer-set2-ends-in-class")
                )
            }
            Self::ComplementMoreThanOneUniqueInSet2 => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-complement-more-than-one-unique")
                )
            }
            Self::BackwardsRange { end, start } => {
                write!(
                    f,
                    "{}",
                    translate!("tr-error-backwards-range", "start" => range_endpoint_to_string(*start), "end" => range_endpoint_to_string(*end))
                )
            }
            Self::MultipleCharInEquivalence(s) => write!(
                f,
                "{}",
                translate!("tr-error-multiple-char-in-equivalence", "chars" => s)
            ),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl Error for BadSequence {}

#[cfg(not(verus_keep_ghost))]
impl UError for BadSequence {}

/// A [`BadSequence`] together with where it was written.
///
/// A set is a small language of its own, so naming the set and the sequence
/// inside it says far more than the message alone: `[:alpah:]` and `[a-Z]` are
/// both "in SET1", but only one character of each is actually wrong.
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Clone)]
pub struct SequenceError {
    pub error: BadSequence,
    /// Which set the problem is in, numbered as the operands are: 1 or 2.
    pub set: u8,
    /// Byte range inside that set, or `None` when the set as a whole is at
    /// fault rather than one sequence in it.
    pub span: Option<Range<usize>>,
}

#[cfg(not(verus_keep_ghost))]
impl SequenceError {
    /// A problem with a set taken as a whole.
    fn whole_set(error: BadSequence, set: u8) -> Self {
        Self {
            error,
            set,
            span: None,
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl Display for SequenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The location is for the caret only; the message reads as it always
        // has.
        Display::fmt(&self.error, f)
    }
}

#[cfg(not(verus_keep_ghost))]
impl Error for SequenceError {}

#[cfg(not(verus_keep_ghost))]
impl UError for SequenceError {}

#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Clone, Copy)]
pub enum Class {
    Alnum,
    Alpha,
    Blank,
    Control,
    Digit,
    Graph,
    Lower,
    Print,
    Punct,
    Space,
    Upper,
    Xdigit,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Clone, Copy)]
pub enum Sequence {
    Char(u8),
    CharRange(u8, u8),
    CharStar(u8),
    CharRepeat(u8, usize),
    Class(Class),
}

#[cfg(not(verus_keep_ghost))]
impl Sequence {
    pub fn flatten(&self) -> Box<dyn Iterator<Item = u8>> {
        match self {
            Self::Char(c) => Box::new(std::iter::once(*c)),
            Self::CharRange(l, r) => Box::new(*l..=*r),
            Self::CharStar(c) => Box::new(std::iter::repeat(*c)),
            Self::CharRepeat(c, n) => Box::new(std::iter::repeat_n(*c, *n)),
            Self::Class(class) => match class {
                Class::Alnum => Box::new((b'0'..=b'9').chain(b'A'..=b'Z').chain(b'a'..=b'z')),
                Class::Alpha => Box::new((b'A'..=b'Z').chain(b'a'..=b'z')),
                Class::Blank => Box::new(unicode_table::BLANK.iter().copied()),
                Class::Control => Box::new((0..=31).chain(std::iter::once(127))),
                Class::Digit => Box::new(b'0'..=b'9'),
                Class::Graph => Box::new(
                    (48..=57) // digit
                        .chain(65..=90) // uppercase
                        .chain(97..=122) // lowercase
                        // punctuations
                        .chain(33..=47)
                        .chain(58..=64)
                        .chain(91..=96)
                        .chain(123..=126),
                ),
                Class::Print => Box::new(
                    (48..=57) // digit
                        .chain(65..=90) // uppercase
                        .chain(97..=122) // lowercase
                        // punctuations
                        .chain(33..=47)
                        .chain(58..=64)
                        .chain(91..=96)
                        .chain(123..=126)
                        .chain(std::iter::once(32)), // space
                ),
                Class::Punct => Box::new((33..=47).chain(58..=64).chain(91..=96).chain(123..=126)),
                Class::Space => Box::new(unicode_table::SPACES.iter().copied()),
                Class::Xdigit => Box::new((b'0'..=b'9').chain(b'A'..=b'F').chain(b'a'..=b'f')),
                Class::Lower => Box::new(b'a'..=b'z'),
                Class::Upper => Box::new(b'A'..=b'Z'),
            },
        }
    }

    /// How many characters the sequence expands to, without expanding it:
    /// the count of a `[c*n]` repeat can be far too large to materialize.
    fn expanded_len(&self) -> usize {
        match self {
            Self::Char(_) => 1,
            Self::CharRange(l, r) => usize::from(*r) - usize::from(*l) + 1,
            // A star is only sized once it has been turned into a repeat.
            Self::CharStar(_) => 0,
            Self::CharRepeat(_, n) => *n,
            Self::Class(_) => self.flatten().count(),
        }
    }

    /// The expanded length of a set. Widened so that repeat counts close to
    /// `usize::MAX` still add up exactly and positions keep their order.
    fn expanded_len_of(set: &[Self]) -> u128 {
        set.iter().map(|s| s.expanded_len() as u128).sum()
    }

    /// The characters of a set, in order, as runs of a repeated character.
    ///
    /// A `[c*n]` repeat is a single run however large `n` is; everything else
    /// expands to runs of one character. Empty runs are left out, and a star
    /// must have been turned into a repeat first.
    fn runs(set: &[Self]) -> impl Iterator<Item = (u8, usize)> + '_ {
        set.iter()
            .flat_map(|s| -> Box<dyn Iterator<Item = (u8, usize)>> {
                match s {
                    Self::CharRepeat(c, n) => Box::new(std::iter::once((*c, *n))),
                    Self::CharStar(_) => Box::new(std::iter::empty()),
                    _ => Box::new(s.flatten().map(|c| (c, 1))),
                }
            })
            .filter(|(_, n)| *n > 0)
    }

    /// The number of characters in a set of runs, widened like `expanded_len_of`.
    fn runs_len(runs: &[(u8, usize)]) -> u128 {
        runs.iter().map(|(_, n)| *n as u128).sum()
    }

    /// The characters a set of runs is made of, as a sorted list without duplicates.
    fn unique_chars(runs: &[(u8, usize)]) -> Vec<u8> {
        let mut uniques: Vec<u8> = runs.iter().map(|(c, _)| *c).collect();
        uniques.sort_unstable();
        uniques.dedup();
        uniques
    }

    /// The complement of the characters that a set holds, or that its first
    /// `len` positions hold, one run per character.
    fn complement_of_prefix(set: &[Self], len: Option<u128>) -> Vec<(u8, usize)> {
        let mut present = [false; 256];
        let mut remaining = len;
        for (c, n) in Self::runs(set) {
            if remaining == Some(0) {
                break;
            }
            present[usize::from(c)] = true;
            remaining = remaining.map(|left| left.saturating_sub(n as u128));
        }
        (0..=u8::MAX)
            .filter(|c| !present[usize::from(*c)])
            .map(|c| (c, 1))
            .collect()
    }

    // Hide all the nasty sh*t in here
    pub fn solve_set_characters(
        set1_str: &[u8],
        set2_str: &[u8],
        complement_flag: bool,
        truncate_set1_flag: bool,
        translating: bool,
    ) -> Result<(Vec<u8>, Vec<u8>), SequenceError> {
        let is_char_star = |s: &&Self| -> bool { matches!(s, Self::CharStar(_)) };

        let set1 = Self::parse_set(set1_str).map_err(|(error, span)| SequenceError {
            error,
            set: 1,
            span: Some(span),
        })?;
        if set1.iter().filter(is_char_star).count() != 0 {
            return Err(SequenceError::whole_set(BadSequence::CharRepeatInSet1, 1));
        }

        let mut set2 = Self::parse_set(set2_str).map_err(|(error, span)| SequenceError {
            error,
            set: 2,
            span: Some(span),
        })?;
        if set2.iter().filter(is_char_star).count() > 1 {
            return Err(SequenceError::whole_set(
                BadSequence::MultipleCharRepeatInSet2,
                2,
            ));
        }

        if translating
            && set2.iter().any(|&x| {
                matches!(x, Self::Class(_))
                    && !matches!(x, Self::Class(Class::Upper | Class::Lower))
            })
        {
            return Err(SequenceError::whole_set(
                BadSequence::ClassExceptLowerUpperInSet2,
                2,
            ));
        }

        // Neither set is expanded character by character: a `[c*n]` repeat can
        // be far too large for that. Both are handled as runs of one character
        // instead, and only the lengths are ever computed in full.
        let mut set1_runs: Vec<(u8, usize)> = if complement_flag {
            Self::complement_of_prefix(&set1, None)
        } else {
            Self::runs(&set1).collect()
        };
        let set1_len = Self::runs_len(&set1_runs);

        // A star has no length of its own until it is turned into a repeat,
        // so this is the length of everything else in set2.
        let set2_fixed_len = Self::expanded_len_of(&set2);

        let star_compensate_len =
            usize::try_from(set1_len.saturating_sub(set2_fixed_len)).unwrap_or(usize::MAX);
        //Replace CharStar with CharRepeat
        set2 = set2
            .iter()
            .filter_map(|s| match s {
                Self::CharStar(0) => None,
                Self::CharStar(c) => Some(Self::CharRepeat(*c, star_compensate_len)),
                r => Some(*r),
            })
            .collect();

        // For every upper/lower in set2, there must be an upper/lower in set1 at the same position. The position is calculated by expanding everything before the upper/lower in both sets
        // This only applies when translating. With `-d -s`, set2 is only the set to squeeze.
        for (set2_pos, set2_item) in set2.iter().enumerate() {
            if translating && matches!(set2_item, Self::Class(_)) {
                let set2_part_solved_len = Self::expanded_len_of(&set2[..set2_pos]);

                let mut class_matches = false;
                for (set1_pos, set1_item) in set1.iter().enumerate() {
                    if matches!(set1_item, Self::Class(_))
                        && Self::expanded_len_of(&set1[..set1_pos]) == set2_part_solved_len
                    {
                        class_matches = true;
                        break;
                    }
                }

                if !class_matches {
                    return Err(SequenceError::whole_set(
                        BadSequence::ClassInSet2NotMatchedBySet1,
                        2,
                    ));
                }
            }
        }

        let set2_runs: Vec<(u8, usize)> = Self::runs(&set2).collect();
        let set2_len = Self::runs_len(&set2_runs);

        // Calculate the set of unique characters in set2
        let set2_uniques = Self::unique_chars(&set2_runs);

        let set1_has_class = set1.iter().any(|x| matches!(x, Self::Class(_)));
        // If the complement flag is used in translate mode, only one unique
        // character may appear in set2. Validate this with the set of uniques
        // in set2 that we just generated.
        // Also, set2 must not overgrow set1, otherwise the mapping can't be 1:1.
        if set1_has_class
            && translating
            && complement_flag
            && (set2_uniques.len() > 1 || set2_len > set1_len)
        {
            return Err(SequenceError::whole_set(
                BadSequence::ComplementMoreThanOneUniqueInSet2,
                2,
            ));
        }

        if set2_len < set1_len {
            if truncate_set1_flag {
                if complement_flag && set1_has_class {
                    // GNU applies -t before complementing a character class.
                    // That means we must first truncate the expanded, non-complemented
                    // source set, then complement the truncated prefix to recover the
                    // final translation domain.
                    set1_runs = Self::complement_of_prefix(&set1, Some(set2_len));
                    // After expansion the complemented domain may be larger than set2.
                    // Re-check the complement validity constraint.
                    if set2_uniques.len() > 1 || set1_runs.len() as u128 > set2_len {
                        return Err(SequenceError::whole_set(
                            BadSequence::ComplementMoreThanOneUniqueInSet2,
                            2,
                        ));
                    }
                }
                // Otherwise set1 is cut to the length of set2 while pairing below.
            } else if matches!(
                set2.last().copied(),
                Some(Self::Class(Class::Upper | Class::Lower))
            ) {
                return Err(SequenceError::whole_set(
                    BadSequence::Set1LongerSet2EndsInClass,
                    1,
                ));
            }
        }

        // Line the two sets up position by position, one run at a time. A run
        // of one character in set1 maps that character to every character it
        // lines up with in set2, and the last mapping wins, so the pair at the
        // end of each run boundary is all that is kept: the pairs in between
        // repeat it. Once set2 runs out, set1 is either cut (-t) or the rest
        // of it maps to the last character of set2.
        let fallback = set2_runs.last().map(|(c, _)| *c);
        let mut set1_solved = Vec::new();
        let mut set2_solved = Vec::new();
        let mut set2_runs = set2_runs.into_iter();
        let mut pending = set2_runs.next();
        'pairing: for (c1, mut n1) in set1_runs {
            while n1 > 0 {
                let Some((c2, n2)) = pending else {
                    if truncate_set1_flag {
                        break 'pairing;
                    }
                    set1_solved.push(c1);
                    set2_solved.extend(fallback);
                    break;
                };
                set1_solved.push(c1);
                set2_solved.push(c2);
                let step = n1.min(n2);
                n1 -= step;
                pending = if n2 > step {
                    Some((c2, n2 - step))
                } else {
                    set2_runs.next()
                };
            }
        }
        // What is left of set2 is still part of it: with -s, the characters
        // to squeeze come from all of set2.
        set2_solved.extend(pending.into_iter().chain(set2_runs).map(|(c, _)| c));

        Ok((set1_solved, set2_solved))
    }
}

#[cfg(not(verus_keep_ghost))]
impl Sequence {
    /// Parse a set, reporting which part of it a bad sequence occupies.
    ///
    /// The alternatives are tried in the same order as before; the loop only
    /// replaces `many0` so that how much each sequence consumed is still known
    /// once it turns out to be wrong. Like `many0`, it consumes the whole set
    /// even past a bad sequence: parsing the tail emits the warnings — an
    /// ambiguous octal escape, invalid UTF-8 — that it always has.
    fn parse_set(input: &[u8]) -> Result<Vec<Self>, (BadSequence, Range<usize>)> {
        let mut result = Vec::new();
        let mut first_error = None;
        let mut rest = input;
        while !rest.is_empty() {
            let start = input.len() - rest.len();
            let parsed = alt((
                Self::parse_char_star,
                Self::parse_char_repeat,
                Self::parse_class,
                Self::parse_char_equal,
                Self::parse_char_range,
                // NOTE: This must be the last one
                map(Self::parse_backslash_or_char_with_warning, |s| {
                    Ok(Self::Char(s))
                }),
            ))
            .parse(rest);
            // The last alternative accepts any single byte, so this only
            // happens on input the loop has already run out of.
            let Ok((next, sequence)) = parsed else { break };
            // `many0` refuses an alternative that matched nothing rather than
            // loop on it forever; none of the ones above can, but the loop is
            // no place to find out if one ever does.
            if next.len() == rest.len() {
                break;
            }
            let end = input.len() - next.len();
            match sequence {
                Ok(sequence) => result.push(sequence),
                Err(error) => {
                    first_error.get_or_insert((error, start..end));
                }
            }
            rest = next;
        }
        match first_error {
            Some(error) => Err(error),
            None => Ok(result),
        }
    }

    fn parse_octal(input: &[u8]) -> IResult<&[u8], u8> {
        // For `parse_char_range`, `parse_char_star`, `parse_char_repeat`, `parse_char_equal`.
        // Because in these patterns, there's no ambiguous cases.
        preceded(tag("\\"), Self::parse_octal_up_to_three_digits).parse(input)
    }

    fn parse_octal_with_warning(input: &[u8]) -> IResult<&[u8], u8> {
        preceded(
            tag("\\"),
            alt((
                Self::parse_octal_up_to_three_digits_with_warning,
                // Fallback for if the three digit octal escape is greater than \377 (0xFF), and therefore can't be
                // parsed as as a byte
                // See test `test_multibyte_octal_sequence`
                Self::parse_octal_two_digits,
            )),
        )
        .parse(input)
    }

    fn parse_octal_up_to_three_digits(input: &[u8]) -> IResult<&[u8], u8> {
        map_opt(
            recognize(many_m_n(1, 3, one_of("01234567"))),
            |out: &[u8]| {
                let str_to_parse = std::str::from_utf8(out).unwrap();
                u8::from_str_radix(str_to_parse, 8).ok()
            },
        )
        .parse(input)
    }

    fn parse_octal_up_to_three_digits_with_warning(input: &[u8]) -> IResult<&[u8], u8> {
        map_opt(
            recognize(many_m_n(1, 3, one_of("01234567"))),
            |out: &[u8]| {
                let str_to_parse = std::str::from_utf8(out).unwrap();
                let result = u8::from_str_radix(str_to_parse, 8).ok();
                if result.is_none() {
                    if let Ok(origin_octal) = std::str::from_utf8(input) {
                        let actual_octal_tail: &str = std::str::from_utf8(&input[0..2]).unwrap();
                        let outstand_char: char = char::from_u32(input[2] as u32).unwrap();
                        show_warning!(
                            "{}",
                            translate!("tr-warning-ambiguous-octal-escape", "origin_octal" => origin_octal, "actual_octal_tail" => actual_octal_tail, "outstand_char" => outstand_char)
                        );
                    } else {
                        show_warning!("{}", translate!("tr-warning-invalid-utf8"));
                    }
                }
                result
            },
        )
        .parse(input)
    }

    fn parse_octal_two_digits(input: &[u8]) -> IResult<&[u8], u8> {
        map_opt(
            recognize(many_m_n(2, 2, one_of("01234567"))),
            |out: &[u8]| u8::from_str_radix(std::str::from_utf8(out).unwrap(), 8).ok(),
        )
        .parse(input)
    }

    fn parse_backslash(input: &[u8]) -> IResult<&[u8], u8> {
        preceded(tag("\\"), Self::single_char)
            .parse(input)
            .map(|(l, a)| {
                let c = match a {
                    b'a' => unicode_table::BEL,
                    b'b' => unicode_table::BS,
                    b'f' => unicode_table::FF,
                    b'n' => unicode_table::LF,
                    b'r' => unicode_table::CR,
                    b't' => unicode_table::HT,
                    b'v' => unicode_table::VT,
                    x => x,
                };
                (l, c)
            })
    }

    fn parse_backslash_or_char(input: &[u8]) -> IResult<&[u8], u8> {
        alt((Self::parse_octal, Self::parse_backslash, Self::single_char)).parse(input)
    }

    fn parse_backslash_or_char_with_warning(input: &[u8]) -> IResult<&[u8], u8> {
        alt((
            Self::parse_octal_with_warning,
            Self::parse_backslash,
            Self::single_char,
        ))
        .parse(input)
    }

    fn single_char(input: &[u8]) -> IResult<&[u8], u8> {
        take(1usize)(input).map(|(l, a)| (l, a[0]))
    }

    fn parse_char_range(input: &[u8]) -> IResult<&[u8], Result<Self, BadSequence>> {
        separated_pair(
            Self::parse_backslash_or_char,
            tag("-"),
            Self::parse_backslash_or_char,
        )
        .parse(input)
        .map(|(l, (a, b))| {
            (l, {
                let (start, end) = (u32::from(a), u32::from(b));

                let range = start..=end;

                if range.is_empty() {
                    Err(BadSequence::BackwardsRange { end, start })
                } else {
                    Ok(Self::CharRange(start as u8, end as u8))
                }
            })
        })
    }

    fn parse_char_star(input: &[u8]) -> IResult<&[u8], Result<Self, BadSequence>> {
        delimited(tag("["), Self::parse_backslash_or_char, tag("*]"))
            .parse(input)
            .map(|(l, a)| (l, Ok(Self::CharStar(a))))
    }

    fn parse_char_repeat(input: &[u8]) -> IResult<&[u8], Result<Self, BadSequence>> {
        delimited(
            tag("["),
            separated_pair(
                Self::parse_backslash_or_char,
                tag("*"),
                // TODO
                // Why are the opening and closing tags not sufficient?
                // Backslash check is a workaround for `check_against_gnu_tr_tests_repeat_bs_9`
                take_till(|ue| matches!(ue, b']' | b'\\')),
            ),
            tag("]"),
        )
        .parse(input)
        .map(|(l, (c, cnt_str))| {
            let s = String::from_utf8_lossy(cnt_str);
            let result = if cnt_str.starts_with(b"0") {
                match usize::from_str_radix(&s, 8) {
                    Ok(0) => Ok(Self::CharStar(c)),
                    Ok(count) => Ok(Self::CharRepeat(c, count)),
                    Err(_) => Err(BadSequence::InvalidRepeatCount(s.to_string())),
                }
            } else {
                match s.parse::<usize>() {
                    Ok(0) => Ok(Self::CharStar(c)),
                    Ok(count) => Ok(Self::CharRepeat(c, count)),
                    Err(_) => Err(BadSequence::InvalidRepeatCount(s.to_string())),
                }
            };
            (l, result)
        })
    }

    fn parse_class(input: &[u8]) -> IResult<&[u8], Result<Self, BadSequence>> {
        preceded(tag("[:"), terminated(take_until(":]"), tag(":]")))
            .parse(input)
            .map(|(l, class_name)| {
                (
                    l,
                    match class_name {
                        b"" => Err(BadSequence::MissingCharClassName),
                        b"alnum" => Ok(Self::Class(Class::Alnum)),
                        b"alpha" => Ok(Self::Class(Class::Alpha)),
                        b"blank" => Ok(Self::Class(Class::Blank)),
                        b"cntrl" => Ok(Self::Class(Class::Control)),
                        b"digit" => Ok(Self::Class(Class::Digit)),
                        b"graph" => Ok(Self::Class(Class::Graph)),
                        b"lower" => Ok(Self::Class(Class::Lower)),
                        b"print" => Ok(Self::Class(Class::Print)),
                        b"punct" => Ok(Self::Class(Class::Punct)),
                        b"space" => Ok(Self::Class(Class::Space)),
                        b"upper" => Ok(Self::Class(Class::Upper)),
                        b"xdigit" => Ok(Self::Class(Class::Xdigit)),
                        _ => Err(BadSequence::InvalidCharClass(
                            String::from_utf8_lossy(class_name).into_owned(),
                        )),
                    },
                )
            })
    }

    fn parse_char_equal(input: &[u8]) -> IResult<&[u8], Result<Self, BadSequence>> {
        preceded(
            tag("[="),
            (
                alt((
                    value(Err(()), peek(tag("=]"))),
                    map(Self::parse_backslash_or_char, Ok),
                )),
                map(terminated(take_until("=]"), tag("=]")), |v: &[u8]| {
                    if v.is_empty() { Ok(()) } else { Err(v) }
                }),
            ),
        )
        .parse(input)
        .map(|(l, (a, b))| {
            (
                l,
                match (a, b) {
                    (Err(()), _) => Err(BadSequence::MissingEquivalentClassChar),
                    (Ok(c), Ok(())) => Ok(Self::Char(c)),
                    (Ok(c), Err(v)) => Err(BadSequence::MultipleCharInEquivalence(format!(
                        "{}{}",
                        String::from_utf8_lossy(&[c]),
                        String::from_utf8_lossy(v),
                    ))),
                },
            )
        })
    }
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub trait SymbolTranslator: Sized + TranslatorModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).valid(),
        ensures result == old(self).step(current).0,
            *final(self) == old(self).step(current).1, final(self).valid(),
    ))]
    fn translate(&mut self, current: u8) -> Option<u8>;

    /// Takes two [`SymbolTranslator`]s and creates a new [`SymbolTranslator`] over both in sequence.
    ///
    /// This behaves pretty much identical to [`Iterator::chain`].
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.stage_a == self, result.stage_b == other,
    ))]
    fn chain<T>(self, other: T) -> ChainedSymbolTranslator<Self, T>
    where
        Self: Sized,
    {
        ChainedSymbolTranslator::<Self, T> {
            stage_a: self,
            stage_b: other,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct ChainedSymbolTranslator<A, B> {
    pub stage_a: A,
    pub stage_b: B,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl<A: SymbolTranslator, B: SymbolTranslator> TranslatorModel for ChainedSymbolTranslator<A, B> {
        open spec fn valid(&self) -> bool { self.stage_a.valid() && self.stage_b.valid() }
        open spec fn step(&self, current: u8) -> (Option<u8>, Self) {
            let a = self.stage_a.step(current);
            match a.0 {
                Some(byte) => {
                    let b = self.stage_b.step(byte);
                    (b.0, Self { stage_a: a.1, stage_b: b.1 })
                },
                None => (None, Self { stage_a: a.1, stage_b: self.stage_b }),
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl<A: SymbolTranslator, B: SymbolTranslator> SymbolTranslator for ChainedSymbolTranslator<A, B> {
    #[cfg_attr(verus_keep_ghost, verus_spec)]
    fn translate(&mut self, current: u8) -> Option<u8> {
        match self.stage_a.translate(current) {
            Some(c) => self.stage_b.translate(c),
            None => None,
        }
    }
}

/// Convert a set of bytes to a 256-element bitmap for O(1) lookup
#[cfg(not(verus_keep_ghost))]
fn set_to_bitmap(set: &[u8]) -> [bool; 256] {
    let mut bitmap = [false; 256];
    for &byte in set {
        bitmap[byte as usize] = true;
    }
    bitmap
}

#[derive(Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct DeleteOperation {
    pub keep_table: [bool; 256],
    /// The byte to delete, when it is the only one.
    pub single_delete: Option<u8>,
}

#[cfg(not(verus_keep_ghost))]
impl DeleteOperation {
    pub fn new(set: Vec<u8>) -> Self {
        use crate::simd::find_single_change;

        let keep_table = set_to_bitmap(&set).map(|delete| !delete);
        let single_delete = find_single_change(&keep_table, |_, &keep| !keep).map(|(b, _)| b);
        Self {
            keep_table,
            single_delete,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl TranslatorModel for DeleteOperation {
        open spec fn valid(&self) -> bool { true }
        open spec fn step(&self, current: u8) -> (Option<u8>, Self) {
            (if self.keep_table@[current as int] { Some(current) } else { None }, *self)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl SymbolTranslator for DeleteOperation {
    #[cfg_attr(verus_keep_ghost, verus_spec)]
    fn translate(&mut self, current: u8) -> Option<u8> {
        // keep if not present in the delete set
        self.keep_table[current as usize].then_some(current)
    }
}

#[cfg(not(verus_keep_ghost))]
impl ChunkProcessor for DeleteOperation {
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8] {
        use crate::simd::{process_delete, process_single_delete};

        if let Some(delete_char) = self.single_delete {
            process_single_delete(input, output, delete_char, &self.keep_table)
        } else {
            // Standard deletion
            process_delete(input, output, &self.keep_table);
            output
        }
    }
}

#[derive(Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct TranslateOperation {
    pub translation_table: [u8; 256],
    /// The byte to replace and its replacement, when it is the only one.
    pub single_change: Option<(u8, u8)>,
}

#[cfg(not(verus_keep_ghost))]
impl TranslateOperation {
    pub fn new(set1: Vec<u8>, set2: Vec<u8>) -> Result<Self, BadSequence> {
        // Initialize translation table with identity mapping
        let mut translation_table = std::array::from_fn(|i| i as u8);

        if let Some(fallback) = set2.last().copied() {
            // Apply translations from set1 to set2
            for (from, to) in set1
                .into_iter()
                .zip(set2.into_iter().chain(std::iter::repeat(fallback)))
            {
                translation_table[from as usize] = to;
            }

            Ok(Self::from_table(translation_table))
        } else if set1.is_empty() && set2.is_empty() {
            // Identity mapping for empty sets
            Ok(Self::from_table(translation_table))
        } else {
            // Raised against the solved sets rather than what was typed, so
            // there is nothing to point a caret at.
            Err(BadSequence::EmptySet2WhenNotTruncatingSet1)
        }
    }

    fn from_table(translation_table: [u8; 256]) -> Self {
        use crate::simd::find_single_change;

        let single_change = find_single_change(&translation_table, |i, &val| val != i as u8);
        Self {
            translation_table,
            single_change,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl TranslatorModel for TranslateOperation {
        open spec fn valid(&self) -> bool { true }
        open spec fn step(&self, current: u8) -> (Option<u8>, Self) {
            (Some(self.translation_table@[current as int]), *self)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl SymbolTranslator for TranslateOperation {
    #[cfg_attr(verus_keep_ghost, verus_spec)]
    fn translate(&mut self, current: u8) -> Option<u8> {
        Some(self.translation_table[current as usize])
    }
}

#[cfg(all(verus_keep_ghost, uutils_tr_translate))]
verus! {
    impl ChunkModel for TranslateOperation {
        open spec fn chunk_valid(&self) -> bool {
            match self.single_change {
                Some((source, target)) => forall|b: int| 0 <= b < 256 ==>
                    self.translation_table@[b] == if b == source as int { target } else { b as u8 },
                None => true,
            }
        }
        open spec fn chunk_output(&self, input: Seq<u8>) -> Seq<u8> {
            crate::tr_proof::table_prefix(input, self.translation_table@, input.len() as int)
        }
    }
}

#[cfg(any(not(verus_keep_ghost), uutils_tr_translate))]
#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl ChunkProcessor for TranslateOperation {
    #[cfg_attr(verus_keep_ghost, verus_spec)]
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8] {
        use crate::simd::process_single_char_replace;

        if let Some((source, target)) = self.single_change {
            // Use SIMD-optimized single character replacement
            #[cfg(verus_keep_ghost)]
            proof! { crate::proof::single_matches(input@, self.translation_table@, source, target, input@.len() as int); }
            process_single_char_replace(input, output, source, target)
        } else {
            // Standard translation using table lookup
            let mapper = crate::simd::closure_with_spec!(
                (result: u8 => ensures result == self.translation_table@[b as int],),
                |b: u8| self.translation_table[b as usize]
            );
            crate::simd::extend_mapped(output, input, mapper);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::table_map(input@, self.translation_table@, output@, input@.len() as int);
                assert(output@.take(input@.len() as int) =~= output@);
            }
            output
        }
    }
}

#[derive(Debug)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct SqueezeOperation {
    pub squeeze_table: [bool; 256],
    pub previous: Option<u8>,
}

#[cfg(not(verus_keep_ghost))]
impl SqueezeOperation {
    pub fn new(set1: Vec<u8>) -> Self {
        Self {
            squeeze_table: set_to_bitmap(&set1),
            previous: None,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl TranslatorModel for SqueezeOperation {
        open spec fn valid(&self) -> bool { true }
        open spec fn step(&self, current: u8) -> (Option<u8>, Self) {
            (crate::tr_proof::squeeze_byte(self.previous, current, self.squeeze_table@),
                Self { squeeze_table: self.squeeze_table, previous: Some(current) })
        }
    }
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl SymbolTranslator for SqueezeOperation {
    #[cfg_attr(verus_keep_ghost, verus_spec)]
    fn translate(&mut self, current: u8) -> Option<u8> {
        let next = if self.squeeze_table[current as usize] {
            match self.previous {
                Some(v) if v == current => None,
                _ => Some(current),
            }
        } else {
            Some(current)
        };
        self.previous = Some(current);
        next
    }
}

#[cfg(any(
    not(verus_keep_ghost),
    uutils_tr_squeeze,
    uutils_tr_delete_and_squeeze,
    uutils_tr_translate_and_squeeze
))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires translator.valid(), io_trusted::readable(old(input)), io_trusted::writable(old(output)),
    ensures result is Ok,
        io_trusted::remaining(final(input)).len() == 0,
        io_trusted::written(final(output)) == io_trusted::written(old(output)) +
            stream_proof::run(translator, io_trusted::remaining(old(input)),
                io_trusted::remaining(old(input)).len() as int).0,
))]
pub fn translate_input<T, R, W>(input: &mut R, output: &mut W, mut translator: T) -> UResult<()>
where
    T: SymbolTranslator,
    R: BufRead,
    W: Write,
{
    const BUFFER_SIZE: usize = 32768; // Large buffer for better throughput
    let mut buf = [0; BUFFER_SIZE];
    let mut output_buf = Vec::with_capacity(BUFFER_SIZE);

    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = translator;
        let ghost bytes = io_trusted::remaining(input);
        let ghost written = io_trusted::written(output);
        let ghost offset: int = 0;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= offset <= bytes.len(), translator.valid(),
            io_trusted::readable(input), io_trusted::writable(output),
            io_trusted::remaining(input) == bytes.skip(offset),
            io_trusted::written(output) == written + stream_proof::run(initial, bytes, offset).0,
            translator == stream_proof::run(initial, bytes, offset).1,
        ensures
            io_trusted::remaining(input).len() == 0,
            offset == bytes.len(),
            io_trusted::written(output) == written + stream_proof::run(initial, bytes, bytes.len() as int).0,
        decreases bytes.len() - offset,
    ))]
    loop {
        let length = match io_trusted::read(input, &mut buf[..]) {
            Ok(0) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(io_trusted::remaining(input).len() == 0);
                    assert(offset == bytes.len());
                }
                break; // EOF reached
            }
            Ok(len) => len,
            #[cfg(not(verus_keep_ghost))]
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            #[cfg(not(verus_keep_ghost))]
            Err(e) => return Err(e.map_err_context(|| translate!("tr-error-read-error"))),
            #[cfg(verus_keep_ghost)]
            Err(e) => return Err(e),
        };

        // Process the buffer and collect translated chars to output
        output_buf.clear();
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = translator; }
        #[cfg_attr(verus_keep_ghost, verus_spec(iter =>
            invariant
                length <= BUFFER_SIZE,
                translator.valid(),
                translator == stream_proof::run(start, buf@.take(length as int), iter.index()).1,
                output_buf@ == stream_proof::run(start, buf@.take(length as int), iter.index()).0,
        ))]
        for current in &buf[..length] {
            let byte = *current;
            if let Some(translated) = translator.translate(byte) {
                output_buf.push(translated);
            }
        }

        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bytes.take(offset).take(offset) =~= bytes.take(offset));
            assert(bytes.take(offset + length).take(offset + length) =~= bytes.take(offset + length));
            assert(buf@.take(length as int) == bytes.subrange(offset, offset + length));
            assert(bytes.take(offset) + buf@.take(length as int) =~= bytes.take(offset + length));
            stream_proof::run_append(initial, bytes.take(offset), buf@.take(length as int), length as int);
            stream_proof::prefix_independent(initial, bytes, bytes.take(offset), offset);
            stream_proof::prefix_independent(initial, bytes, bytes.take(offset + length), offset + length);
        }

        if !output_buf.is_empty() {
            crate::simd::write_output(output, &output_buf)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { offset = offset + length; }
    }

    #[cfg(verus_keep_ghost)]
    proof! {
        assert(io_trusted::remaining(input).len() == 0);
        assert(offset == bytes.len());
        assert(io_trusted::written(output) == written + stream_proof::run(initial, bytes, bytes.len() as int).0);
    }
    Ok(())
}

/// Platform-specific flush operation
#[inline]
#[cfg(not(verus_keep_ghost))]
pub fn flush_output<W: Write>(output: &mut W) -> UResult<()> {
    #[cfg(not(windows))]
    return output
        .flush()
        .map_err_context(|| translate!("tr-error-write-error"));

    #[cfg(windows)]
    match output.flush() {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::BrokenPipe => {
            std::process::exit(13);
        }
        Err(err) => Err(err.map_err_context(|| translate!("tr-error-write-error"))),
    }
}
