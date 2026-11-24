// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use clap::{Arg, ArgAction, Command};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use num_traits::Zero;
use std::ffi::{OsStr, OsString};
use std::io::{BufWriter, Write, stdout};
use uucore::error::{FromIo, UResult};
use uucore::extendedbigdecimal::ExtendedBigDecimal;
use uucore::format::num_format::FloatVariant;
use uucore::format::{Format, num_format};
use uucore::{fast_inc::fast_inc, format_usage};
use vstd::prelude::*;
#[cfg(not(uutils_seq_all))]
mod diagnostics;
#[cfg(not(uutils_seq_all))]
mod error;
#[cfg(fuzzing)]
pub mod number;
#[cfg(not(fuzzing))]
mod number;
#[cfg(not(uutils_seq_all))]
mod numberparse;
#[cfg(not(uutils_seq_all))]
use crate::original::error::SeqError;
use crate::original::number::PreciseNumber;
#[cfg(all(unix, not(target_os = "fuchsia")))]
use uucore::signals;
use uucore::translate;
#[path = "runtime/stdio.rs"]
mod io_trusted;
use crate::trusted as format_trusted;
const OPT_SEPARATOR: &str = "separator";
const OPT_TERMINATOR: &str = "terminator";
const OPT_EQUAL_WIDTH: &str = "equal-width";
pub(crate) const OPT_FORMAT: &str = "format";
const ARG_NUMBERS: &str = "numbers";
#[derive(Clone)]
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub(crate) struct SeqOptions<'a> {
    separator: OsString,
    terminator: OsString,
    equal_width: bool,
    format: Option<&'a str>,
}
#[doc = " A range of floats."]
#[doc = ""]
#[doc = " The elements are (first, increment, last)."]
type RangeFloat = (ExtendedBigDecimal, ExtendedBigDecimal, ExtendedBigDecimal);
#[doc = " Turn short args with attached value, for example \"-s,\", into two args \"-s\" and \",\" to make"]
#[doc = " them work with clap."]
#[cfg(not(uutils_seq_all))]
fn split_short_args_with_value(args: impl uucore::Args) -> impl uucore::Args {
    let mut v: Vec<OsString> = Vec::new();
    for arg in args {
        let bytes = arg.as_encoded_bytes();
        if bytes.len() > 2
            && (bytes.starts_with(b"-f") || bytes.starts_with(b"-s") || bytes.starts_with(b"-t"))
        {
            let (short_arg, value) = bytes.split_at(2);
            v.push(unsafe { OsString::from_encoded_bytes_unchecked(short_arg.to_vec()) });
            v.push(unsafe { OsString::from_encoded_bytes_unchecked(value.to_vec()) });
        } else {
            v.push(arg);
        }
    }
    v.into_iter()
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn select_precision(
    first: &PreciseNumber,
    increment: &PreciseNumber,
    last: &PreciseNumber,
) -> Option<usize> {
    match (
        first.num_fractional_digits,
        increment.num_fractional_digits,
        last.num_fractional_digits,
    ) {
        (Some(0), Some(0), Some(0)) => Some(0),
        (Some(f), Some(i), Some(_)) => Some(f.max(i)),
        _ => None,
    }
}
#[cfg(not(uutils_seq_all))]
#[uucore::main]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let raw_args: Vec<OsString> = args.collect();
    let diag_args = uucore::diagnostics::capture(&raw_args);
    let matches = uucore::clap_localization::handle_clap_result(
        uu_app(),
        split_short_args_with_value(raw_args.into_iter()),
    )?;
    let numbers_option = matches.get_many::<String>(ARG_NUMBERS);
    if numbers_option.is_none() {
        return Err(SeqError::NoArguments.into());
    }
    let numbers = numbers_option.unwrap().collect::<Vec<_>>();
    let options = SeqOptions {
        separator: matches
            .get_one::<OsString>(OPT_SEPARATOR)
            .cloned()
            .unwrap_or_else(|| OsString::from("\n")),
        terminator: matches
            .get_one::<OsString>(OPT_TERMINATOR)
            .cloned()
            .unwrap_or_else(|| OsString::from("\n")),
        equal_width: matches.get_flag(OPT_EQUAL_WIDTH),
        format: matches.get_one::<String>(OPT_FORMAT).map(String::as_str),
    };
    if options.equal_width && options.format.is_some() {
        return Err(SeqError::FormatAndEqualWidth.into());
    }
    let first = if numbers.len() > 1 {
        numbers[0]
            .parse()
            .map_err(|e| SeqError::ParseError(numbers[0].to_owned(), e))?
    } else {
        PreciseNumber::one()
    };
    let increment = if numbers.len() > 2 {
        numbers[1]
            .parse()
            .map_err(|e| SeqError::ParseError(numbers[1].to_owned(), e))?
    } else {
        PreciseNumber::one()
    };
    if increment.is_zero() {
        return Err(SeqError::ZeroIncrement(numbers[1].to_owned()).into());
    }
    let last: PreciseNumber = {
        let n: usize = numbers.len();
        numbers[n - 1]
            .parse()
            .map_err(|e| SeqError::ParseError(numbers[n - 1].to_owned(), e))?
    };
    let (format, padding, fast_allowed) = if let Some(str) = options.format {
        let format =
            Format::<num_format::Float, &ExtendedBigDecimal>::parse(str).map_err(|error| {
                uucore::diagnostics::error_after_report(
                    diag_args.as_deref(),
                    error,
                    |args, error| diagnostics::render(args, str, error),
                )
            })?;
        (format, 0, false)
    } else {
        let precision = select_precision(&first, &increment, &last);
        let padding = if options.equal_width {
            let precision_value = precision.unwrap_or(0);
            first
                .num_integral_digits
                .max(last.num_integral_digits)
                .saturating_add(if precision_value > 0 {
                    precision_value.saturating_add(1)
                } else {
                    0
                })
        } else {
            0
        };
        let formatter = match precision {
            Some(precision) => num_format::Float {
                variant: FloatVariant::Decimal,
                width: padding,
                alignment: num_format::NumberAlignment::RightZero,
                precision: Some(precision),
                ..Default::default()
            },
            None => num_format::Float {
                variant: FloatVariant::Shortest,
                ..Default::default()
            },
        };
        (
            Format::from_formatter(formatter),
            padding,
            precision == Some(0),
        )
    };
    let result = print_seq(
        (first.number, increment.number, last.number),
        &options.separator,
        &options.terminator,
        &format,
        fast_allowed,
        padding,
        BufWriter::new(stdout().lock()),
    );
    match result {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::BrokenPipe => {
            let err = err.map_err_context(|| "write error".into());
            uucore::show_error!("{err}");
            #[cfg(all(unix, not(target_os = "fuchsia")))]
            if signals::sigpipe_was_ignored() {
                uucore::error::set_exit_code(1);
            }
            Ok(())
        }
        Err(err) => Err(err.map_err_context(|| "write error".into())),
    }
}
#[cfg(not(uutils_seq_all))]
pub fn uu_app() -> Command {
    Command::new("seq")
        .trailing_var_arg(true)
        .infer_long_args(true)
        .version(uucore::crate_version!())
        .help_template(uucore::localized_help_template(uucore::util_name()))
        .about(translate!("seq-about"))
        .override_usage(format_usage(&translate!("seq-usage")))
        .arg(
            Arg::new(OPT_SEPARATOR)
                .short('s')
                .long("separator")
                .help(translate!("seq-help-separator"))
                .value_parser(clap::value_parser!(OsString)),
        )
        .arg(
            Arg::new(OPT_TERMINATOR)
                .short('t')
                .long("terminator")
                .help(translate!("seq-help-terminator"))
                .value_parser(clap::value_parser!(OsString)),
        )
        .arg(
            Arg::new(OPT_EQUAL_WIDTH)
                .short('w')
                .long("equal-width")
                .help(translate!("seq-help-equal-width"))
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(OPT_FORMAT)
                .short('f')
                .long(OPT_FORMAT)
                .help(translate!("seq-help-format")),
        )
        .arg(
            Arg::new(ARG_NUMBERS)
                .allow_hyphen_values(true)
                .action(ArgAction::Append)
                .num_args(1..=3),
        )
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub(crate) fn execute(
    first: PreciseNumber,
    increment: PreciseNumber,
    last: PreciseNumber,
    options: &SeqOptions<'_>,
    stdout: impl Write,
) -> std::io::Result<()> {
    let (format, padding, fast_allowed) = if let Some(str) = options.format {
        let format = format_trusted::parse(str)?;
        (format, 0, false)
    } else {
        let precision = select_precision(&first, &increment, &last);
        let padding = if options.equal_width {
            let precision_value = precision.unwrap_or(0);
            first
                .num_integral_digits
                .max(last.num_integral_digits)
                .saturating_add(if precision_value > 0 {
                    precision_value.saturating_add(1)
                } else {
                    0
                })
        } else {
            0
        };
        let formatter = match precision {
            Some(precision) => format_trusted::decimal_formatter(padding, precision),
            None => format_trusted::shortest_formatter(),
        };
        (
            Format::from_formatter(formatter),
            padding,
            precision == Some(0),
        )
    };
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result = print_seq(
            (first.number, increment.number, last.number),
            &options.separator,
            &options.terminator,
            &format,
            fast_allowed,
            padding,
            stdout,
        );
        io_result
    }
}
#[doc = " Integer print, default format, positive increment: fast code path"]
#[doc = " that avoids reformatting digit at all iterations."]
#[cfg_attr(verus_keep_ghost, verus_verify)]
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
fn fast_print_seq(
    mut stdout: impl Write,
    first: &BigUint,
    increment: u64,
    last: &BigUint,
    separator: &OsStr,
    terminator: &OsStr,
    padding: usize,
) -> std::io::Result<()> {
    if last < first {
        return Ok(());
    }
    let loop_cnt = ((last - first) / increment).to_u64().unwrap_or(u64::MAX);
    let first_str = first.to_string();
    let last_length = last.to_string().len();
    let size = last_length.max(padding) + separator.len();
    let mut buf = vec![b'0'; size];
    let buf = buf.as_mut_slice();
    let num_end = buf.len() - separator.len();
    let mut start = num_end - first_str.len();
    buf[start..num_end].copy_from_slice(first_str.as_bytes());
    buf[num_end..].copy_from_slice(separator.as_encoded_bytes());
    start = start.min(num_end - padding);
    let inc_str = increment.to_string();
    let inc_str = inc_str.as_bytes();
    for _ in 0..loop_cnt {
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = crate::trusted_common::io::write_state(&mut stdout, &buf[start..]);
            io_result
        }?;
        fast_inc(buf, &mut start, num_end, inc_str);
    }
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result = crate::trusted_common::io::write_state(&mut stdout, &buf[start..num_end]);
        io_result
    }?;
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result =
            crate::trusted_common::io::write_state(&mut stdout, terminator.as_encoded_bytes());
        io_result
    }?;
    format_trusted::flush(&mut stdout)?;
    Ok(())
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn done_printing<T: Zero + PartialOrd>(next: &T, increment: &T, last: &T) -> bool {
    if increment >= &T::zero() {
        next > last
    } else {
        next < last
    }
}
#[doc = " Arbitrary precision decimal number code path (\"slow\" path)"]
#[cfg_attr(verus_keep_ghost, verus_verify)]
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
fn print_seq(
    range: RangeFloat,
    separator: &OsStr,
    terminator: &OsStr,
    format: &Format<num_format::Float, &ExtendedBigDecimal>,
    fast_allowed: bool,
    padding: usize,
    mut stdout: impl Write,
) -> std::io::Result<()> {
    let (first, increment, last) = range;
    if fast_allowed {
        let (first_bui, increment_u64, last_bui) = (
            first.to_biguint(),
            increment.to_biguint().and_then(|x| x.to_u64()),
            last.to_biguint(),
        );
        if let (Some(first_bui), Some(increment_u64), Some(last_bui)) =
            (first_bui, increment_u64, last_bui)
        {
            return {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = fast_print_seq(
                    stdout,
                    &first_bui,
                    increment_u64,
                    &last_bui,
                    separator,
                    terminator,
                    padding,
                );
                io_result
            };
        }
    }
    let mut value = first;
    let mut is_first_iteration = true;
    while !done_printing(&value, &increment, &last) {
        if !is_first_iteration {
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = crate::trusted_common::io::write_state(
                    &mut stdout,
                    separator.as_encoded_bytes(),
                );
                io_result
            }?;
        }
        let rendered = format_trusted::render(format, &value)?;
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = crate::trusted_common::io::write_state(&mut stdout, &rendered);
            io_result
        }?;
        value = value + increment.clone();
        is_first_iteration = false;
    }
    if !is_first_iteration {
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result =
                crate::trusted_common::io::write_state(&mut stdout, terminator.as_encoded_bytes());
            io_result
        }?;
    }
    format_trusted::flush(&mut stdout)?;
    Ok(())
}
