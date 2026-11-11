// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

// spell-checker:ignore (ToDO) fullname

use clap::builder::ValueParser;
use clap::{Arg, ArgAction, Command};
use std::ffi::OsString;
use std::io::{Write, stdout};
use std::path::{PathBuf, is_separator};
use uucore::display::Quotable;
#[cfg(not(verus_keep_ghost))]
use uucore::error::UResult;
use uucore::error::UUsageError;
#[cfg(verus_keep_ghost)]
type UResult<T> = std::io::Result<T>;
use uucore::format_usage;
use uucore::line_ending::LineEnding;

use uucore::translate;

#[path = "../../../../verification_runtime/stdio.rs"]
mod io_trusted;
#[path = "../../../../verification_runtime/codec_library.rs"]
mod library;

pub mod options {
    pub static MULTIPLE: &str = "multiple";
    pub static NAME: &str = "name";
    pub static SUFFIX: &str = "suffix";
    pub static ZERO: &str = "zero";
}

#[cfg(not(uutils_basename_all))]
#[uucore::main(no_signals)]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    //
    // Argument parsing
    //
    let matches = uucore::clap_localization::handle_clap_result(uu_app(), args)?;

    let line_ending = LineEnding::from_zero_flag(matches.get_flag(options::ZERO));

    // todo: use .required(true) of clap and sed GnuTests to provide better error message
    let mut name_args = matches
        .get_many::<OsString>(options::NAME)
        .ok_or_else(|| UUsageError::new(1, translate!("basename-error-missing-operand")))?
        .collect::<Vec<_>>();
    let multiple_paths = matches.get_one::<OsString>(options::SUFFIX).is_some()
        || matches.get_flag(options::MULTIPLE);
    let suffix = if multiple_paths {
        matches
            .get_one::<OsString>(options::SUFFIX)
            .cloned()
            .unwrap_or_default()
    } else {
        // "simple format"
        match name_args.len() {
            0 => panic!("already checked"),
            1 => OsString::default(),
            2 => name_args.pop().unwrap().clone(),
            _ => {
                return Err(UUsageError::new(
                    1,
                    translate!("basename-error-extra-operand",
                               "operand" => name_args[2].quote()),
                ));
            }
        }
    };

    //
    // Main Program Processing
    //

    for path in name_args {
        let mut out = stdout();
        out.write_all(&basename(path, &suffix)?)?;
        write!(out, "{line_ending}")?;
    }

    Ok(())
}

#[cfg(not(uutils_basename_all))]
pub fn uu_app() -> Command {
    Command::new("basename")
        .version(uucore::crate_version!())
        .help_template(uucore::localized_help_template("basename"))
        .about(translate!("basename-about"))
        .override_usage(format_usage(&translate!("basename-usage")))
        .infer_long_args(true)
        .arg(
            Arg::new(options::MULTIPLE)
                .short('a')
                .long(options::MULTIPLE)
                .help(translate!("basename-help-multiple"))
                .action(ArgAction::SetTrue)
                .overrides_with(options::MULTIPLE),
        )
        .arg(
            Arg::new(options::NAME)
                .action(ArgAction::Append)
                .value_parser(ValueParser::os_string())
                .value_hint(clap::ValueHint::AnyPath)
                .hide(true)
                .trailing_var_arg(true),
        )
        .arg(
            Arg::new(options::SUFFIX)
                .short('s')
                .long(options::SUFFIX)
                .value_name("SUFFIX")
                .value_parser(ValueParser::os_string())
                .help(translate!("basename-help-suffix"))
                .overrides_with(options::SUFFIX),
        )
        .arg(
            Arg::new(options::ZERO)
                .short('z')
                .long(options::ZERO)
                .help(translate!("basename-help-zero"))
                .action(ArgAction::SetTrue)
                .overrides_with(options::ZERO),
        )
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) fn write_name<W: Write>(path: &OsString, suffix: &OsString, ending: u8, output: &mut W) -> UResult<()> {
    io_trusted::write_all(output, &basename(path, suffix)?)?;
    io_trusted::write_all(output, &[ending])?;
    Ok(())
}

// We return a Vec<u8>. Returning a seemingly more proper `OsString` would
// require back and forth conversions as we need a &[u8] for printing anyway.
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn basename(fullname: &OsString, suffix: &OsString) -> UResult<Vec<u8>> {
    let fullname_bytes = library::os_bytes(fullname)?;

    // Path::components() normalizes a trailing `.` away. Inspect a trimmed view
    // first so `foo/./` yields `.`, while using the original path below keeps
    // platform-specific root paths intact.
    let mut path_end = fullname_bytes;
    while path_end
        .last()
        .is_some_and(|byte_ref| { let byte = *byte_ref; is_separator(byte as char) })
    {
        path_end = &path_end[..path_end.len() - 1];
    }
    if path_end.len() > 1
        && path_end.last() == Some(&b'.')
        && is_separator(path_end[path_end.len() - 2] as char)
    {
        return Ok(b".".into());
    }

    // Convert to path buffer and get last path component
    let pb = library::path_buf(fullname);

    pb.components().next_back().map_or(Ok([].into()), |c| {
        let name = c.as_os_str();
        let name_bytes = library::os_bytes(name)?;
        if name == suffix {
            Ok(name_bytes.into())
        } else {
            let suffix_bytes = library::os_bytes(suffix)?;
            Ok(io_trusted::strip_suffix(name_bytes, suffix_bytes)
                .unwrap_or(name_bytes)
                .into())
        }
    })
}
