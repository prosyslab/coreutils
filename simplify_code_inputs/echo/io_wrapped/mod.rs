// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use clap::builder::ValueParser;
use clap::{Arg, ArgAction, Command};
use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{StdoutLock, Write, stdout};
#[cfg(not(verus_keep_ghost))]
use uucore::error::UResult;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
type UResult<T> = std::io::Result<T>;
use uucore::format::{EscapeSet, FormatChar, OctalParsing, parse_escape_only};
use uucore::translate;
use uucore::{crate_version, format_usage, os_str_as_bytes};
#[path = "runtime/stdio.rs"]
mod io_trusted;
use crate::trusted as format_trusted;
use crate::trusted as library;
mod options {
    pub const STRING: &str = "STRING";
    pub const NO_NEWLINE: &str = "no_newline";
    pub const ENABLE_BACKSLASH_ESCAPE: &str = "enable_backslash_escape";
    pub const DISABLE_BACKSLASH_ESCAPE: &str = "disable_backslash_escape";
}
#[doc = " Options for the echo command."]
#[derive(Debug, Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub(crate) struct Options {
    #[doc = " Whether the output should have a trailing newline."]
    #[doc = ""]
    #[doc = " True by default. `-n` disables it."]
    pub trailing_newline: bool,
    #[doc = " Whether given string literals should be parsed for"]
    #[doc = " escape characters."]
    #[doc = ""]
    #[doc = " False by default, can be enabled with `-e`. Always true if"]
    #[doc = " `POSIXLY_CORRECT` (cannot be disabled with `-E`)."]
    pub escape: bool,
}
#[cfg(not(uutils_echo_all))]
impl Default for Options {
    fn default() -> Self {
        Self {
            trailing_newline: true,
            escape: false,
        }
    }
}
#[cfg(not(uutils_echo_all))]
impl Options {
    fn posixly_correct_default() -> Self {
        Self {
            trailing_newline: true,
            escape: true,
        }
    }
}
#[doc = " Checks if an argument is a valid echo flag, and if"]
#[doc = " it is records the changes in [`Options`]."]
#[cfg(not(uutils_echo_all))]
fn is_flag(arg: &OsStr, options: &mut Options) -> bool {
    let arg = arg.as_encoded_bytes();
    if arg.first() != Some(&b'-') || arg == b"-" {
        return false;
    }
    let mut options_: Options = *options;
    for c in &arg[1..] {
        match c {
            b'e' => options_.escape = true,
            b'E' => options_.escape = false,
            b'n' => options_.trailing_newline = false,
            _ => return false,
        }
    }
    *options = options_;
    true
}
#[doc = " Processes command line arguments, separating flags from normal arguments."]
#[doc = ""]
#[doc = " # Returns"]
#[doc = ""]
#[doc = " - Vector of non-flag arguments."]
#[doc = " - [`Options`], describing how the arguments should be interpreted."]
#[cfg(not(uutils_echo_all))]
fn filter_flags(args: impl Iterator<Item = OsString>) -> (impl Iterator<Item = OsString>, Options) {
    let mut options = Options::default();
    let mut args = args.peekable();
    while let Some(arg) = args.peek() {
        if is_flag(arg, &mut options) {
            args.next();
        } else {
            break;
        }
    }
    (args, options)
}
#[cfg(not(uutils_echo_all))]
#[uucore::main]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let mut args = args.skip(1).peekable();
    let is_posixly_correct = env::var_os("POSIXLY_CORRECT").is_some();
    let (args, options): (Box<dyn Iterator<Item = OsString>>, Options) = if is_posixly_correct {
        if args.peek().is_some_and(|arg| arg == "-n") {
            let (args, _) = filter_flags(args);
            (
                Box::new(args),
                Options {
                    trailing_newline: false,
                    ..Options::posixly_correct_default()
                },
            )
        } else {
            (Box::new(args), Options::posixly_correct_default())
        }
    } else if let Some(first_arg) = args.next() {
        if first_arg == "--help" && args.peek().is_none() {
            uu_app().print_help()?;
            return Ok(());
        } else if first_arg == "--version" && args.peek().is_none() {
            writeln!(stdout(), "echo {}", crate_version!())?;
            return Ok(());
        }
        let (args, options) = filter_flags(std::iter::once(first_arg).chain(args));
        (Box::new(args), options)
    } else {
        (Box::new(args), Options::default())
    };
    execute(&mut stdout().lock(), args, options)?;
    Ok(())
}
#[cfg(not(uutils_echo_all))]
pub fn uu_app() -> Command {
    Command::new("echo")
        .trailing_var_arg(true)
        .allow_hyphen_values(true)
        .version(crate_version!())
        .about(translate!("echo-about"))
        .after_help(translate!("echo-after-help"))
        .override_usage(format_usage(&translate!("echo-usage")))
        .help_template(uucore::localized_help_template("echo"))
        .arg(
            Arg::new(options::NO_NEWLINE)
                .short('n')
                .help(translate!("echo-help-no-newline"))
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::ENABLE_BACKSLASH_ESCAPE)
                .short('e')
                .help(translate!("echo-help-enable-escapes"))
                .action(ArgAction::SetTrue)
                .overrides_with(options::DISABLE_BACKSLASH_ESCAPE),
        )
        .arg(
            Arg::new(options::DISABLE_BACKSLASH_ESCAPE)
                .short('E')
                .help(translate!("echo-help-disable-escapes"))
                .action(ArgAction::SetTrue)
                .overrides_with(options::ENABLE_BACKSLASH_ESCAPE),
        )
        .arg(
            Arg::new(options::STRING)
                .action(ArgAction::Append)
                .value_parser(ValueParser::os_string()),
        )
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub(crate) fn execute<W: Write>(
    stdout: &mut W,
    args: impl Iterator<Item = OsString>,
    options: Options,
) -> UResult<()> {
    for (i, arg) in format_trusted::enumerate(args) {
        let bytes = library::os_bytes(&arg)?;
        if i > 0 {
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = crate::trusted_common::io::write_state(stdout, b" ");
                io_result
            }?;
        }
        if options.escape {
            for item in format_trusted::escapes(
                bytes,
                format_trusted::three_digits(),
                format_trusted::escape_set(),
            ) {
                let (rendered, stop) = format_trusted::render_escape(&item)?;
                {
                    # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                    let io_result = crate::trusted_common::io::write_state(stdout, &rendered);
                    io_result
                }?;
                if stop {
                    return Ok(());
                }
            }
        } else {
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = crate::trusted_common::io::write_state(stdout, bytes);
                io_result
            }?;
        }
    }
    if options.trailing_newline {
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = crate::trusted_common::io::write_state(stdout, b"\n");
            io_result
        }?;
    }
    Ok(())
}
