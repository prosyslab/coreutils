// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use clap::{Arg, ArgAction, Command};
use std::ffi::{OsStr, OsString};
use std::io::{Write, stdout};
#[cfg(unix)]
use uucore::display::print_verbatim;
use uucore::error::{UResult, UUsageError};
use uucore::format_usage;
use uucore::line_ending::LineEnding;
use uucore::translate;
use vstd::prelude::*;
#[path = "runtime/stdio.rs"]
mod io_trusted;
use crate::trusted as library;
mod options {
    pub const ZERO: &str = "zero";
    pub const DIR: &str = "dir";
}
#[cfg(not(windows))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn is_sep(b: u8) -> bool {
    std::path::is_separator(b as char)
}
#[cfg(windows)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn is_sep(b: u8) -> bool {
    b == b'/' || b == b'\\'
}
#[cfg(not(windows))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn root_prefix_len(_path: &OsStr) -> usize {
    0
}
#[cfg(windows)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn root_prefix_len(path: &OsStr) -> usize {
    use std::path::{Component, Path};
    let bytes = path.as_encoded_bytes();
    let Some(Component::Prefix(p)) = Path::new(path).components().next() else {
        return 0;
    };
    let mut len = p.as_os_str().len();
    if len > 0 && len < bytes.len() && is_sep(bytes[len]) {
        len += 1;
    }
    len
}
#[doc = " Perform dirname as pure string manipulation per POSIX/GNU behavior."]
#[doc = ""]
#[doc = " dirname should NOT normalize paths. It does simple string manipulation:"]
#[doc = " 1. Strip trailing slashes (unless path is all slashes)"]
#[doc = " 2. If ends with `/.` (possibly `//.` or `///.`), strip the `/+.` pattern"]
#[doc = " 3. Otherwise, remove everything after the last `/`"]
#[doc = " 4. If no `/` found, return `.`"]
#[doc = " 5. Strip trailing slashes from result (unless result would be empty)"]
#[doc = ""]
#[doc = " Examples:"]
#[doc = " - `foo/.` → `foo`"]
#[doc = " - `foo/./bar` → `foo/.`"]
#[doc = " - `foo/bar` → `foo`"]
#[doc = " - `a/b/c` → `a/b`"]
#[doc = " - `C:\\foo\\bar` → `C:\\foo` (Windows)"]
#[doc = " - `C:\\foo` → `C:\\` (Windows)"]
#[doc = " - `\\\\server\\share\\foo` → `\\\\server\\share\\` (Windows)"]
#[doc = ""]
#[doc = " Per POSIX.1-2017 dirname specification and GNU coreutils manual:"]
#[doc = " - POSIX: <https://pubs.opengroup.org/onlinepubs/9699919799/utilities/dirname.html>"]
#[doc = " - GNU: <https://www.gnu.org/software/coreutils/manual/html_node/dirname-invocation.html>"]
#[doc = ""]
#[doc = " See issue #8910 and similar fix in basename (#8373, commit c5268a897)."]
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn dirname_string_manipulation(path: &OsStr) -> &[u8] {
    let path_bytes = uucore::os_str_as_bytes(path).unwrap_or(&[]);
    if path_bytes.is_empty() {
        return b".";
    }
    let mut bytes = path_bytes;
    let root_len = root_prefix_len(path);
    if library::all(&bytes[root_len..], is_sep) {
        return &bytes[..root_len.max(1)];
    }
    while bytes.len() > root_len.max(1) && is_sep(bytes[bytes.len() - 1]) {
        bytes = &bytes[..bytes.len() - 1];
    }
    if bytes.last() == Some(&b'.') && bytes.len() >= 2 && is_sep(bytes[bytes.len() - 2]) {
        let dot_pos = bytes.len() - 1;
        let mut slash_start = dot_pos - 1;
        while slash_start > 0 && is_sep(bytes[slash_start - 1]) {
            slash_start -= 1;
        }
        if slash_start == 0 {
            return if is_sep(path_bytes[0]) {
                &path_bytes[..1]
            } else {
                b"."
            };
        }
        if slash_start < root_len {
            return &path_bytes[..root_len];
        }
        return &bytes[..slash_start];
    }
    if let Some(last_slash_pos) = library::rposition(bytes, is_sep) {
        let mut result = &bytes[..last_slash_pos];
        while result.len() > 1 && is_sep(result[result.len() - 1]) {
            result = &result[..result.len() - 1];
        }
        if result.is_empty() {
            return &bytes[..1];
        }
        if result.len() < root_len {
            return &bytes[..root_len];
        }
        return result;
    }
    if root_len > 0 {
        return &bytes[..root_len];
    }
    b"."
}
#[cfg(not(uutils_dirname_all))]
#[uucore::main(no_signals)]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let matches = uucore::clap_localization::handle_clap_result(uu_app(), args)?;
    let line_ending = LineEnding::from_zero_flag(matches.get_flag(options::ZERO));
    let dirnames: Vec<OsString> = matches
        .get_many::<OsString>(options::DIR)
        .ok_or_else(|| UUsageError::new(1, translate!("dirname-missing-operand")))?
        .cloned()
        .collect();
    for path in &dirnames {
        let result = dirname_string_manipulation(path.as_os_str());
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            let result_os = OsStr::from_bytes(result);
            print_verbatim(result_os)?;
        }
        #[cfg(not(unix))]
        {
            if let Ok(s) = std::str::from_utf8(result) {
                write!(stdout(), "{s}")?;
            } else {
                write!(stdout(), ".")?;
            }
        }
        write!(stdout(), "{line_ending}")?;
    }
    Ok(())
}
#[cfg(not(uutils_dirname_all))]
pub fn uu_app() -> Command {
    Command::new("dirname")
        .about(translate!("dirname-about"))
        .version(uucore::crate_version!())
        .help_template(uucore::localized_help_template(uucore::util_name()))
        .override_usage(format_usage(&translate!("dirname-usage")))
        .args_override_self(true)
        .infer_long_args(true)
        .after_help(translate!("dirname-after-help"))
        .arg(
            Arg::new(options::ZERO)
                .long(options::ZERO)
                .short('z')
                .help(translate!("dirname-zero-help"))
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::DIR)
                .hide(true)
                .action(ArgAction::Append)
                .value_hint(clap::ValueHint::AnyPath)
                .value_parser(clap::value_parser!(OsString)),
        )
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub(crate) fn write_name<W: Write>(
    path: &OsStr,
    ending: u8,
    output: &mut W,
) -> std::io::Result<()> {
    let result = dirname_string_manipulation(path);
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result = crate::trusted_common::io::write_state(output, result);
        io_result
    }?;
    {
        # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
        let io_result = crate::trusted_common::io::write_state(output, &[ending]);
        io_result
    }
}
