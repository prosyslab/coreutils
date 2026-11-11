// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

mod buffer_hint;
mod check;
mod chunks;
mod custom_str_cmp;
mod diagnostics;
mod ext_sort;
mod merge;
mod numeric_str_cmp;
mod tmp_dir;
use crate::buffer_hint::automatic_buffer_size;
use crate::proof::unwind::Comparator as UnwindComparator;
use crate::tmp_dir::TmpDirWrapper;
use bigdecimal::BigDecimal;
use chunks::LineData;
use clap::builder::ValueParser;
use clap::{Arg, ArgAction, ArgMatches, Command};
use custom_str_cmp::{custom_str_cmp, is_blank};
use ext_sort::ext_sort;
use foldhash::fast::FoldHasher;
use foldhash::{HashMap, SharedSeed};
use numeric_str_cmp::{NumInfo, NumInfoParseSettings, human_numeric_str_cmp, numeric_str_cmp};
use rand::{RngExt as _, rng};
#[cfg(not(target_os = "wasi"))]
use rayon::slice::ParallelSliceMut;
use std::cmp::Ordering;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{File, OpenOptions};
use std::hash::{Hash, Hasher};
use std::io::{BufRead, BufReader, BufWriter, Read, Write, stdin, stdout};
use std::num::IntErrorKind;
use std::ops::Range;
use std::path::Path;
use std::path::PathBuf;
use std::str::Utf8Error;
use std::sync::OnceLock;
use uucore::diagnostics::OptionValue;
use uucore::display::Quotable;
use uucore::error::{FromIo, strip_errno};
use uucore::error::{UError, UResult, USimpleError, UUsageError};
use uucore::extendedbigdecimal::ExtendedBigDecimal;
#[cfg(feature = "i18n-collator")]
use uucore::i18n::collator::{compute_sort_key_utf8, locale_cmp};
use uucore::i18n::datetime::get_locale_months;
use uucore::i18n::decimal::locale_decimal_separator;
use uucore::line_ending::LineEnding;
use uucore::parser::num_parser::{ExtendedParser, ExtendedParserError};
use uucore::parser::parse_size::{ParseSizeError, Parser};
use uucore::parser::shortcut_value_parser::ShortcutValueParser;
use uucore::posix::{MODERN, TRADITIONAL};
use uucore::show_error;
use uucore::translate;
use uucore::translate_text;
use uucore::version_cmp::version_cmp;
use uucore::{format_usage, i18n};
type InputReader = crate::trusted::Reader;
type SortResult<T> = Result<T, crate::trusted::IoFailure>;
fn boxed_reader<R: Read + Send + 'static>(reader: R) -> InputReader {
    { crate::trusted::Reader::new(reader) }
}
mod options {
    pub mod modes {
        pub const SORT: &'static str = "sort";
        pub const HUMAN_NUMERIC: &'static str = "human-numeric-sort";
        pub const MONTH: &'static str = "month-sort";
        pub const NUMERIC: &'static str = "numeric-sort";
        pub const GENERAL_NUMERIC: &'static str = "general-numeric-sort";
        pub const VERSION: &'static str = "version-sort";
        pub const RANDOM: &'static str = "random-sort";
    }
    pub mod check {
        pub const CHECK: &'static str = "check";
        pub const CHECK_SILENT: &'static str = "check-silent";
        pub const SILENT: &'static str = "silent";
        pub const QUIET: &'static str = "quiet";
        pub const DIAGNOSE_FIRST: &'static str = "diagnose-first";
    }
    pub const HELP: &'static str = "help";
    pub const VERSION: &'static str = "version";
    pub const DICTIONARY_ORDER: &'static str = "dictionary-order";
    pub const MERGE: &'static str = "merge";
    pub const DEBUG: &'static str = "debug";
    pub const IGNORE_CASE: &'static str = "ignore-case";
    pub const IGNORE_LEADING_BLANKS: &'static str = "ignore-leading-blanks";
    pub const IGNORE_NONPRINTING: &'static str = "ignore-nonprinting";
    pub const OUTPUT: &'static str = "output";
    pub const REVERSE: &'static str = "reverse";
    pub const STABLE: &'static str = "stable";
    pub const UNIQUE: &'static str = "unique";
    pub const KEY: &'static str = "key";
    pub const SEPARATOR: &'static str = "field-separator";
    pub const ZERO_TERMINATED: &'static str = "zero-terminated";
    pub const PARALLEL: &'static str = "parallel";
    pub const FILES0_FROM: &'static str = "files0-from";
    pub const BUF_SIZE: &'static str = "buffer-size";
    pub const TMP_DIR: &'static str = "temporary-directory";
    pub const COMPRESS_PROG: &'static str = "compress-program";
    pub const BATCH_SIZE: &'static str = "batch-size";
    pub const RANDOM_SOURCE: &'static str = "random-source";
    pub const FILES: &'static str = "files";
}
const DECIMAL_PT: u8 = b'.';
fn locale_decimal_pt() -> u8 {
    let bytes = crate::trusted::sorting::locale_decimal_bytes();
    match bytes.first().copied() {
        Some(b'.') => b'.',
        Some(b',') => b',',
        _ => DECIMAL_PT,
    }
}
const NEGATIVE: &'static u8 = &b'-';
const POSITIVE: &'static u8 = &b'+';
const MIN_AUTOMATIC_BUF_SIZE: usize = 512 * 1024;
const FALLBACK_AUTOMATIC_BUF_SIZE: usize = 32 * 1024 * 1024;
const MAX_AUTOMATIC_BUF_SIZE: usize = 1024 * 1024 * 1024;
#[derive(Debug, thiserror :: Error)]
pub enum SortError {
    # [error ("{}" , format_disorder (. file , . line_number , . line , . silent))]
    Disorder {
        file: OsString,
        line_number: usize,
        line: String,
        silent: bool,
    },
    # [error ("{}" , translate_text ! ("sort-open-failed" , "path" => format ! ("{}" , . path . maybe_quote ()) , "error" => strip_errno (. error)))]
    OpenFailed {
        path: PathBuf,
        error: std::io::Error,
    },
    # [error ("{}" , translate_text ! ("sort-truncate-failed" , "path" => format ! ("{}" , . path . maybe_quote ()) , "error" => strip_errno (. error)))]
    TruncateFailed {
        path: PathBuf,
        error: std::io::Error,
    },
    # [error ("{}" , translate_text ! ("sort-cannot-read" , "path" => format ! ("{}" , . path . maybe_quote ()) , "error" => strip_errno (. error)))]
    ReadFailed {
        path: PathBuf,
        error: std::io::Error,
    },
    # [error ("{}" , translate ! ("sort-read-failed" , "error" => strip_errno (. error)))]
    ChunkReadFailed { error: std::io::Error },
    # [error ("{}" , translate ! ("sort-open-tmp-file-failed" , "error" => strip_errno (. error)))]
    OpenTmpFileFailed { error: std::io::Error },
    # [error ("{}" , translate ! ("sort-compress-prog-execution-failed" , "prog" => . prog , "error" => strip_errno (. error)))]
    CompressProgExecutionFailed { prog: String, error: std::io::Error },
    # [error ("{}" , translate ! ("sort-compress-prog-terminated-abnormally" , "prog" => . prog . quote ()))]
    CompressProgTerminatedAbnormally { prog: String },
    # [error ("{}" , translate_text ! ("sort-cannot-create-tmp-file" , "path" => format ! ("{}" , . path . quote ())))]
    TmpFileCreationFailed { path: PathBuf },
    # [error ("{}" , translate_text ! ("sort-file-operands-combined" , "file" => format ! ("{}" , . file . quote ()) , "help" => uucore :: execution_phrase ()))]
    FileOperandsCombined { file: PathBuf },
    #[error("{error}")]
    Uft8Error { error: Utf8Error },
    # [error ("{}" , translate ! ("sort-multiple-output-files"))]
    MultipleOutputFiles,
    # [error ("{}" , translate ! ("sort-incompatible-tabs"))]
    IncompatibleTabs,
    # [error ("{}" , translate ! ("sort-minus-in-stdin"))]
    MinusInStdIn,
    # [error ("{}" , translate_text ! ("sort-no-input-from" , "file" => format ! ("{}" , . file . quote ())))]
    EmptyInputFile { file: PathBuf },
    # [error ("{}" , translate_text ! ("sort-random-source-end-of-file" , "path" => format ! ("{}" , . path . quote ())))]
    RandomSourceEndOfFile { path: PathBuf },
    # [error ("{}" , translate_text ! ("sort-invalid-zero-length-filename" , "file" => . file . maybe_quote () , "line_num" => . line_num))]
    ZeroLengthFileName { file: PathBuf, line_num: usize },
}
impl UError for SortError {
    fn code(&self) -> i32 {
        match self {
            Self::Disorder { .. } => 1,
            _ => 2,
        }
    }
}
#[expect(clippy::trivially_copy_pass_by_ref)]
fn format_disorder(file: &OsString, line_number: &usize, line: &String, silent: &bool) -> String {
    if *silent {
        String::new()
    } else {
        translate_text ! ("sort-error-disorder" , "file" => file . maybe_quote () , "line_number" => line_number , "line" => line . to_owned ())
    }
}
#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Copy, Debug)]
enum SortMode {
    Numeric,
    HumanNumeric,
    GeneralNumeric,
    Month,
    Version,
    Random,
    Default,
}
fn count_non_null_bytes(bytes: &[u8]) -> usize {
    bytes.iter().filter(|&&c| c != b'\0').count()
}
pub struct Output {
    file: Option<(OsString, File)>,
}
impl Output {
    fn new(name: Option<impl AsRef<OsStr>>) -> UResult<Self> {
        let file = if let Some(name) = name {
            let path = Path::new(name.as_ref());
            #[allow(clippy::suspicious_open_options)]
            let file = OpenOptions::new()
                .write(true)
                .create(true)
                .open(path)
                .map_err(|e| SortError::OpenFailed {
                    path: path.to_owned(),
                    error: e,
                })?;
            Some((name.as_ref().to_owned(), file))
        } else {
            None
        };
        Ok(Self { file })
    }
    fn into_write(self) -> UResult<BufWriter<Box<dyn Write>>> {
        Ok(BufWriter::new(match self.file {
            Some((name, file)) => {
                if file.metadata().is_ok_and(|meta| meta.is_file()) {
                    file.set_len(0).map_err(|error| SortError::TruncateFailed {
                        path: PathBuf::from(name),
                        error,
                    })?;
                }
                Box::new(file)
            }
            None => Box::new(stdout()),
        }))
    }
    fn as_output_name(&self) -> Option<&OsStr> {
        match &self.file {
            Some((name, _file)) => Some(name.as_os_str()),
            None => None,
        }
    }
    fn write_failed_context(&self) -> impl Fn() -> String + use<> {
        let output_name = self
            .as_output_name()
            .unwrap_or(OsStr::new("standard output"))
            .to_owned();
        move || translate_text ! ("sort-error-write-failed" , "output" => output_name . maybe_quote ())
    }
}
#[derive(Clone)]
pub struct GlobalSettings {
    mode: SortMode,
    debug: bool,
    ignore_leading_blanks: bool,
    ignore_case: bool,
    dictionary_order: bool,
    ignore_non_printing: bool,
    merge: bool,
    reverse: bool,
    stable: bool,
    unique: bool,
    check: bool,
    check_silent: bool,
    salt: Option<[u8; 16]>,
    random_source: Option<PathBuf>,
    selectors: Vec<FieldSelector>,
    separator: Option<u8>,
    line_ending: LineEnding,
    buffer_size: usize,
    buffer_size_is_explicit: bool,
    compress_prog: Option<String>,
    merge_batch_size: usize,
    numeric_locale: NumericLocaleSettings,
    precomputed: Precomputed,
}
#[derive(Clone, Copy, Debug)]
struct NumericLocaleSettings {
    thousands_sep: Option<u8>,
    decimal_pt: Option<u8>,
}
impl Default for NumericLocaleSettings {
    fn default() -> Self {
        Self {
            thousands_sep: None,
            decimal_pt: Some(DECIMAL_PT),
        }
    }
}
impl NumericLocaleSettings {
    fn num_info_settings(self, accept_si_units: bool, fold_si_units: bool) -> NumInfoParseSettings {
        NumInfoParseSettings {
            accept_si_units,
            fold_si_units,
            thousands_separator: self.thousands_sep,
            decimal_pt: self.decimal_pt,
        }
    }
}
#[derive(Clone, Debug, Default)]
struct Precomputed {
    needs_tokens: bool,
    num_infos_per_line: usize,
    floats_per_line: usize,
    selections_per_line: usize,
    fast_lexicographic: bool,
    fast_locale_collation: bool,
    fast_ascii_insensitive: bool,
    whole_line_numeric: bool,
    tokenize_blank_thousands_sep: bool,
    tokenize_allow_unit_after_blank: bool,
}
impl GlobalSettings {
    fn parse_byte_count(input: &str) -> Result<usize, ParseSizeError> {
        let size = Parser::default()
            .with_allow_list(&[
                "b", "k", "K", "m", "M", "g", "G", "t", "T", "P", "E", "Z", "Y", "R", "Q", "%",
            ])
            .with_default_unit("K")
            .with_b_byte_count(true)
            .parse(input.trim())?;
        usize::try_from(size).map_err(|_| {
            ParseSizeError::SizeTooBig(
                translate ! ("sort-error-buffer-size-too-big" , "size" => size),
            )
        })
    }
    fn init_precomputed(&mut self, disable_fast_lexicographic: bool) {
        {
            self.precomputed.needs_tokens =
                crate::trusted::configuration::any(&self.selectors, |s: &FieldSelector| -> bool {
                    s.needs_tokens
                });
            self.precomputed.selections_per_line = crate::trusted::configuration::count(
                &self.selectors,
                |s: &FieldSelector| -> bool { s.needs_selection },
            );
            self.precomputed.num_infos_per_line = crate::trusted::configuration::count(
                &self.selectors,
                |s: &FieldSelector| -> bool {
                    matches!(s.settings.mode, SortMode::Numeric | SortMode::HumanNumeric)
                },
            );
            self.precomputed.floats_per_line = crate::trusted::configuration::count(
                &self.selectors,
                |s: &FieldSelector| -> bool { matches!(s.settings.mode, SortMode::GeneralNumeric) },
            );
            let uses_numeric =
                crate::trusted::configuration::any(&self.selectors, |s: &FieldSelector| -> bool {
                    matches!(s.settings.mode, SortMode::Numeric | SortMode::HumanNumeric)
                });
            let uses_human_numeric =
                crate::trusted::configuration::any(&self.selectors, |s: &FieldSelector| -> bool {
                    matches!(s.settings.mode, SortMode::HumanNumeric)
                });
            self.precomputed.tokenize_blank_thousands_sep = self.separator.is_none()
                && uses_numeric
                && self.numeric_locale.thousands_sep == Some(b' ');
            self.precomputed.tokenize_allow_unit_after_blank =
                self.precomputed.tokenize_blank_thousands_sep && uses_human_numeric;
        }
        self.precomputed.fast_lexicographic =
            !disable_fast_lexicographic && self.can_use_fast_lexicographic();
        self.precomputed.fast_locale_collation =
            disable_fast_lexicographic && self.can_use_fast_lexicographic();
        self.precomputed.fast_ascii_insensitive = self.can_use_fast_ascii_insensitive();
        self.precomputed.whole_line_numeric = self.can_use_whole_line_numeric();
    }
    fn can_use_whole_line_numeric(&self) -> bool {
        if self.selectors.len() != 1 {
            return false;
        }
        let selector = &self.selectors[0];
        matches!(self.mode, SortMode::Numeric)
            && matches!(selector.settings.mode, SortMode::Numeric)
            && selector.settings.reverse == self.reverse
            && selector.from.field == 1
            && selector.from.char == 1
            && selector.to.is_none()
    }
    fn can_use_fast_lexicographic(&self) -> bool {
        if self.selectors.len() != 1 {
            return false;
        }
        let selector = &self.selectors[0];
        matches!(self.mode, SortMode::Default)
            && !self.ignore_case
            && !self.dictionary_order
            && !self.ignore_non_printing
            && !self.ignore_leading_blanks
            && !selector.needs_selection
            && matches!(selector.settings.mode, SortMode::Default)
            && !selector.settings.ignore_case
            && !selector.settings.dictionary_order
            && !selector.settings.ignore_non_printing
            && !selector.settings.ignore_blanks
            && selector.settings.reverse == self.reverse
    }
    fn can_use_fast_ascii_insensitive(&self) -> bool {
        if self.selectors.len() != 1 {
            return false;
        }
        let selector = &self.selectors[0];
        matches!(self.mode, SortMode::Default)
            && self.ignore_case
            && !self.dictionary_order
            && !self.ignore_non_printing
            && !self.ignore_leading_blanks
            && !selector.needs_selection
            && matches!(selector.settings.mode, SortMode::Default)
            && selector.settings.ignore_case
            && !selector.settings.dictionary_order
            && !selector.settings.ignore_non_printing
            && !selector.settings.ignore_blanks
            && selector.settings.reverse == self.reverse
    }
}
impl Default for GlobalSettings {
    fn default() -> Self {
        Self {
            mode: SortMode::Default,
            debug: false,
            ignore_leading_blanks: false,
            ignore_case: false,
            dictionary_order: false,
            ignore_non_printing: false,
            merge: false,
            reverse: false,
            stable: false,
            unique: false,
            check: false,
            check_silent: false,
            salt: None,
            random_source: None,
            selectors: vec![],
            separator: None,
            line_ending: LineEnding::Newline,
            buffer_size: FALLBACK_AUTOMATIC_BUF_SIZE,
            buffer_size_is_explicit: false,
            compress_prog: None,
            merge_batch_size: default_merge_batch_size(),
            numeric_locale: NumericLocaleSettings::default(),
            precomputed: Precomputed::default(),
        }
    }
}
#[derive(Clone, PartialEq, Debug)]
struct KeySettings {
    mode: SortMode,
    ignore_blanks: bool,
    ignore_case: bool,
    dictionary_order: bool,
    ignore_non_printing: bool,
    reverse: bool,
}
impl From<&GlobalSettings> for KeySettings {
    fn from(settings: &GlobalSettings) -> Self {
        Self {
            mode: settings.mode,
            ignore_blanks: settings.ignore_leading_blanks,
            ignore_case: settings.ignore_case,
            ignore_non_printing: settings.ignore_non_printing,
            reverse: settings.reverse,
            dictionary_order: settings.dictionary_order,
        }
    }
}
impl Default for KeySettings {
    fn default() -> Self {
        Self::from(&GlobalSettings::default())
    }
}
#[derive(Clone, Copy, Debug, Default)]
struct ModeFlags {
    numeric: bool,
    general_numeric: bool,
    human_numeric: bool,
    month: bool,
    version: bool,
    random: bool,
}
impl ModeFlags {
    fn from_mode(mode: SortMode) -> Self {
        let mut flags = Self::default();
        match mode {
            SortMode::Numeric => flags.numeric = true,
            SortMode::GeneralNumeric => flags.general_numeric = true,
            SortMode::HumanNumeric => flags.human_numeric = true,
            SortMode::Month => flags.month = true,
            SortMode::Version => flags.version = true,
            SortMode::Random => flags.random = true,
            SortMode::Default => {}
        }
        flags
    }
    fn to_mode(self) -> SortMode {
        if self.numeric {
            SortMode::Numeric
        } else if self.general_numeric {
            SortMode::GeneralNumeric
        } else if self.human_numeric {
            SortMode::HumanNumeric
        } else if self.month {
            SortMode::Month
        } else if self.random {
            SortMode::Random
        } else if self.version {
            SortMode::Version
        } else {
            SortMode::Default
        }
    }
}
fn ordering_opts_string(
    flags: ModeFlags,
    dictionary_order: bool,
    ignore_non_printing: bool,
    ignore_case: bool,
) -> String {
    let mut opts = String::new();
    if dictionary_order {
        opts.push('d');
    }
    if ignore_case {
        opts.push('f');
    }
    if flags.general_numeric {
        opts.push('g');
    }
    if flags.human_numeric {
        opts.push('h');
    }
    if !dictionary_order && ignore_non_printing {
        opts.push('i');
    }
    if flags.month {
        opts.push('M');
    }
    if flags.numeric {
        opts.push('n');
    }
    if flags.random {
        opts.push('R');
    }
    if flags.version {
        opts.push('V');
    }
    opts
}
fn ordering_incompatible(
    flags: ModeFlags,
    dictionary_order: bool,
    ignore_non_printing: bool,
) -> bool {
    let mode_count = u8::from(flags.numeric)
        + u8::from(flags.general_numeric)
        + u8::from(flags.human_numeric)
        + u8::from(flags.month);
    if mode_count > 1 {
        return true;
    }
    if mode_count == 1 {
        return flags.version || flags.random || dictionary_order || ignore_non_printing;
    }
    false
}
fn incompatible_options_message(opts: &str) -> String {
    translate ! ("sort-options-incompatible" , "opt1" => opts , "opt2" => "")
}
#[cold]
#[inline(never)]
fn incompatible_options_error(opts: &str) -> Box<dyn UError> {
    USimpleError::new(2, incompatible_options_message(opts))
}
enum Selection<'a> {
    AsBigDecimal(GeneralBigDecimalParseResult),
    WithNumInfo(&'a [u8], NumInfo),
    Str(&'a [u8]),
}
type Field = Range<usize>;
#[derive(Clone, Debug)]
pub struct Line<'a> {
    line: &'a [u8],
    index: usize,
}
impl<'a> Line<'a> {
    fn create<'s>(
        line: &'a [u8],
        index: usize,
        line_data: &mut LineData<'a>,
        token_buffer: &mut Vec<Field>,
        settings: &'s GlobalSettings,
    ) -> Self {
        let line = crate::trusted::bounded_bytes(line);
        #[cfg(feature = "i18n-collator")]
        if settings.precomputed.fast_locale_collation {
            compute_sort_key_utf8(line, &mut line_data.collation_key_buffer);
            line_data
                .collation_key_ends
                .push(line_data.collation_key_buffer.len());
            return Self { line, index };
        }
        let needs_line_data = settings.precomputed.needs_tokens
            || settings.precomputed.selections_per_line > 0
            || settings.precomputed.num_infos_per_line > 0
            || settings.precomputed.floats_per_line > 0
            || settings.precomputed.whole_line_numeric;
        if !needs_line_data {
            return Self { line, index };
        }
        token_buffer.clear();
        if settings.precomputed.needs_tokens {
            tokenize(
                line,
                settings.separator,
                token_buffer,
                &settings.precomputed,
            );
        }
        if settings.precomputed.whole_line_numeric {
            let line_num_float = if crate::trusted::sorting::any_ascii_alpha(line) {
                None
            } else {
                match crate::trusted::sorting::utf8(line) {
                    Err(_) => None,
                    Ok(text) => {
                        if crate::trusted::sorting::trimmed_plus(text) {
                            None
                        } else {
                            crate::trusted::sorting::float_from_str(text)
                        }
                    }
                }
            };
            line_data.line_num_floats.push(line_num_float);
        }
        for selector in &settings.selectors {
            let selection = selector.get_selection(line, token_buffer, settings.numeric_locale);
            match selection {
                Selection::AsBigDecimal(parsed_float) => line_data.parsed_floats.push(parsed_float),
                Selection::WithNumInfo(str, num_info) => {
                    line_data.num_infos.push(num_info);
                    line_data.selections.push(str);
                }
                Selection::Str(str) => {
                    if selector.needs_selection {
                        line_data.selections.push(str);
                    }
                }
            }
        }
        Self { line, index }
    }
    fn write(&self, writer: &mut impl Write, settings: &GlobalSettings) -> std::io::Result<()> {
        if settings.debug {
        } else {
            {
                crate::trusted::write_output(writer, self.line)?;
            }
            {
                crate::trusted::write_output(writer, &[settings.line_ending.into()])?;
            }
        }
        Ok(())
    }
    fn write_debug(
        &self,
        settings: &GlobalSettings,
        writer: &mut impl Write,
    ) -> std::io::Result<()> {
        let line = self
            .line
            .iter()
            .copied()
            .map(|c| if c == b'\t' { b'>' } else { c })
            .collect::<Vec<_>>();
        writer.write_all(&line)?;
        writeln!(writer)?;
        let mut fields = vec![];
        tokenize(
            self.line,
            settings.separator,
            &mut fields,
            &settings.precomputed,
        );
        for selector in &settings.selectors {
            let mut selection = selector.get_range(self.line, Some(&fields));
            match selector.settings.mode {
                SortMode::Numeric | SortMode::HumanNumeric => {
                    let mut parse_settings = settings
                        .numeric_locale
                        .num_info_settings(selector.settings.mode == SortMode::HumanNumeric, false);
                    parse_settings.thousands_separator = None;
                    let (_, num_range) =
                        NumInfo::parse(&self.line[selection.clone()], &parse_settings);
                    let initial_selection = selection.clone();
                    selection.start += num_range.start;
                    selection.end = selection.start + num_range.len();
                    if num_range == (0..0) {
                        let leading_whitespace = self.line[selection.clone()]
                            .iter()
                            .position(|c| !c.is_ascii_whitespace())
                            .unwrap_or(0);
                        selection.start += leading_whitespace;
                        selection.end += leading_whitespace;
                    } else {
                        if selector.settings.mode == SortMode::HumanNumeric
                            && self.line[selection.end..initial_selection.end]
                                .first()
                                .is_some_and(|c| b"kKMGTPEZYRQ".contains(c))
                        {
                            selection.end += 1;
                        }
                        while self.line[initial_selection.start..selection.start]
                            .last()
                            .is_some_and(|c| b"-0.".contains(c))
                        {
                            selection.start -= 1;
                        }
                    }
                }
                SortMode::GeneralNumeric => {
                    let initial_selection = &self.line[selection.clone()];
                    let decimal_pt = locale_decimal_pt();
                    let leading = get_leading_gen(initial_selection, decimal_pt);
                    selection.start += leading.start;
                    selection.end = selection.start + leading.len();
                }
                SortMode::Month => {
                    let initial_selection = &self.line[selection.clone()];
                    let first_non_blank = initial_selection
                        .iter()
                        .position(|&c| !is_blank(c))
                        .unwrap_or(initial_selection.len());
                    let (parsed, match_len) = month_parse(initial_selection);
                    if parsed == Month::Unknown {
                        selection.start += first_non_blank;
                        selection.end = selection.start;
                    } else {
                        selection.start += first_non_blank;
                        selection.end = selection.start + match_len;
                    }
                }
                _ => {}
            }
            let select = &line[..selection.start];
            let indent = count_non_null_bytes(select);
            write!(writer, "{}", " ".repeat(indent))?;
            if selection.is_empty() {
                writeln!(writer, "{}", translate!("sort-error-no-match-for-key"))?;
            } else {
                let select = &line[selection];
                let underline_len = count_non_null_bytes(select);
                writeln!(writer, "{}", "_".repeat(underline_len))?;
            }
        }
        if settings.mode != SortMode::Random
            && !settings.stable
            && !settings.unique
            && (settings.dictionary_order
                || settings.ignore_leading_blanks
                || settings.ignore_case
                || settings.ignore_non_printing
                || settings.mode != SortMode::Default
                || settings
                    .selectors
                    .last()
                    .is_none_or(|selector| selector != &FieldSelector::default()))
        {
            if self.line.is_empty() {
                writeln!(writer, "{}", translate!("sort-error-no-match-for-key"))?;
            } else {
                writeln!(writer, "{}", "_".repeat(self.line.len()))?;
            }
        }
        Ok(())
    }
}
fn tokenize(
    line: &[u8],
    separator: Option<u8>,
    token_buffer: &mut Vec<Field>,
    precomputed: &Precomputed,
) {
    if let Some(separator) = separator {
        tokenize_with_separator(line, separator, token_buffer);
    } else {
        tokenize_default(
            line,
            token_buffer,
            precomputed.tokenize_blank_thousands_sep,
            precomputed.tokenize_allow_unit_after_blank,
        );
    }
}
fn tokenize_default(
    line: &[u8],
    token_buffer: &mut Vec<Field>,
    blank_thousands_sep: bool,
    allow_unit_after_blank: bool,
) {
    token_buffer.push(0..0);
    let mut previous_was_whitespace = true;
    let byte_iter = crate::trusted::keys::enumerate_bytes(line);
    for (idx, char) in byte_iter {
        let is_separator = is_blank(*char);
        if is_separator {
            if !previous_was_whitespace {
                let last = token_buffer.last_mut().unwrap();
                last.end = idx;
                token_buffer.push(idx..0);
            }
            previous_was_whitespace = true;
        } else {
            previous_was_whitespace = false;
        }
    }
    let last = token_buffer.last_mut().unwrap();
    last.end = line.len();
}
fn is_blank_thousands_sep(line: &[u8], idx: usize, allow_unit_after_blank: bool) -> bool {
    if line.get(idx) != Some(&b' ') {
        return false;
    }
    let prev_is_digit = idx
        .checked_sub(1)
        .and_then(|prev_idx| line.get(prev_idx))
        .is_some_and(u8::is_ascii_digit);
    if !prev_is_digit {
        return false;
    }
    let next = line.get(idx + 1).copied();
    next.is_some_and(|c| {
        c.is_ascii_digit() || (allow_unit_after_blank && b"kKMGTPEZYRQ".contains(&c))
    })
}
fn tokenize_with_separator(line: &[u8], separator: u8, token_buffer: &mut Vec<Field>) {
    let separator_indices =
        crate::trusted::keys::filter_indices(line, |byte: u8| -> bool { byte == separator });
    let mut start = 0;
    for sep_idx in separator_indices {
        token_buffer.push(start..sep_idx);
        start = sep_idx + 1;
    }
    if start < line.len() {
        token_buffer.push(start..line.len());
    }
}
#[derive(Clone, PartialEq, Debug)]
struct KeyPosition {
    field: usize,
    char: usize,
    ignore_blanks: bool,
}
impl Default for KeyPosition {
    fn default() -> Self {
        Self {
            field: 1,
            char: 1,
            ignore_blanks: false,
        }
    }
}
pub struct KeyError {
    message: String,
    span: Range<usize>,
    kind: KeyErrorKind,
}
pub enum KeyErrorKind {
    #[doc = " A field or character number was expected, and there were no digits."]
    MissingCount,
    #[doc = " A number was given where counting starts at one."]
    ZeroCount,
    #[doc = " Something that is not a key option, past the end of the spec."]
    StrayCharacter,
    #[doc = " Ordering options that contradict each other."]
    IncompatibleOptions,
}
impl From<KeyError> for Box<dyn UError> {
    fn from(error: KeyError) -> Self {
        USimpleError::new(2, error.message)
    }
}
fn missing_count(span_start: usize, msg_key: &str, rest: &str) -> KeyError {
    KeyError {
        message: format!(
            "{}: {}",
            translate!(msg_key),
            translate ! ("sort-invalid-count-at-start-of" , "string" => rest . quote ())
        ),
        span: span_start..span_start + rest.len(),
        kind: KeyErrorKind::MissingCount,
    }
}
fn stray_character(key: &str, offset: usize) -> KeyError {
    let width = key[offset..].chars().next().map_or(0, char::len_utf8);
    bad_field_spec(
        key,
        offset..offset + width,
        "sort-stray-character-field-spec",
        KeyErrorKind::StrayCharacter,
    )
}
fn bad_field_spec(spec: &str, span: Range<usize>, msg_key: &str, kind: KeyErrorKind) -> KeyError {
    KeyError {
        message: translate ! ("sort-invalid-field-spec" , "msg" => translate ! (msg_key) , "spec" => spec . quote ()),
        span,
        kind,
    }
}
fn parse_field_count<'a>(
    input: &'a str,
    offset: usize,
    msg_key: &str,
) -> Result<(usize, &'a str), KeyError> {
    let bytes = input.as_bytes();
    let mut idx = 0;
    while bytes.get(idx).is_some_and(u8::is_ascii_digit) {
        idx += 1;
    }
    if idx == 0 {
        return Err(missing_count(offset, msg_key, input));
    }
    let (num_str, rest) = input.split_at(idx);
    let value = match num_str.parse::<usize>() {
        Ok(v) => v,
        Err(e) if *e.kind() == IntErrorKind::PosOverflow => usize::MAX,
        Err(_) => return Err(missing_count(offset, msg_key, input)),
    };
    Ok((value, rest))
}
#[derive(Clone, Copy, PartialEq)]
enum KeyEnd {
    #[doc = " Before the comma, or the whole spec when there is none."]
    From,
    #[doc = " After the comma."]
    To,
}
impl KeyEnd {
    fn missing_field_key(self) -> &'static str {
        match self {
            Self::From => "sort-invalid-number-at-field-start",
            Self::To => "sort-invalid-number-after-comma",
        }
    }
    fn default_char(self) -> usize {
        match self {
            Self::From => 1,
            Self::To => 0,
        }
    }
}
fn parse_position<'a>(
    key: &str,
    input: &'a str,
    end: KeyEnd,
) -> Result<(usize, usize, &'a str), KeyError> {
    let at = |rest: &str| key.len() - rest.len();
    let (field, mut rest) = parse_field_count(input, at(input), end.missing_field_key())?;
    if field == 0 {
        return Err(bad_field_spec(
            key,
            at(input)..at(rest),
            "sort-field-number-is-zero",
            KeyErrorKind::ZeroCount,
        ));
    }
    let mut char = end.default_char();
    if let Some(stripped) = rest.strip_prefix('.') {
        let (char_idx, rest_after) =
            parse_field_count(stripped, at(stripped), "sort-invalid-number-after-dot")?;
        if char_idx == 0 && end == KeyEnd::From {
            return Err(bad_field_spec(
                key,
                at(stripped)..at(rest_after),
                "sort-character-offset-is-zero",
                KeyErrorKind::ZeroCount,
            ));
        }
        char = char_idx;
        rest = rest_after;
    }
    Ok((field, char, rest))
}
fn is_ordering_option_char(byte: u8) -> bool {
    matches!(
        byte,
        b'b' | b'd' | b'f' | b'g' | b'h' | b'i' | b'M' | b'n' | b'R' | b'r' | b'V'
    )
}
fn ordering_options_span(key: &str) -> Range<usize> {
    let is_option = |(_, byte): &(usize, u8)| is_ordering_option_char(*byte);
    let mut options = key.bytes().enumerate().filter(is_option);
    let Some((first, _)) = options.next() else {
        return 0..key.len();
    };
    let last = options.next_back().map_or(first, |(index, _)| index);
    first..last + 1
}
fn parse_ordering_options<'a>(
    input: &'a str,
    settings: &mut KeySettings,
    flags: &mut ModeFlags,
) -> (&'a str, bool) {
    let mut ignore_blanks = false;
    let bytes = input.as_bytes();
    let mut idx = 0;
    while let Some(byte) = bytes.get(idx) {
        match byte {
            b'b' => ignore_blanks = true,
            b'd' => {
                settings.dictionary_order = true;
                settings.ignore_non_printing = false;
            }
            b'f' => settings.ignore_case = true,
            b'g' => flags.general_numeric = true,
            b'h' => flags.human_numeric = true,
            b'i' => {
                if !settings.dictionary_order {
                    settings.ignore_non_printing = true;
                }
            }
            b'M' => flags.month = true,
            b'n' => flags.numeric = true,
            b'R' => flags.random = true,
            b'r' => settings.reverse = true,
            b'V' => flags.version = true,
            _ => break,
        }
        idx += 1;
    }
    (&input[idx..], ignore_blanks)
}
#[derive(Clone, PartialEq, Debug, Default)]
struct FieldSelector {
    from: KeyPosition,
    to: Option<KeyPosition>,
    settings: KeySettings,
    needs_tokens: bool,
    needs_selection: bool,
}
enum KeyResolution {
    StartOfChar(usize),
    EndOfChar(usize),
    TooLow,
    TooHigh,
}
fn key_resolve_index(
    line: &[u8],
    tokens: Option<&[Field]>,
    position: &KeyPosition,
) -> KeyResolution {
    if matches ! (tokens , Some (tokens) if tokens . len () < position . field) {
        KeyResolution::TooHigh
    } else if position.char == 0 {
        let end = tokens.unwrap()[position.field - 1].end;
        if end == 0 {
            KeyResolution::TooLow
        } else {
            KeyResolution::EndOfChar(end)
        }
    } else {
        let mut idx = if position.field == 1 {
            0
        } else {
            tokens.unwrap()[position.field - 1].start
        };
        if position.ignore_blanks {
            let offset = crate::trusted::keys::find_index(&line[idx..], |byte: &u8| -> bool {
                !is_blank(*byte)
            });
            idx += offset;
        }
        let offset = crate::trusted::keys::nth_index(&line[idx..], position.char - 1);
        idx += offset;
        if idx >= line.len() {
            KeyResolution::TooHigh
        } else {
            KeyResolution::StartOfChar(idx)
        }
    }
}
impl FieldSelector {
    fn parse(key: &str, global_settings: &GlobalSettings) -> Result<Self, KeyError> {
        let at = |rest: &str| key.len() - rest.len();
        let has_options = key.as_bytes().iter().copied().any(is_ordering_option_char);
        let mut settings = if has_options {
            KeySettings::default()
        } else {
            KeySettings::from(global_settings)
        };
        let mut flags = if has_options {
            ModeFlags::default()
        } else {
            ModeFlags::from_mode(settings.mode)
        };
        let mut from_ignore_blanks = if has_options {
            false
        } else {
            settings.ignore_blanks
        };
        let mut to_ignore_blanks = if has_options {
            false
        } else {
            settings.ignore_blanks
        };
        let (from_field, from_char, rest) = parse_position(key, key, KeyEnd::From)?;
        let (rest_after_opts, ignore_blanks) =
            parse_ordering_options(rest, &mut settings, &mut flags);
        if ignore_blanks {
            from_ignore_blanks = true;
        }
        let mut to = None;
        if let Some(rest_after_comma) = rest_after_opts.strip_prefix(',') {
            let (to_field, to_char, rest) = parse_position(key, rest_after_comma, KeyEnd::To)?;
            let (rest, ignore_blanks_end) = parse_ordering_options(rest, &mut settings, &mut flags);
            if ignore_blanks_end {
                to_ignore_blanks = true;
            }
            if !rest.is_empty() {
                return Err(stray_character(key, at(rest)));
            }
            to = Some(KeyPosition {
                field: to_field,
                char: to_char,
                ignore_blanks: to_ignore_blanks,
            });
        } else if !rest_after_opts.is_empty() {
            return Err(stray_character(key, at(rest_after_opts)));
        }
        if ordering_incompatible(
            flags,
            settings.dictionary_order,
            settings.ignore_non_printing,
        ) {
            let opts = ordering_opts_string(
                flags,
                settings.dictionary_order,
                settings.ignore_non_printing,
                settings.ignore_case,
            );
            return Err(KeyError {
                message: incompatible_options_message(&opts),
                span: ordering_options_span(key),
                kind: KeyErrorKind::IncompatibleOptions,
            });
        }
        settings.mode = flags.to_mode();
        let from = KeyPosition {
            field: from_field,
            char: from_char,
            ignore_blanks: from_ignore_blanks,
        };
        Ok(Self::new(from, to, settings))
    }
    fn new(from: KeyPosition, to: Option<KeyPosition>, settings: KeySettings) -> Self {
        Self {
            needs_selection: (from.field != 1
                || from.char != 1
                || to.is_some()
                || matches!(settings.mode, SortMode::Numeric | SortMode::HumanNumeric)
                || from.ignore_blanks)
                && !matches!(settings.mode, SortMode::GeneralNumeric),
            needs_tokens: from.field != 1 || to.is_some(),
            from,
            to,
            settings,
        }
    }
    fn get_selection<'a>(
        &self,
        line: &'a [u8],
        tokens: &[Field],
        numeric_locale: NumericLocaleSettings,
    ) -> Selection<'a> {
        let tokens = if self.needs_tokens {
            Some(tokens)
        } else {
            None
        };
        let mut range_str = &line[self.get_range(line, tokens)];
        if self.settings.mode == SortMode::Numeric || self.settings.mode == SortMode::HumanNumeric {
            let (info, num_range) = NumInfo::parse(
                range_str,
                &numeric_locale.num_info_settings(
                    self.settings.mode == SortMode::HumanNumeric,
                    self.settings.ignore_case,
                ),
            );
            range_str = &range_str[num_range];
            Selection::WithNumInfo(range_str, info)
        } else if self.settings.mode == SortMode::GeneralNumeric {
            let decimal_pt = locale_decimal_pt();
            Selection::AsBigDecimal(general_bd_parse(
                &range_str[get_leading_gen(range_str, decimal_pt)],
                decimal_pt,
            ))
        } else {
            Selection::Str(range_str)
        }
    }
    fn get_range(&self, line: &[u8], tokens: Option<&[Field]>) -> Range<usize> {
        match key_resolve_index(line, tokens, &self.from) {
            KeyResolution::StartOfChar(from) => {
                let to = match &self.to {
                    None => None,
                    Some(to) => Some(key_resolve_index(line, tokens, to)),
                };
                let mut range = match to {
                    Some(KeyResolution::StartOfChar(mut to)) => {
                        to += 1;
                        from..to
                    }
                    Some(KeyResolution::EndOfChar(to)) => from..to,
                    None | Some(KeyResolution::TooHigh) => from..line.len(),
                    Some(KeyResolution::TooLow) => 0..0,
                };
                if range.start > range.end {
                    range.end = range.start;
                }
                range
            }
            KeyResolution::TooLow | KeyResolution::EndOfChar(_) => 0..0,
            KeyResolution::TooHigh => line.len()..line.len(),
        }
    }
}
fn detect_numeric_locale() -> NumericLocaleSettings {
    let numeric_locale = i18n::get_numeric_locale();
    let locale = &numeric_locale.0;
    let encoding = numeric_locale.1;
    let is_c_locale = encoding == i18n::UEncoding::Ascii && locale.to_string() == "und";
    if is_c_locale {
        return NumericLocaleSettings {
            decimal_pt: Some(DECIMAL_PT),
            thousands_sep: None,
        };
    }
    let grouping = i18n::decimal::locale_grouping_separator();
    NumericLocaleSettings {
        decimal_pt: Some(locale_decimal_pt()),
        thousands_sep: match grouping.as_bytes() {
            [b] => Some(*b),
            [0xC2, 0xA0] if encoding != i18n::UEncoding::Utf8 => Some(0xA0),
            _ => None,
        },
    }
}
fn make_sort_mode_arg(mode: &'static str, short: char, help: String) -> Arg {
    Arg::new(mode)
        .short(short)
        .long(mode)
        .help(help)
        .action(ArgAction::SetTrue)
}
#[cfg(unix)]
fn get_rlimit() -> UResult<usize> {
    use rlimit::{Resource, getrlimit};
    let (rlim_cur, _) = getrlimit(Resource::NOFILE)
        .map_err(|_| UUsageError::new(2, translate!("sort-failed-fetch-rlimit")))?;
    usize::try_from(rlim_cur)
        .map_err(|_| UUsageError::new(2, translate!("sort-failed-fetch-rlimit")))
}
#[cfg(unix)]
pub(crate) fn fd_soft_limit() -> Option<usize> {
    get_rlimit().ok()
}
#[cfg(not(unix))]
pub(crate) fn fd_soft_limit() -> Option<usize> {
    None
}
fn max_merge_batch_size() -> Option<usize> {
    const RESERVED_STDIO: usize = 3;
    fd_soft_limit().map(|limit| limit.saturating_sub(RESERVED_STDIO))
}
#[cfg(unix)]
pub(crate) fn current_open_fd_count() -> Option<usize> {
    fn count_dir(path: &str) -> Option<usize> {
        let entries = std::fs::read_dir(path).ok()?;
        let mut count = 0usize;
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name.parse::<usize>().is_ok() {
                count = count.saturating_add(1);
            }
        }
        Some(count)
    }
    if let Some(count) = count_dir("/proc/self/fd").or_else(|| count_dir("/dev/fd")) {
        return Some(count);
    }
    let limit = fd_soft_limit().filter(|l| *l <= 16_384)?;
    let mut count = 0usize;
    for fd in 0..limit {
        let fd = fd as core::ffi::c_int;
        if unsafe { libc::fcntl(fd, libc::F_GETFD) } != -1 {
            count = count.saturating_add(1);
        }
    }
    Some(count)
}
#[cfg(not(unix))]
pub(crate) fn current_open_fd_count() -> Option<usize> {
    None
}
const STDIN_FILE: &'static str = "-";
fn allows_traditional_usage() -> bool {
    !matches ! (uucore :: posix :: posix_version () , Some (ver) if (TRADITIONAL .. MODERN) . contains (& ver))
}
#[derive(Debug, Clone)]
struct LegacyKeyPart {
    field: usize,
    char_pos: usize,
    opts: String,
}
#[derive(Debug, Clone)]
struct LegacyKeyWarning {
    arg_index: usize,
    key_index: Option<usize>,
    from_field: usize,
    to_field: Option<usize>,
    to_char: Option<usize>,
}
impl LegacyKeyWarning {
    fn legacy_key_display(&self) -> String {
        match self.to_field {
            Some(to) => format!("+{} -{to}", self.from_field),
            None => format!("+{}", self.from_field),
        }
    }
    fn replacement_key_display(&self) -> String {
        let start_field = self.from_field.saturating_add(1);
        match self.to_field {
            Some(to_field) => {
                let end_field = match self.to_char {
                    Some(0) | None => to_field.max(1),
                    Some(_) => to_field.saturating_add(1),
                };
                format!("{start_field},{end_field}")
            }
            None => start_field.to_string(),
        }
    }
}
#[derive(Default)]
struct GlobalOptionFlags {
    keys_specified: bool,
    ignore_leading_blanks: bool,
    dictionary_order: bool,
    ignore_case: bool,
    ignore_non_printing: bool,
    reverse: bool,
    mode_numeric: bool,
    mode_general: bool,
    mode_human: bool,
    mode_month: bool,
    mode_random: bool,
    mode_version: bool,
}
impl GlobalOptionFlags {
    fn from_matches(matches: &ArgMatches) -> Self {
        let sort_value = matches
            .get_one::<String>(options::modes::SORT)
            .map(String::as_str);
        Self {
            keys_specified: matches.contains_id(options::KEY),
            ignore_leading_blanks: matches.get_flag(options::IGNORE_LEADING_BLANKS),
            dictionary_order: matches.get_flag(options::DICTIONARY_ORDER),
            ignore_case: matches.get_flag(options::IGNORE_CASE),
            ignore_non_printing: matches.get_flag(options::IGNORE_NONPRINTING),
            reverse: matches.get_flag(options::REVERSE),
            mode_human: matches.get_flag(options::modes::HUMAN_NUMERIC)
                || sort_value == Some("human-numeric"),
            mode_month: matches.get_flag(options::modes::MONTH) || sort_value == Some("month"),
            mode_general: matches.get_flag(options::modes::GENERAL_NUMERIC)
                || sort_value == Some("general-numeric"),
            mode_numeric: matches.get_flag(options::modes::NUMERIC)
                || sort_value == Some("numeric"),
            mode_version: matches.get_flag(options::modes::VERSION)
                || sort_value == Some("version"),
            mode_random: matches.get_flag(options::modes::RANDOM) || sort_value == Some("random"),
        }
    }
}
fn parse_usize_or_max(num: &str) -> Option<usize> {
    match num.parse::<usize>() {
        Ok(v) => Some(v),
        Err(e) if *e.kind() == IntErrorKind::PosOverflow => Some(usize::MAX),
        Err(_) => None,
    }
}
fn parse_legacy_part(spec: &str) -> Option<LegacyKeyPart> {
    let idx = spec.chars().take_while(char::is_ascii_digit).count();
    if idx == 0 {
        return None;
    }
    let field = parse_usize_or_max(&spec[..idx])?;
    let mut char_pos = 0;
    let mut rest = &spec[idx..];
    if let Some(stripped) = rest.strip_prefix('.') {
        let char_idx = stripped.chars().take_while(char::is_ascii_digit).count();
        if char_idx == 0 {
            return None;
        }
        char_pos = parse_usize_or_max(&stripped[..char_idx])?;
        rest = &stripped[char_idx..];
    }
    Some(LegacyKeyPart {
        field,
        char_pos,
        opts: rest.to_string(),
    })
}
fn legacy_key_to_k(from: &LegacyKeyPart, to: Option<&LegacyKeyPart>) -> String {
    let start_field = from.field.saturating_add(1);
    let start_char = from.char_pos.saturating_add(1);
    let mut keydef = format!(
        "{start_field}{}{}",
        if from.char_pos == 0 {
            String::new()
        } else {
            format!(".{start_char}")
        },
        from.opts,
    );
    if let Some(to) = to {
        let end_field = if to.char_pos == 0 {
            to.field.max(1)
        } else {
            to.field.saturating_add(1)
        };
        keydef.push(',');
        keydef.push_str(&end_field.to_string());
        if to.char_pos != 0 {
            keydef.push('.');
            keydef.push_str(&to.char_pos.to_string());
        }
        keydef.push_str(&to.opts);
    }
    keydef
}
fn preprocess_legacy_args<I>(args: I) -> (Vec<OsString>, Vec<LegacyKeyWarning>)
where
    I: IntoIterator,
    I::Item: Into<OsString>,
{
    if !allows_traditional_usage() {
        return (args.into_iter().map(Into::into).collect(), Vec::new());
    }
    let mut processed = Vec::new();
    let mut legacy_warnings = Vec::new();
    let mut iter = args.into_iter().map(Into::into).peekable();
    while let Some(arg) = iter.next() {
        if arg == "--" {
            processed.push(arg);
            processed.extend(iter);
            break;
        }
        let as_str = arg.to_string_lossy();
        if let Some(from_spec) = as_str.strip_prefix('+')
            && let Some(from) = parse_legacy_part(from_spec)
        {
            let mut to_part = None;
            let next_candidate = iter.peek().map(|next| next.to_string_lossy().to_string());
            if let Some(next_str) = next_candidate
                && let Some(stripped) = next_str
                    .strip_prefix('-')
                    .filter(|s| s.starts_with(|c: char| c.is_ascii_digit()))
            {
                let next_arg = iter.next().unwrap();
                if let Some(parsed) = parse_legacy_part(stripped) {
                    to_part = Some(parsed);
                } else {
                    processed.push(arg);
                    processed.push(next_arg);
                    continue;
                }
            }
            let keydef = legacy_key_to_k(&from, to_part.as_ref());
            let arg_index = processed.len();
            legacy_warnings.push(LegacyKeyWarning {
                arg_index,
                key_index: None,
                from_field: from.field,
                to_field: to_part.as_ref().map(|p| p.field),
                to_char: to_part.as_ref().map(|p| p.char_pos),
            });
            processed.push(OsString::from(format!("-k{keydef}")));
            continue;
        }
        processed.push(arg);
    }
    (processed, legacy_warnings)
}
fn index_legacy_warnings(processed_args: &[OsString], legacy_warnings: &mut [LegacyKeyWarning]) {
    if legacy_warnings.is_empty() {
        return;
    }
    let mut index_by_arg = HashMap::default();
    for (warning_idx, warning) in legacy_warnings.iter().enumerate() {
        index_by_arg.insert(warning.arg_index, warning_idx);
    }
    let mut key_index = 0usize;
    let mut i = 0usize;
    while let Some(arg) = processed_args.get(i).filter(|&a| a != OsStr::new("--")) {
        let mut matched_key = false;
        if arg == OsStr::new("-k") || arg == OsStr::new("--key") {
            if i + 1 < processed_args.len() {
                key_index = key_index.saturating_add(1);
                matched_key = true;
                i += 2;
            } else {
                i += 1;
            }
        } else {
            let as_str = arg.to_string_lossy();
            if as_str
                .strip_prefix("-k")
                .is_some_and(|spec| !spec.is_empty())
                || as_str
                    .strip_prefix("--key=")
                    .is_some_and(|spec| !spec.is_empty())
            {
                key_index = key_index.saturating_add(1);
                matched_key = true;
            }
            i += 1;
        }
        if matched_key && let Some(&warning_idx) = index_by_arg.get(&i.saturating_sub(1)) {
            legacy_warnings[warning_idx].key_index = Some(key_index);
        }
    }
}
#[cfg(target_os = "linux")]
const LINUX_BATCH_DIVISOR: usize = 4;
#[cfg(target_os = "linux")]
const LINUX_BATCH_MIN: usize = 32;
#[cfg(target_os = "linux")]
const LINUX_BATCH_MAX: usize = 256;
fn default_merge_batch_size() -> usize {
    #[cfg(target_os = "linux")]
    {
        let limit = crate::trusted::descriptor_limit();
        match limit {
            Some(limit) => {
                let usable_limit = limit.saturating_div(LINUX_BATCH_DIVISOR);
                usable_limit.clamp(LINUX_BATCH_MIN, LINUX_BATCH_MAX)
            }
            None => 64,
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        64
    }
}
#[cfg(not(unix))]
fn locale_failed_to_set() -> bool {
    env::var_os("LC_ALL").as_deref() == Some(OsStr::new("missing"))
}
#[cfg(unix)]
fn locale_failed_to_set() -> bool {
    unsafe { libc::setlocale(libc::LC_COLLATE, c"".as_ptr()).is_null() }
}
fn key_zero_width(selector: &FieldSelector) -> bool {
    let Some(to) = &selector.to else {
        return false;
    };
    if to.field < selector.from.field {
        return true;
    }
    if to.field == selector.from.field {
        return to.char != 0 && to.char < selector.from.char;
    }
    false
}
fn key_spans_multiple_fields(selector: &FieldSelector) -> bool {
    if !matches!(
        selector.settings.mode,
        SortMode::Numeric | SortMode::HumanNumeric | SortMode::GeneralNumeric
    ) {
        return false;
    }
    match &selector.to {
        None => true,
        Some(to) => to.field > selector.from.field,
    }
}
fn key_leading_blanks_significant(selector: &FieldSelector) -> bool {
    selector.settings.mode == SortMode::Default
        && !selector.from.ignore_blanks
        && !selector.settings.ignore_blanks
}
fn emit_debug_warnings(
    settings: &GlobalSettings,
    flags: &GlobalOptionFlags,
    legacy_warnings: &[LegacyKeyWarning],
) {
    if locale_failed_to_set() {
        show_error!("{}", translate!("sort-warning-failed-to-set-locale"));
    }
    let (locale, encoding) = i18n::get_collating_locale();
    if matches!(encoding, i18n::UEncoding::Utf8) {
        let locale_as_posix = format!("{}.UTF-8", locale.to_string().replace('-', "_"));
        show_error!(
            "{}",
            translate ! ("sort-warning-sort-rule" , "locale" => locale_as_posix)
        );
    } else {
        show_error!("{}", translate!("sort-warning-simple-byte-comparison"));
    }
    for (key_index, selector) in (1..).zip(settings.selectors.iter()) {
        if let Some(legacy) = legacy_warnings
            .iter()
            .find(|warning| warning.key_index == Some(key_index))
        {
            show_error!(
                "{}",
                translate ! ("sort-warning-obsolescent-key" , "key" => legacy . legacy_key_display () , "replacement" => legacy . replacement_key_display ())
            );
        }
        if key_zero_width(selector) {
            show_error!(
                "{}",
                translate ! ("sort-warning-key-zero-width" , "key" => key_index)
            );
            continue;
        }
        if flags.keys_specified && key_spans_multiple_fields(selector) {
            show_error!(
                "{}",
                translate ! ("sort-warning-key-numeric-spans-fields" , "key" => key_index)
            );
        } else if flags.keys_specified && key_leading_blanks_significant(selector) {
            show_error!(
                "{}",
                translate ! ("sort-warning-leading-blanks-significant" , "key" => key_index)
            );
        }
    }
    let numeric_used = settings.selectors.iter().any(|selector| {
        matches!(
            selector.settings.mode,
            SortMode::Numeric | SortMode::HumanNumeric | SortMode::GeneralNumeric
        )
    });
    let mut suppress_decimal_warning = false;
    if numeric_used {
        if let Some(sep) = settings.separator {
            match sep {
                b'.' => {
                    show_error!(
                        "{}",
                        translate ! ("sort-warning-separator-decimal" , "sep" => ".")
                    );
                    suppress_decimal_warning = true;
                }
                b'-' => {
                    show_error!(
                        "{}",
                        translate ! ("sort-warning-separator-minus" , "sep" => "-")
                    );
                }
                b'+' => {
                    show_error!(
                        "{}",
                        translate ! ("sort-warning-separator-plus" , "sep" => "+")
                    );
                }
                _ => {}
            }
        }
        if !suppress_decimal_warning {
            show_error!("{}", translate!("sort-warning-numbers-use-decimal-point"));
        }
    }
    let uses_reverse = settings
        .selectors
        .iter()
        .any(|selector| selector.settings.reverse);
    let uses_blanks = settings
        .selectors
        .iter()
        .any(|selector| selector.settings.ignore_blanks || selector.from.ignore_blanks);
    let uses_dictionary = settings
        .selectors
        .iter()
        .any(|selector| selector.settings.dictionary_order);
    let uses_case = settings
        .selectors
        .iter()
        .any(|selector| selector.settings.ignore_case);
    let uses_non_printing = settings
        .selectors
        .iter()
        .any(|selector| selector.settings.ignore_non_printing);
    let uses_mode = |mode| {
        settings
            .selectors
            .iter()
            .any(|selector| selector.settings.mode == mode)
    };
    let reverse_unused = flags.reverse && !uses_reverse;
    let last_resort_active =
        settings.mode != SortMode::Random && !settings.stable && !settings.unique;
    let reverse_ignored = reverse_unused && !last_resort_active;
    let reverse_last_resort_warning = reverse_unused && last_resort_active;
    let mut ignored_opts = String::new();
    if flags.ignore_leading_blanks && !uses_blanks {
        ignored_opts.push('b');
    }
    if flags.dictionary_order && !uses_dictionary {
        ignored_opts.push('d');
    }
    if flags.ignore_case && !uses_case {
        ignored_opts.push('f');
    }
    if flags.ignore_non_printing && !uses_non_printing {
        ignored_opts.push('i');
    }
    if flags.mode_general && !uses_mode(SortMode::GeneralNumeric) {
        ignored_opts.push('g');
    }
    if flags.mode_human && !uses_mode(SortMode::HumanNumeric) {
        ignored_opts.push('h');
    }
    if flags.mode_month && !uses_mode(SortMode::Month) {
        ignored_opts.push('M');
    }
    if flags.mode_numeric && !uses_mode(SortMode::Numeric) {
        ignored_opts.push('n');
    }
    if flags.mode_random && !uses_mode(SortMode::Random) {
        ignored_opts.push('R');
    }
    if reverse_ignored {
        ignored_opts.push('r');
    }
    if flags.mode_version && !uses_mode(SortMode::Version) {
        ignored_opts.push('V');
    }
    if ignored_opts.len() == 1 {
        show_error!(
            "{}",
            translate ! ("sort-warning-option-ignored" , "option" => ignored_opts)
        );
    } else if ignored_opts.len() > 1 {
        show_error!(
            "{}",
            translate ! ("sort-warning-options-ignored" , "options" => ignored_opts)
        );
    }
    if reverse_last_resort_warning {
        show_error!("{}", translate!("sort-warning-option-reverse-last-resort"));
    }
}
fn has_conflicting_values<T>(matches: &ArgMatches, id: &str) -> bool
where
    T: Clone + PartialEq + Send + Sync + 'static,
{
    matches.get_many::<T>(id).is_some_and(|mut values| {
        values
            .next()
            .is_some_and(|first| values.any(|value| value != first))
    })
}
#[uucore::main]
#[allow(clippy::cognitive_complexity)]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let mut settings = GlobalSettings {
        numeric_locale: detect_numeric_locale(),
        ..Default::default()
    };
    let args: Vec<OsString> = args.collect();
    let key_args = uucore::diagnostics::capture(&args);
    let args = args.into_iter().map(|x| {
        let as_str = x.to_string_lossy();
        if as_str.starts_with("-t") && as_str.chars().count() > 2 {
            OsString::from(format!("--{}={}", options::SEPARATOR, &as_str[2..]))
        } else {
            x
        }
    });
    let args: Vec<OsString> = args.collect();
    let (processed_args, mut legacy_warnings) = preprocess_legacy_args(args);
    if !legacy_warnings.is_empty() {
        index_legacy_warnings(&processed_args, &mut legacy_warnings);
    }
    let matches =
        uucore::clap_localization::handle_clap_result_with_exit_code(uu_app(), processed_args, 2)?;
    if has_conflicting_values::<OsString>(&matches, options::OUTPUT) {
        return Err(SortError::MultipleOutputFiles.into());
    }
    if has_conflicting_values::<OsString>(&matches, options::SEPARATOR) {
        return Err(SortError::IncompatibleTabs.into());
    }
    settings.debug = matches.get_flag(options::DEBUG);
    if let Some(path) = matches.get_one::<OsString>(options::RANDOM_SOURCE) {
        settings.random_source = Some(PathBuf::from(path));
    }
    let mut files: Vec<OsString> = if matches.contains_id(options::FILES0_FROM) {
        let files0_from: PathBuf = matches
            .get_one::<OsString>(options::FILES0_FROM)
            .map(Into::into)
            .unwrap_or_default();
        if let Some(s) = matches.get_one::<OsString>(options::FILES) {
            return Err(SortError::FileOperandsCombined { file: s.into() }.into());
        }
        let mut files = Vec::new();
        let reader = open_with_open_failed_error(&files0_from)?;
        let buf_reader = BufReader::new(reader);
        for (line_num, line_res) in buf_reader.split(b'\0').enumerate() {
            let line = line_res.map_err(|error| SortError::ReadFailed {
                path: files0_from.clone(),
                error,
            })?;
            if line.as_slice() == STDIN_FILE.as_bytes() {
                return Err(SortError::MinusInStdIn.into());
            }
            if line.is_empty() {
                return Err(SortError::ZeroLengthFileName {
                    file: files0_from,
                    line_num: line_num + 1,
                }
                .into());
            }
            files.push(uucore::os_string_from_vec(line)?);
        }
        if files.is_empty() {
            return Err(SortError::EmptyInputFile { file: files0_from }.into());
        }
        files
    } else {
        matches
            .get_many::<OsString>(options::FILES)
            .map(|v| v.map(ToOwned::to_owned).collect())
            .unwrap_or_default()
    };
    let mut mode_flags = ModeFlags {
        human_numeric: matches.get_flag(options::modes::HUMAN_NUMERIC),
        month: matches.get_flag(options::modes::MONTH),
        general_numeric: matches.get_flag(options::modes::GENERAL_NUMERIC),
        numeric: matches.get_flag(options::modes::NUMERIC),
        version: matches.get_flag(options::modes::VERSION),
        random: matches.get_flag(options::modes::RANDOM),
    };
    if let Some(sort_arg) = matches.get_one::<String>(options::modes::SORT) {
        match sort_arg.as_str() {
            "human-numeric" => mode_flags.human_numeric = true,
            "month" => mode_flags.month = true,
            "general-numeric" => mode_flags.general_numeric = true,
            "numeric" => mode_flags.numeric = true,
            "version" => mode_flags.version = true,
            "random" => mode_flags.random = true,
            _ => {}
        }
    }
    let dictionary_order = matches.get_flag(options::DICTIONARY_ORDER);
    let ignore_non_printing = matches.get_flag(options::IGNORE_NONPRINTING);
    let ignore_case = matches.get_flag(options::IGNORE_CASE);
    if !matches.contains_id(options::KEY)
        && ordering_incompatible(mode_flags, dictionary_order, ignore_non_printing)
    {
        let opts = ordering_opts_string(
            mode_flags,
            dictionary_order,
            ignore_non_printing,
            ignore_case,
        );
        return Err(incompatible_options_error(&opts));
    }
    settings.mode = mode_flags.to_mode();
    if mode_flags.random {
        settings.salt = Some(get_rand_string());
    }
    settings.dictionary_order = dictionary_order;
    settings.ignore_non_printing = ignore_non_printing;
    settings.ignore_case = ignore_case;
    let threads = match matches.get_one::<String>(options::PARALLEL) {
        Some(value) => parse_parallel(value)?,
        None => std::thread::available_parallelism().map_or(1, |n| n.get() as u64),
    };
    #[cfg(not(target_os = "wasi"))]
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(threads as usize)
        .build_global();
    #[cfg(target_os = "wasi")]
    let _ = threads;
    if let Some(size_str) = matches.get_one::<String>(options::BUF_SIZE) {
        settings.buffer_size = GlobalSettings::parse_byte_count(size_str).map_err(|error| {
            let message = format_error_message(&error, size_str, options::BUF_SIZE);
            error.size_value_error(
                key_args.as_deref(),
                &OptionValue::new(size_str, 'S', options::BUF_SIZE),
                0,
                &message,
                USimpleError::new(2, message.clone()),
            )
        })?;
        settings.buffer_size_is_explicit = true;
    } else {
        settings.buffer_size = automatic_buffer_size(&files);
        settings.buffer_size_is_explicit = false;
    }
    let mut tmp_dir = TmpDirWrapper::new(matches.get_one::<String>(options::TMP_DIR).map_or_else(
        || {
            #[cfg(target_os = "wasi")]
            {
                PathBuf::from("/tmp")
            }
            #[cfg(not(target_os = "wasi"))]
            {
                env::temp_dir()
            }
        },
        PathBuf::from,
    ));
    settings.compress_prog = matches
        .get_one::<String>(options::COMPRESS_PROG)
        .map(String::from);
    if let Some(n_merge) = matches.get_one::<String>(options::BATCH_SIZE) {
        let parsed_value = match n_merge.parse::<usize>() {
            Ok(parsed_value) => Some(parsed_value),
            Err(e) if *e.kind() == IntErrorKind::PosOverflow => None,
            Err(_) => {
                return Err(UUsageError::new(
                    2,
                    translate ! ("sort-invalid-batch-size-arg" , "arg" => n_merge),
                ));
            }
        };
        if parsed_value.is_some_and(|value| value < 2) {
            show_error!(
                "{}",
                translate ! ("sort-invalid-batch-size-arg" , "arg" => n_merge)
            );
            return Err(UUsageError::new(
                2,
                translate!("sort-minimum-batch-size-two"),
            ));
        }
        let max_batch_size = max_merge_batch_size();
        let too_large = match (parsed_value, max_batch_size) {
            (None, _) => true,
            (Some(value), Some(max)) => value > max,
            (Some(_), None) => false,
        };
        if too_large {
            let batch_too_large =
                translate ! ("sort-batch-size-too-large" , "arg" => n_merge . quote ());
            let error_message = match max_batch_size {
                Some(max) => {
                    show_error!("{batch_too_large}");
                    translate ! ("sort-maximum-batch-size-rlimit" , "rlimit" => max)
                }
                None => batch_too_large,
            };
            return Err(UUsageError::new(2, error_message));
        }
        settings.merge_batch_size = parsed_value.unwrap_or(usize::MAX);
    }
    settings.line_ending = LineEnding::from_zero_flag(matches.get_flag(options::ZERO_TERMINATED));
    settings.merge = matches.get_flag(options::MERGE);
    settings.check = matches.contains_id(options::check::CHECK);
    if settings.check && matches.get_flag(options::check::CHECK_SILENT) {
        return Err(incompatible_options_error("cC"));
    }
    if matches.get_flag(options::check::CHECK_SILENT)
        || matches!(
            matches
                .get_one::<String>(options::check::CHECK)
                .map(String::as_str),
            Some(options::check::SILENT | options::check::QUIET)
        )
    {
        settings.check_silent = true;
        settings.check = true;
    }
    if matches.contains_id(options::OUTPUT) && settings.check {
        let opts = if settings.check_silent { "Co" } else { "co" };
        return Err(incompatible_options_error(opts));
    }
    settings.ignore_leading_blanks = matches.get_flag(options::IGNORE_LEADING_BLANKS);
    settings.reverse = matches.get_flag(options::REVERSE);
    settings.stable = matches.get_flag(options::STABLE);
    settings.unique = matches.get_flag(options::UNIQUE);
    if files.is_empty() {
        files.push(OsString::from(STDIN_FILE));
    } else if settings.check && files.len() != 1 {
        return Err(UUsageError::new(
            2,
            translate_text ! ("sort-extra-operand-not-allowed-with-c" , "operand" => files [1] . quote ()),
        ));
    }
    if let Some(arg) = matches.get_one::<OsString>(options::SEPARATOR) {
        let mut separator = arg.to_str().ok_or_else(|| {
            UUsageError::new(
                2,
                translate ! ("sort-separator-not-valid-unicode" , "arg" => arg . quote ()),
            )
        })?;
        if separator == "\\0" {
            separator = "\0";
        }
        let &[sep_char] = separator.as_bytes() else {
            return Err(UUsageError::new(
                2,
                translate ! ("sort-separator-must-be-one-char" , "separator" => separator . quote ()),
            ));
        };
        settings.separator = Some(sep_char);
    }
    if let Some(values) = matches.get_many::<String>(options::KEY) {
        for value in values {
            let selector = match FieldSelector::parse(value, &settings) {
                Ok(selector) => selector,
                Err(error) => {
                    return Err(uucore::diagnostics::error_after_report(
                        key_args.as_deref(),
                        error,
                        |args, error| diagnostics::render(args, value, error),
                    ));
                }
            };
            settings.selectors.push(selector);
        }
    }
    if !matches.contains_id(options::KEY) {
        let key_settings = KeySettings::from(&settings);
        settings.selectors.push(FieldSelector::new(
            KeyPosition {
                field: 1,
                char: 1,
                ignore_blanks: key_settings.ignore_blanks,
            },
            None,
            key_settings,
        ));
    }
    let needs_random = settings.mode == SortMode::Random
        || settings
            .selectors
            .iter()
            .any(|selector| selector.settings.mode == SortMode::Random);
    if needs_random {
        settings.salt = Some(match settings.random_source.as_deref() {
            Some(path) => salt_from_random_source(path)?,
            None => get_rand_string(),
        });
    }
    if !(settings.merge || settings.check) {
        check_inputs(&files)?;
    }
    let output = Output::new(matches.get_one::<OsString>(options::OUTPUT))?;
    if settings.debug {
        let global_flags = GlobalOptionFlags::from_matches(&matches);
        emit_debug_warnings(&settings, &global_flags, &legacy_warnings);
    }
    #[cfg(feature = "i18n-collator")]
    let needs_locale_collation = i18n::collator::init_locale_collation();
    #[cfg(not(feature = "i18n-collator"))]
    let needs_locale_collation = false;
    settings.init_precomputed(needs_locale_collation);
    let result = exec(&mut files, &settings, output, &mut tmp_dir);
    tmp_dir.wait_if_signal();
    result
}
pub fn uu_app() -> Command {
    uucore::clap_localization::configure_localized_command(
        Command::new("sort")
            .version(uucore::crate_version!())
            .about(translate!("sort-about"))
            .after_help(translate!("sort-after-help"))
            .override_usage(format_usage(&translate!("sort-usage"))),
    )
    .infer_long_args(true)
    .disable_help_flag(true)
    .disable_version_flag(true)
    .args_override_self(true)
    .arg(
        Arg::new(options::HELP)
            .long(options::HELP)
            .help(translate!("sort-help-help"))
            .action(ArgAction::Help),
    )
    .arg(
        Arg::new(options::VERSION)
            .long(options::VERSION)
            .help(translate!("sort-help-version"))
            .action(ArgAction::Version),
    )
    .arg(
        Arg::new(options::modes::SORT)
            .long(options::modes::SORT)
            .value_parser(ShortcutValueParser::new([
                "general-numeric",
                "human-numeric",
                "month",
                "numeric",
                "version",
                "random",
            ])),
    )
    .arg(make_sort_mode_arg(
        options::modes::HUMAN_NUMERIC,
        'h',
        translate!("sort-help-human-numeric"),
    ))
    .arg(make_sort_mode_arg(
        options::modes::MONTH,
        'M',
        translate!("sort-help-month"),
    ))
    .arg(make_sort_mode_arg(
        options::modes::NUMERIC,
        'n',
        translate!("sort-help-numeric"),
    ))
    .arg(make_sort_mode_arg(
        options::modes::GENERAL_NUMERIC,
        'g',
        translate!("sort-help-general-numeric"),
    ))
    .arg(make_sort_mode_arg(
        options::modes::VERSION,
        'V',
        translate!("sort-help-version-sort"),
    ))
    .arg(make_sort_mode_arg(
        options::modes::RANDOM,
        'R',
        translate!("sort-help-random"),
    ))
    .arg(
        Arg::new(options::RANDOM_SOURCE)
            .long(options::RANDOM_SOURCE)
            .help(translate!("sort-help-random-source"))
            .value_name("FILE")
            .value_parser(ValueParser::os_string())
            .value_hint(clap::ValueHint::FilePath),
    )
    .arg(
        Arg::new(options::DICTIONARY_ORDER)
            .short('d')
            .long(options::DICTIONARY_ORDER)
            .help(translate!("sort-help-dictionary-order"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::MERGE)
            .short('m')
            .long(options::MERGE)
            .help(translate!("sort-help-merge"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::check::CHECK)
            .short('c')
            .long(options::check::CHECK)
            .require_equals(true)
            .num_args(0..)
            .value_parser(ShortcutValueParser::new([
                options::check::SILENT,
                options::check::QUIET,
                options::check::DIAGNOSE_FIRST,
            ]))
            .help(translate!("sort-help-check")),
    )
    .arg(
        Arg::new(options::check::CHECK_SILENT)
            .short('C')
            .long(options::check::CHECK_SILENT)
            .help(translate!("sort-help-check-silent"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::IGNORE_CASE)
            .short('f')
            .long(options::IGNORE_CASE)
            .help(translate!("sort-help-ignore-case"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::IGNORE_NONPRINTING)
            .short('i')
            .long(options::IGNORE_NONPRINTING)
            .help(translate!("sort-help-ignore-nonprinting"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::IGNORE_LEADING_BLANKS)
            .short('b')
            .long(options::IGNORE_LEADING_BLANKS)
            .help(translate!("sort-help-ignore-leading-blanks"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::OUTPUT)
            .short('o')
            .long(options::OUTPUT)
            .help(translate!("sort-help-output"))
            .value_parser(ValueParser::os_string())
            .value_name("FILENAME")
            .value_hint(clap::ValueHint::FilePath)
            .num_args(1)
            .allow_hyphen_values(true)
            .action(ArgAction::Append),
    )
    .arg(
        Arg::new(options::REVERSE)
            .short('r')
            .long(options::REVERSE)
            .help(translate!("sort-help-reverse"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::STABLE)
            .short('s')
            .long(options::STABLE)
            .help(translate!("sort-help-stable"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::UNIQUE)
            .short('u')
            .long(options::UNIQUE)
            .help(translate!("sort-help-unique"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::KEY)
            .short('k')
            .long(options::KEY)
            .help(translate!("sort-help-key"))
            .action(ArgAction::Append)
            .num_args(1),
    )
    .arg(
        Arg::new(options::SEPARATOR)
            .short('t')
            .long(options::SEPARATOR)
            .help(translate!("sort-help-separator"))
            .value_parser(ValueParser::os_string())
            .action(ArgAction::Append),
    )
    .arg(
        Arg::new(options::ZERO_TERMINATED)
            .short('z')
            .long(options::ZERO_TERMINATED)
            .help(translate!("sort-help-zero-terminated"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::PARALLEL)
            .long(options::PARALLEL)
            .help(translate!("sort-help-parallel"))
            .allow_hyphen_values(true)
            .value_name("NUM_THREADS"),
    )
    .arg(
        Arg::new(options::BUF_SIZE)
            .short('S')
            .long(options::BUF_SIZE)
            .help(translate!("sort-help-buf-size"))
            .value_name("SIZE"),
    )
    .arg(
        Arg::new(options::TMP_DIR)
            .short('T')
            .long(options::TMP_DIR)
            .help(translate!("sort-help-tmp-dir"))
            .value_name("DIR")
            .value_hint(clap::ValueHint::DirPath),
    )
    .arg(
        Arg::new(options::COMPRESS_PROG)
            .long(options::COMPRESS_PROG)
            .help(translate!("sort-help-compress-prog"))
            .value_name("PROG")
            .value_hint(clap::ValueHint::CommandName),
    )
    .arg(
        Arg::new(options::BATCH_SIZE)
            .long(options::BATCH_SIZE)
            .help(translate!("sort-help-batch-size"))
            .value_name("N_MERGE"),
    )
    .arg(
        Arg::new(options::FILES0_FROM)
            .long(options::FILES0_FROM)
            .help(translate!("sort-help-files0-from"))
            .value_name("NUL_FILE")
            .value_parser(ValueParser::os_string())
            .value_hint(clap::ValueHint::FilePath),
    )
    .arg(
        Arg::new(options::DEBUG)
            .long(options::DEBUG)
            .help(translate!("sort-help-debug"))
            .action(ArgAction::SetTrue),
    )
    .arg(
        Arg::new(options::FILES)
            .action(ArgAction::Append)
            .value_parser(ValueParser::os_string())
            .value_hint(clap::ValueHint::FilePath),
    )
}
fn exec(
    files: &mut [OsString],
    settings: &GlobalSettings,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    if settings.check {
        if files.len() > 1 {
            Err(UUsageError::new(
                2,
                translate!("sort-only-one-file-allowed-with-c"),
            ))
        } else {
            check::check(files.first().unwrap(), settings).map_err(Into::into)
        }
    } else if settings.merge {
        merge::merge(files, settings, output, tmp_dir).map_err(Into::into)
    } else {
        let mut lines = files.iter().map(open).map(|file| file.map_err(Into::into));
        ext_sort(&mut lines, settings, output, tmp_dir).map_err(Into::into)
    }
}
pub struct SortComparator<'s, 'a> {
    pub settings: &'s GlobalSettings,
    pub line_data: &'s LineData<'a>,
}
impl<'s, 'a> crate::proof::unwind::Comparator<Line<'a>> for SortComparator<'s, 'a> {
    fn compare(&self, a: &Line<'a>, b: &Line<'a>) -> Ordering {
        compare_by(a, b, self.settings, self.line_data, self.line_data)
    }
}
fn sort_by<'a>(unsorted: &mut Vec<Line<'a>>, settings: &GlobalSettings, line_data: &LineData<'a>) {
    let cmp = SortComparator {
        settings,
        line_data,
    };
    if settings.stable || settings.unique {
        crate::trusted::unwind::sort_values(unsorted, true, &cmp);
    } else {
        crate::trusted::unwind::sort_values(unsorted, false, &cmp);
    }
}
#[inline]
pub fn merge_compare<'a>(
    a: &Line<'a>,
    b: &Line<'a>,
    settings: &GlobalSettings,
    a_line_data: &LineData<'a>,
    b_line_data: &LineData<'a>,
) -> Ordering {
    #[cfg(feature = "i18n-collator")]
    if settings.precomputed.fast_locale_collation {
        return compare_lines_with_collator(a, b, settings);
    }
    compare_by(a, b, settings, a_line_data, b_line_data)
}
#[cfg(feature = "i18n-collator")]
#[inline(never)]
fn compare_lines_with_collator(a: &Line<'_>, b: &Line<'_>, settings: &GlobalSettings) -> Ordering {
    let mut cmp = locale_cmp(a.line, b.line);
    if cmp == Ordering::Equal {
        cmp = b.line.cmp(a.line);
    }
    if settings.reverse { cmp.reverse() } else { cmp }
}
fn compare_by<'a>(
    a: &Line<'a>,
    b: &Line<'a>,
    global_settings: &GlobalSettings,
    a_line_data: &LineData<'a>,
    b_line_data: &LineData<'a>,
) -> Ordering {
    if global_settings.precomputed.fast_lexicographic {
        let cmp = crate::trusted::compare_byte_slices(a.line, b.line);
        return if global_settings.reverse {
            cmp.reverse()
        } else {
            cmp
        };
    }
    #[cfg(feature = "i18n-collator")]
    if global_settings.precomputed.fast_locale_collation {
        let a_key = a_line_data.collation_key(a.index);
        let b_key = b_line_data.collation_key(b.index);
        let mut cmp = a_key.cmp(b_key);
        if cmp == Ordering::Equal {
            cmp = b.line.cmp(a.line);
        }
        return if global_settings.reverse {
            cmp.reverse()
        } else {
            cmp
        };
    }
    if global_settings.precomputed.fast_ascii_insensitive {
        let cmp = ascii_case_insensitive_cmp(a.line, b.line);
        if !matches!(cmp, Ordering::Equal) || {
            { crate::trusted::comparisons::equal_bytes(a.line, b.line) }
        } {
            return if global_settings.reverse {
                cmp.reverse()
            } else {
                cmp
            };
        }
    }
    let mut selection_index = 0;
    let mut num_info_index = 0;
    let mut parsed_float_index = 0;
    let hints = (
        crate::trusted::comparisons::vec_get(&a_line_data.line_num_floats, a.index),
        crate::trusted::comparisons::vec_get(&b_line_data.line_num_floats, b.index),
    );
    if let (Some(Some(a_f64)), Some(Some(b_f64))) = hints {
        let float_order = crate::trusted::comparisons::float_partial_cmp(a_f64, b_f64);
        if let Some(cmp) = float_order {
            if !matches!(cmp, Ordering::Equal) || {
                { crate::trusted::comparisons::equal_bytes(a.line, b.line) }
            } {
                return if global_settings.reverse {
                    cmp.reverse()
                } else {
                    cmp
                };
            }
        }
    }
    let mut selectors_iter = crate::trusted::comparisons::vec_refs(&global_settings.selectors);
    let mut selector_index = 0usize;
    while let Some(selector) = selectors_iter.next() {
        let (a_str, b_str) = if selector.needs_selection {
            let selections = (
                *crate::trusted::comparisons::vec_at(
                    &a_line_data.selections,
                    a.index * global_settings.precomputed.selections_per_line + selection_index,
                ),
                *crate::trusted::comparisons::vec_at(
                    &b_line_data.selections,
                    b.index * global_settings.precomputed.selections_per_line + selection_index,
                ),
            );
            selection_index += 1;
            selections
        } else {
            (a.line, b.line)
        };
        let settings = &selector.settings;
        let cmp: Ordering = match settings.mode {
            SortMode::Numeric => {
                let a_num_info = crate::trusted::comparisons::vec_at(
                    &a_line_data.num_infos,
                    a.index * global_settings.precomputed.num_infos_per_line + num_info_index,
                );
                let b_num_info = crate::trusted::comparisons::vec_at(
                    &b_line_data.num_infos,
                    b.index * global_settings.precomputed.num_infos_per_line + num_info_index,
                );
                num_info_index += 1;
                numeric_str_cmp((a_str, a_num_info), (b_str, b_num_info))
            }
            SortMode::HumanNumeric => {
                let a_num_info = crate::trusted::comparisons::vec_at(
                    &a_line_data.num_infos,
                    a.index * global_settings.precomputed.num_infos_per_line + num_info_index,
                );
                let b_num_info = crate::trusted::comparisons::vec_at(
                    &b_line_data.num_infos,
                    b.index * global_settings.precomputed.num_infos_per_line + num_info_index,
                );
                num_info_index += 1;
                human_numeric_str_cmp((a_str, a_num_info), (b_str, b_num_info))
            }
            SortMode::GeneralNumeric => {
                let a_float = crate::trusted::comparisons::vec_at(
                    &a_line_data.parsed_floats,
                    a.index * global_settings.precomputed.floats_per_line + parsed_float_index,
                );
                let b_float = crate::trusted::comparisons::vec_at(
                    &b_line_data.parsed_floats,
                    b.index * global_settings.precomputed.floats_per_line + parsed_float_index,
                );
                parsed_float_index += 1;
                general_numeric_compare(a_float, b_float)
            }
            SortMode::Month => month_compare(a_str, b_str),
            SortMode::Version | SortMode::Random => Ordering::Equal,
            SortMode::Default => {
                #[cfg(feature = "i18n-collator")]
                {
                    if settings.ignore_case
                        || settings.dictionary_order
                        || settings.ignore_non_printing
                    {
                        custom_str_cmp(
                            a_str,
                            b_str,
                            settings.ignore_non_printing,
                            settings.dictionary_order,
                            settings.ignore_case,
                        )
                    } else {
                        locale_cmp(a_str, b_str)
                    }
                }
                #[cfg(not(feature = "i18n-collator"))]
                {
                    custom_str_cmp(
                        a_str,
                        b_str,
                        settings.ignore_non_printing,
                        settings.dictionary_order,
                        settings.ignore_case,
                    )
                }
            }
        };
        if !matches!(cmp, Ordering::Equal) {
            return if settings.reverse { cmp.reverse() } else { cmp };
        }
        {
            selector_index += 1;
        }
    }
    let cmp = if matches!(global_settings.mode, SortMode::Random)
        || global_settings.stable
        || global_settings.unique
    {
        Ordering::Equal
    } else {
        { crate::trusted::compare_byte_slices(a.line, b.line) }
    };
    if global_settings.reverse {
        cmp.reverse()
    } else {
        cmp
    }
}
#[inline]
fn fold(byte: u8) -> u8 {
    byte.to_ascii_uppercase()
}
fn ascii_case_insensitive_cmp(a: &[u8], b: &[u8]) -> Ordering {
    {
        let a_len = crate::trusted::comparisons::slice_len(a);
        let b_len = crate::trusted::comparisons::slice_len(b);
        let mut index = 0usize;
        while index < a_len && index < b_len {
            let l = fold(*crate::trusted::comparisons::slice_at(a, index));
            let r = fold(*crate::trusted::comparisons::slice_at(b, index));
            if l != r {
                return crate::trusted::comparisons::cmp_u8(l, r);
            }
            index += 1;
        }
        crate::trusted::comparisons::cmp_usize(a_len, b_len)
    }
}
#[allow(clippy::cognitive_complexity)]
fn get_leading_gen(inp: &[u8], decimal_pt: u8) -> Range<usize> {
    let allowed_prefixes: &[&[u8]] = &[
        &[b'i', b'n', b'f'],
        &[b'-', b'i', b'n', b'f'],
        &[b'n', b'a', b'n'],
    ];
    let trimmed = crate::trusted::comparisons::trim_ascii_start(inp);
    let leading_whitespace_len = inp.len() - trimmed.len();
    for allowed_prefix_ref in allowed_prefixes {
        let allowed_prefix = *allowed_prefix_ref;
        let matches = trimmed.len() >= allowed_prefix.len()
            && crate::trusted::comparisons::equal_folded(
                &trimmed[..allowed_prefix.len()],
                allowed_prefix,
            );
        if matches {
            return leading_whitespace_len..(leading_whitespace_len + allowed_prefix.len());
        }
    }
    let mut char_indices = crate::trusted::comparisons::indexed_peek(trimmed);
    let first = char_indices.peek();
    if matches!(first, Some((_, b'-' | b'+'))) {
        char_indices.next();
    }
    let mut had_e_notation = false;
    let mut had_decimal_pt = false;
    let mut had_hex_notation: bool = false;
    while let Some((idx, c_ref)) = char_indices.next() {
        let c = *c_ref;
        if had_hex_notation && c.is_ascii_hexdigit() {
            continue;
        }
        if c.is_ascii_digit() {
            if c == b'0' && matches!(char_indices.peek(), Some((_, b'x' | b'X'))) {
                had_hex_notation = true;
                char_indices.next();
            }
            continue;
        }
        if c == decimal_pt && !had_decimal_pt && !had_e_notation {
            had_decimal_pt = true;
            continue;
        }
        let is_decimal_e = (c == b'e' || c == b'E') && !had_hex_notation;
        let is_hex_e = (c == b'p' || c == b'P') && had_hex_notation;
        if (is_decimal_e || is_hex_e) && !had_e_notation {
            if let Some(next) = char_indices.peek() {
                let next_char = *next.1;
                if (next_char == b'+' || next_char == b'-')
                    && matches ! (char_indices . peek_nth (1) , Some ((_ , c)) if c . is_ascii_digit ())
                {
                    char_indices.next();
                    had_e_notation = true;
                    continue;
                }
                if next_char.is_ascii_digit() {
                    had_e_notation = true;
                    continue;
                }
            }
        }
        return leading_whitespace_len..(leading_whitespace_len + idx);
    }
    leading_whitespace_len..inp.len()
}
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum GeneralBigDecimalParseResult {
    Invalid,
    Nan,
    MinusInfinity,
    Number(BigDecimal),
    Infinity,
}
#[inline(always)]
fn general_bd_parse(a: &[u8], decimal_pt: u8) -> GeneralBigDecimalParseResult {
    let parsed_bytes = crate::trusted::comparisons::replace_decimal(a, decimal_pt);
    let input = match &parsed_bytes {
        Some(bytes) => &bytes[..],
        None => a,
    };
    let decoded = crate::trusted::comparisons::utf8(input);
    let Ok(a) = decoded else {
        return GeneralBigDecimalParseResult::Invalid;
    };
    let ebd = match ExtendedBigDecimal::extended_parse(a) {
        Err(ExtendedParserError::NotNumeric) => return GeneralBigDecimalParseResult::Invalid,
        Err(
            ExtendedParserError::PartialMatch(ebd, _)
            | ExtendedParserError::Overflow(ebd)
            | ExtendedParserError::Underflow(ebd),
        )
        | Ok(ebd) => ebd,
    };
    match ebd {
        ExtendedBigDecimal::BigDecimal(bd) => GeneralBigDecimalParseResult::Number(bd),
        ExtendedBigDecimal::Infinity => GeneralBigDecimalParseResult::Infinity,
        ExtendedBigDecimal::MinusInfinity => GeneralBigDecimalParseResult::MinusInfinity,
        ExtendedBigDecimal::MinusZero => GeneralBigDecimalParseResult::Number(0.into()),
        ExtendedBigDecimal::Nan | ExtendedBigDecimal::MinusNan => GeneralBigDecimalParseResult::Nan,
    }
}
fn general_numeric_compare(
    a: &GeneralBigDecimalParseResult,
    b: &GeneralBigDecimalParseResult,
) -> Ordering {
    {
        crate::trusted::comparisons::unwrap_order(crate::trusted::comparisons::derived_general_cmp(
            a, b,
        ))
    }
}
fn get_rand_string() -> [u8; SALT_LEN] {
    rng().sample(rand::distr::StandardUniform)
}
const SALT_LEN: usize = 16;
const MAX_BYTES: usize = 1024 * 1024;
const BUF_LEN: usize = 8192;
const U64_LEN: usize = 8;
const RANDOM_SOURCE_TAG: &'static [u8] = b"uutils-sort-random-source";
fn salt_from_random_source(path: &Path) -> UResult<[u8; SALT_LEN]> {
    let mut reader = open_with_open_failed_error(path)?;
    let mut buf = [0u8; BUF_LEN];
    let mut total = 0usize;
    let mut hasher = FoldHasher::with_seed(1, SharedSeed::global_fixed());
    while let n @ 1.. = reader
        .read(&mut buf)
        .map_err(|error| SortError::ReadFailed {
            path: path.to_owned(),
            error,
        })?
        && let remaining @ 1.. = MAX_BYTES.saturating_sub(total)
    {
        let take = n.min(remaining);
        hasher.write(&buf[..take]);
        total = total.saturating_add(take);
        if take < n {
            break;
        }
    }
    if total < SALT_LEN {
        return Err(SortError::RandomSourceEndOfFile {
            path: path.to_owned(),
        }
        .into());
    }
    let first = hasher.finish();
    let mut second_hasher = FoldHasher::with_seed(2, SharedSeed::global_fixed());
    second_hasher.write(RANDOM_SOURCE_TAG);
    second_hasher.write_u64(first);
    let second = second_hasher.finish();
    let mut out = [0u8; SALT_LEN];
    out[..U64_LEN].copy_from_slice(&first.to_le_bytes());
    out[U64_LEN..].copy_from_slice(&second.to_le_bytes());
    Ok(out)
}
fn get_hash<T: Hash>(t: &T) -> u64 {
    let mut s = FoldHasher::with_seed(0, SharedSeed::global_fixed());
    t.hash(&mut s);
    s.finish()
}
fn random_shuffle(a: &[u8], b: &[u8], salt: &[u8]) -> Ordering {
    let da = get_hash(&(a, salt));
    let db = get_hash(&(b, salt));
    da.cmp(&db)
}
#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Copy)]
pub enum Month {
    Unknown,
    January,
    February,
    March,
    April,
    May,
    June,
    July,
    August,
    September,
    October,
    November,
    December,
}
pub type MonthTable = Vec<(Vec<u8>, Month)>;
pub struct MonthTableFactory {}
impl crate::trusted::comparisons::MonthInitializer for MonthTableFactory {
    fn initialize(&self) -> Option<MonthTable> {
        init_month_table()
    }
}
fn get_locale_month_table() -> Option<&'static MonthTable> {
    { crate::trusted::comparisons::cached_none_months(MonthTableFactory {}) }
}
fn init_month_table() -> Option<MonthTable> {
    let months = match get_locale_months() {
        Some(months) => months,
        None => return None,
    };
    let all_months = [
        Month::January,
        Month::February,
        Month::March,
        Month::April,
        Month::May,
        Month::June,
        Month::July,
        Month::August,
        Month::September,
        Month::October,
        Month::November,
        Month::December,
    ];
    let table = crate::trusted::comparisons::month_pairs(months, &all_months);
    Some(table)
}
use crate::trusted::comparisons::equal_vec_array as trusted_month_equal;
fn month_parse(line: &[u8]) -> (Month, usize) {
    let mut line = line;
    while {
        {
            crate::trusted::comparisons::slice_len(line) > 0
                && is_blank(*crate::trusted::comparisons::slice_at(line, 0))
        }
    } {
        {
            line = crate::trusted::comparisons::slice_from(line, 1);
        }
    }
    if let Some(table) = get_locale_month_table() {}
    let prefix = crate::trusted::comparisons::upper_prefix(line, 3);
    match &prefix {
        Some(name) if crate::trusted_month_equal(name, &[b'J', b'A', b'N']) => (Month::January, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'F', b'E', b'B']) => (Month::February, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'M', b'A', b'R']) => (Month::March, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'A', b'P', b'R']) => (Month::April, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'M', b'A', b'Y']) => (Month::May, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'J', b'U', b'N']) => (Month::June, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'J', b'U', b'L']) => (Month::July, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'A', b'U', b'G']) => (Month::August, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'S', b'E', b'P']) => {
            (Month::September, 3)
        }
        Some(name) if crate::trusted_month_equal(name, &[b'O', b'C', b'T']) => (Month::October, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'N', b'O', b'V']) => (Month::November, 3),
        Some(name) if crate::trusted_month_equal(name, &[b'D', b'E', b'C']) => (Month::December, 3),
        _ => (Month::Unknown, 0),
    }
}
fn month_compare(a: &[u8], b: &[u8]) -> Ordering {
    let ma = month_parse(a).0;
    let mb = month_parse(b).0;
    { crate::trusted::comparisons::cmp_month(&ma, &mb) }
}
fn print_sorted<'a, T: Iterator<Item = &'a Line<'a>>>(
    iter: T,
    settings: &GlobalSettings,
    output: Output,
) -> SortResult<()> {
    let mut writer = crate::trusted::output_writer(output)?;
    for line in iter {
        line.write(&mut writer, settings)?;
    }
    crate::trusted::flush_output(&mut writer)?;
    Ok(())
}
fn check_inputs(files: &[OsString]) -> UResult<()> {
    for file in files {
        if file == STDIN_FILE {
            continue;
        }
        let path = Path::new(file);
        check_readable(path).map_err(|error| SortError::ReadFailed {
            path: path.to_owned(),
            error,
        })?;
    }
    Ok(())
}
#[cfg(all(unix, not(target_os = "redox")))]
fn check_readable(path: &Path) -> std::io::Result<()> {
    use rustix::fs::{Access, access};
    access(path, Access::READ_OK).map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
}
#[cfg(any(not(unix), target_os = "redox"))]
fn check_readable(path: &Path) -> std::io::Result<()> {
    File::open(path)?;
    Ok(())
}
fn open(path: impl AsRef<OsStr>) -> UResult<InputReader> {
    let path = path.as_ref();
    if path == STDIN_FILE {
        let stdin = stdin();
        return Ok(boxed_reader(stdin));
    }
    let path = Path::new(path);
    match File::open(path) {
        Ok(f) => Ok(boxed_reader(f)),
        Err(error) => Err(SortError::ReadFailed {
            path: path.to_owned(),
            error,
        }
        .into()),
    }
}
fn open_with_open_failed_error(path: impl AsRef<OsStr>) -> UResult<InputReader> {
    let path = path.as_ref();
    if path == STDIN_FILE {
        let stdin = stdin();
        return Ok(boxed_reader(stdin));
    }
    let path = Path::new(path);
    match File::open(path) {
        Ok(f) => Ok(boxed_reader(f)),
        Err(error) => Err(SortError::OpenFailed {
            path: path.to_owned(),
            error,
        }
        .into()),
    }
}
fn parse_parallel(value: &str) -> UResult<u64> {
    let digits = value.strip_prefix('+').unwrap_or(value);
    let invalid = |key: &str| {
        USimpleError::new(
            2,
            translate ! (key , "option" => options :: PARALLEL , "arg" => value . quote ()),
        )
    };
    if !digits.starts_with(|c: char| c.is_ascii_digit()) {
        return Err(invalid("sort-invalid-option-arg"));
    }
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(invalid("sort-invalid-suffix-in-option-arg"));
    }
    match digits.parse::<u64>() {
        Ok(0) => Err(USimpleError::new(
            2,
            translate!("sort-parallel-must-be-nonzero"),
        )),
        Ok(threads) => Ok(threads),
        Err(_) => Err(invalid("sort-option-arg-too-large")),
    }
}
fn format_error_message(error: &ParseSizeError, s: &str, option: &str) -> String {
    match error {
        ParseSizeError::InvalidSuffix(_) => {
            translate ! ("sort-invalid-suffix-in-option-arg" , "option" => option , "arg" => s . quote ())
        }
        ParseSizeError::ParseFailure(_) | ParseSizeError::PhysicalMem(_) => {
            translate ! ("sort-invalid-option-arg" , "option" => option , "arg" => s . quote ())
        }
        ParseSizeError::SizeTooBig(_) => {
            translate ! ("sort-option-arg-too-large" , "option" => option , "arg" => s . quote ())
        }
    }
}
