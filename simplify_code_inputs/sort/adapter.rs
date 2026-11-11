use super::*;
use crate::args::{Args, Mode as InputMode, OrderingOptions, SortOptions};
use crate::proof_common::State;
#[cfg(verus_keep_ghost)]
use crate::proof_common::ready;
use vstd::prelude::*;

fn native_mode(mode: InputMode) -> SortMode {
    match mode {
        InputMode::Text => SortMode::Default,
        InputMode::Numeric => SortMode::Numeric,
        InputMode::HumanNumeric => SortMode::HumanNumeric,
        InputMode::GeneralNumeric => SortMode::GeneralNumeric,
        InputMode::Month => SortMode::Month,
    }
}

fn native_key_settings(options: &OrderingOptions) -> KeySettings {
    KeySettings {
        mode: native_mode(options.mode), ignore_blanks: options.ignore_blanks,
        ignore_case: options.ignore_case, dictionary_order: options.dictionary,
        ignore_non_printing: options.ignore_nonprinting, reverse: options.reverse,
    }
}

fn native_settings(options: &SortOptions) -> GlobalSettings {
    let global = &options.ordering;
    let mut settings = GlobalSettings {
        mode: native_mode(global.mode), ignore_leading_blanks: global.ignore_blanks,
        ignore_case: global.ignore_case, dictionary_order: global.dictionary,
        ignore_non_printing: global.ignore_nonprinting, reverse: global.reverse,
        stable: options.stable, unique: options.unique, salt: Some(options.random_salt),
        separator: options.separator,
        line_ending: LineEnding::from_zero_flag(options.zero_terminated),
        debug: false, merge: false, check: false, check_silent: false,
        random_source: None, selectors: Vec::new(), compress_prog: None,
        buffer_size: FALLBACK_AUTOMATIC_BUF_SIZE, buffer_size_is_explicit: false,
        merge_batch_size: default_merge_batch_size(),
        numeric_locale: NumericLocaleSettings { thousands_sep: None, decimal_pt: Some(b'.') },
        precomputed: Precomputed::default(),
    };
    if options.keys.is_empty() {
        settings.selectors.push(FieldSelector::new(
            KeyPosition { field: 1, char: 1, ignore_blanks: global.ignore_blanks },
            None, native_key_settings(global)));
    } else {
        for key in &options.keys {
            let from = KeyPosition {
                field: key.start.field.saturating_add(1), char: key.start.offset.saturating_add(1),
                ignore_blanks: key.start.skip_blanks,
            };
            let to = key.end.as_ref().map(|end| KeyPosition {
                field: end.field.saturating_add(1),
                char: match end.offset { None => 0, Some(offset) => offset.saturating_add(1) },
                ignore_blanks: end.skip_blanks,
            });
            settings.selectors.push(FieldSelector::new(from, to, native_key_settings(&key.ordering)));
        }
    }
    settings.init_precomputed(false);
    settings
}

#[cfg_attr(verus_keep_ghost, verus_spec(with state: &mut Ghost<State>,))]
fn run_inputs(inputs: &[Vec<u8>], options: &SortOptions, initial_output: &Vec<u8>) -> Vec<u8> {
    use std::io::Seek;
    rayon::current_num_threads();
    let settings = native_settings(options);
    let empty = Vec::new();
    let inputs = if inputs.is_empty() { std::slice::from_ref(&empty) } else { inputs };
    let mut capture = tempfile::tempfile().unwrap();
    let output = Output { file: Some(("sort-capture".into(), capture.try_clone().unwrap())) };
    let mut directory = tmp_dir::TmpDirWrapper::new(std::env::temp_dir());
    let readers = super::trusted::memory_readers(inputs);
    let mut files = readers.into_iter();
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let result = ext_sort::ext_sort(&mut files, &settings, output, &mut directory);
    result.unwrap();
    capture.rewind().unwrap();
    let mut bytes = Vec::new();
    capture.read_to_end(&mut bytes).unwrap();
    let mut result = initial_output.clone();
    result.extend_from_slice(&bytes);
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(with state: &mut Ghost<State>,))]
fn read_file(name: &std::ffi::OsString) -> Vec<u8> {
    let bytes = std::fs::read(name).unwrap();
    #[cfg(verus_keep_ghost)]
    proof! {
        let ghost before = state@;
        let ghost path = crate::filesystem::os_bytes(name);
        before.open_valid(path, 3);
        let ghost opened = before.open_file(path, 3);
        opened.advance_valid(3, bytes.len() as nat);
        let ghost consumed = opened.advance(3, bytes.len() as nat);
        assert(crate::trusted_common::fd::read(opened, consumed, 3, bytes.len() as nat, bytes@));
        consumed.close_valid(3);
        *state = Ghost(consumed.close_file(3));
    }
    bytes
}

verus! {
pub fn run(args: &Args, stdin: &[u8], stdout: &Vec<u8>, state: &mut Ghost<State>) -> Vec<u8>
    requires ready(args, stdin@, stdout@, old(state)@),
{
    #[cfg(verus_keep_ghost)]
    let mut reader = crate::trusted_common::io::reader(stdin);
    #[cfg(not(verus_keep_ghost))]
    let mut reader = stdin;
    let mut inputs = Vec::new();
    if args.filenames.is_empty() {
        #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
        let result = crate::trusted_common::io::read_all_state(&mut reader);
        inputs.push(result.unwrap());
    } else {
        for name in &args.filenames {
            let bytes = if name == "-" {
                #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
                let result = crate::trusted_common::io::read_all_state(&mut reader);
                result.unwrap()
            } else {
                #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
                let bytes = read_file(name);
                bytes
            };
            inputs.push(bytes);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let output = run_inputs(&inputs, &args.options, stdout);
    #[cfg(verus_keep_ghost)]
    proof {
        assert(state@.valid());
        assert(state@.remaining(0) == reader@);
        assert(state@.output() == output@);
    }
    output
}
}
