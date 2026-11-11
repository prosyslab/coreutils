// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::cell::{OnceCell, RefCell};
use std::ffi::OsString;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Stdin, Write, stdin, stdout};
use std::iter::Cycle;
use std::rc::Rc;
use std::slice::Iter;
use uucore::i18n::charmap::mb_char_len;
use uucore::line_ending::LineEnding;
type UResult<T> = std::io::Result<T>;
use crate::paste_trusted;
#[allow(clippy::cognitive_complexity)]
pub(crate) fn paste(
    filenames: Vec<OsString>,
    serial: bool,
    delimiters: &OsString,
    line_ending: LineEnding,
) -> UResult<()> {
    let unescaped_and_encoded_delimiters = parse_delimiters(delimiters)?;
    let mut input_source_vec = open_inputs(filenames)?;
    let line_ending_byte = u8::from(line_ending);
    let input_source_vec_len = input_source_vec.len();
    let mut stdout = paste_trusted::lock_stdout(&stdout());
    if !serial && input_source_vec_len == 1 {
        return {
            write_single_input_source(
                &mut stdout,
                input_source_vec
                    .pop()
                    .expect("input_source_vec_len was checked to be exactly one"),
                line_ending_byte,
            )
        };
    }
    let line_ending_byte_array_ref = &[line_ending_byte];
    let mut delimiter_state = DelimiterState::new(&unescaped_and_encoded_delimiters);
    let mut output = Vec::new();
    if serial {
        for i in 0..input_source_vec_len {
            let input_source = &mut input_source_vec[i];
            output.clear();
            while let read @ 1.. = { input_source.read_until(line_ending_byte, &mut output)? } {
                remove_trailing_line_ending_byte(line_ending_byte, read, &mut output);
                delimiter_state.write_delimiter(&mut output);
            }
            delimiter_state.remove_trailing_delimiter(&mut output);
            paste_trusted::write_all(&mut stdout, &output)?;
            paste_trusted::write_all(&mut stdout, line_ending_byte_array_ref)?;
            delimiter_state.reset_to_first_delimiter();
        }
    } else {
        let mut eof = vec![false; input_source_vec_len];
        loop {
            output.clear();
            let mut eof_count = 0;
            for i in 0..input_source_vec_len {
                let input_source = &mut input_source_vec[i];
                if eof[i] {
                    eof_count += 1;
                } else {
                    match { input_source.read_until(line_ending_byte, &mut output)? } {
                        0 => {
                            eof[i] = true;
                            eof_count += 1;
                        }
                        read => {
                            remove_trailing_line_ending_byte(line_ending_byte, read, &mut output);
                        }
                    }
                }
                delimiter_state.write_delimiter(&mut output);
            }
            if eof_count == input_source_vec_len {
                break;
            }
            delimiter_state.remove_trailing_delimiter(&mut output);
            paste_trusted::write_all(&mut stdout, &output)?;
            paste_trusted::write_all(&mut stdout, line_ending_byte_array_ref)?;
            delimiter_state.reset_to_first_delimiter();
        }
    }
    Ok(())
}
pub(crate) fn open_inputs(filenames: Vec<OsString>) -> UResult<Vec<InputSource>> {
    let stdin_once_cell = paste_trusted::library::new_cache::<Rc<RefCell<Stdin>>>();
    let mut input_source_vec = Vec::with_capacity(filenames.len());
    for _index in 0..filenames.len() {
        let filename = &filenames[_index];
        let input_source = if paste_trusted::filename_is_stdin(&filename) {
            let shared = {
                let init = || -> Rc<RefCell<Stdin>> {
                    let handle = paste_trusted::library::stdin_handle();
                    Rc::new(RefCell::new(handle))
                };
                let value = paste_trusted::library::cached(&stdin_once_cell, init);
                paste_trusted::library::clone_rc(value)
            };
            InputSource::StandardInput(shared)
        } else {
            let file = paste_trusted::library::open_file(&filename)?;
            let reader = paste_trusted::library::buffered(file);
            InputSource::File(reader)
        };
        input_source_vec.push(input_source);
    }
    Ok(input_source_vec)
}
fn write_single_input_source(
    writer: &mut impl Write,
    mut input_source: InputSource,
    line_ending_byte: u8,
) -> UResult<()> {
    let mut buffer = [0_u8; 8 * 1024];
    let mut has_data = false;
    let mut last_byte = line_ending_byte;
    while let bytes_read @ 1.. = { input_source.read(&mut buffer)? } {
        has_data = true;
        last_byte = buffer[bytes_read - 1];
        paste_trusted::write_all(writer, &buffer[..bytes_read])?;
    }
    if has_data && last_byte != line_ending_byte {
        paste_trusted::write_all(writer, &[line_ending_byte])?;
    }
    Ok(())
}
pub(crate) fn parse_delimiters(delimiters: &OsString) -> UResult<Box<[Box<[u8]>]>> {
    let bytes = paste_trusted::encoded_bytes(delimiters);
    let mut vec = Vec::<Box<[u8]>>::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i += 1;
            if i >= bytes.len() {
                return Err(paste_trusted::delimiter_error());
            }
            match bytes[i] {
                b'0' => vec.push(paste_trusted::box_bytes(b"")),
                b'\\' => vec.push(paste_trusted::box_byte(b'\\')),
                b'n' => vec.push(paste_trusted::box_byte(b'\n')),
                b't' => vec.push(paste_trusted::box_byte(b'\t')),
                b'b' => vec.push(paste_trusted::box_byte(8)),
                b'f' => vec.push(paste_trusted::box_byte(12)),
                b'r' => vec.push(paste_trusted::box_byte(b'\r')),
                b'v' => vec.push(paste_trusted::box_byte(11)),
                _ => {
                    let remaining = &bytes[i..];
                    let len = paste_trusted::character_length(remaining);
                    vec.push(paste_trusted::box_bytes(&bytes[i..i + len]));
                    i += len;
                    continue;
                }
            }
            i += 1;
        } else {
            let remaining = &bytes[i..];
            let len = paste_trusted::character_length(remaining);
            vec.push(paste_trusted::box_bytes(&bytes[i..i + len]));
            i += len;
        }
    }
    Ok(paste_trusted::boxed_slice(vec))
}
fn remove_trailing_line_ending_byte(line_ending_byte: u8, read: usize, output: &mut Vec<u8>) {
    if paste_trusted::pop_if_eq(output, line_ending_byte).is_none() {
        return;
    }
    if cfg!(windows) && line_ending_byte == b'\n' && read > 1 {
        let _ = paste_trusted::pop_if_eq(output, b'\r');
    }
}
enum DelimiterState<'a> {
    NoDelimiters,
    OneDelimiter(&'a [u8]),
    MultipleDelimiters {
        current_delimiter: &'a [u8],
        delimiters: &'a [Box<[u8]>],
        delimiters_iterator: Cycle<Iter<'a, Box<[u8]>>>,
    },
}
impl<'a> DelimiterState<'a> {
    fn new(unescaped_and_encoded_delimiters: &'a [Box<[u8]>]) -> Self {
        if unescaped_and_encoded_delimiters.is_empty() {
            DelimiterState::NoDelimiters
        } else if unescaped_and_encoded_delimiters.len() == 1 {
            let only_delimiter = &unescaped_and_encoded_delimiters[0];
            if only_delimiter.is_empty() {
                DelimiterState::NoDelimiters
            } else {
                DelimiterState::OneDelimiter(only_delimiter)
            }
        } else {
            DelimiterState::MultipleDelimiters {
                current_delimiter: &unescaped_and_encoded_delimiters[0],
                delimiters: unescaped_and_encoded_delimiters,
                delimiters_iterator: paste_trusted::delimiter_cycle(
                    unescaped_and_encoded_delimiters,
                ),
            }
        }
    }
    fn reset_to_first_delimiter(&mut self) {
        if let DelimiterState::MultipleDelimiters {
            delimiters_iterator,
            delimiters,
            ..
        } = self
        {
            *delimiters_iterator = paste_trusted::delimiter_cycle(delimiters);
        }
    }
    fn remove_trailing_delimiter(&mut self, output: &mut Vec<u8>) {
        let delimiter_length = match self {
            DelimiterState::OneDelimiter(only_delimiter) => only_delimiter.len(),
            DelimiterState::MultipleDelimiters {
                current_delimiter, ..
            } => current_delimiter.len(),
            DelimiterState::NoDelimiters => {
                return;
            }
        };
        if delimiter_length > 0 {
            let output_len = output.len();
            if let Some(output_without_delimiter_length) = output_len.checked_sub(delimiter_length)
            {
                output.truncate(output_without_delimiter_length);
            } else {
            }
        }
    }
    fn write_delimiter(&mut self, output: &mut Vec<u8>) {
        match self {
            DelimiterState::OneDelimiter(only_delimiter) => {
                output.extend_from_slice(only_delimiter);
            }
            DelimiterState::MultipleDelimiters {
                current_delimiter,
                delimiters_iterator,
                ..
            } => {
                let bo = paste_trusted::delimiter_next(delimiters_iterator).unwrap();
                output.extend_from_slice(bo);
                *current_delimiter = bo;
            }
            DelimiterState::NoDelimiters => {}
        }
    }
}
pub enum InputSource {
    File(BufReader<File>),
    StandardInput(Rc<RefCell<Stdin>>),
}
impl InputSource {
    fn read(&mut self, buf: &mut [u8]) -> UResult<usize> {
        let us = match self {
            Self::File(reader) => paste_trusted::library::read(reader, buf)?,
            Self::StandardInput(rc) => {
                let mut reader = paste_trusted::library::lock_stdin(rc);
                paste_trusted::library::read(&mut reader, buf)?
            }
        };
        Ok(us)
    }
    pub(crate) fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> UResult<usize> {
        let us = match self {
            Self::File(reader) => paste_trusted::library::read_until(reader, byte, buf)?,
            Self::StandardInput(rc) => {
                let mut reader = paste_trusted::library::lock_stdin(rc);
                paste_trusted::library::read_until(&mut reader, byte, buf)?
            }
        };
        Ok(us)
    }
}
