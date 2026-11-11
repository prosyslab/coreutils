// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::io_trusted;
use crate::operation::ChunkProcessor;
use crate::trusted::{chunks, count_kept};
use std::io::{BufRead, Write};
type UResult<T> = std::io::Result<T>;
#[path = "../../../../verification_runtime/tr_translate.rs"]
pub(crate) mod translation_trusted;
use crate::trusted_common as library_trusted;
pub(crate) use crate::trusted_common::{closure_with_spec, extend_mapped};
pub fn find_single_change<T, F>(table: &[T; 256], check: F) -> Option<(u8, T)>
where
    F: Fn(usize, &T) -> bool,
    T: Copy,
{
    let matches = library_trusted::enumerated_filter_take(table, check, 2);
    if matches.len() == 1 {
        Some((matches[0].0 as u8, matches[0].1))
    } else {
        None
    }
}
#[inline]
pub fn process_single_char_replace<'a>(
    input: &'a [u8],
    output: &'a mut Vec<u8>,
    source_char: u8,
    target_char: u8,
) -> &'a [u8] {
    let count = translation_trusted::count(input, source_char);
    if count == 0 {
        return input;
    }
    if count == input.len() {
        output.resize(output.len() + input.len(), target_char);
    } else {
        let mapper = |b: u8| if b == source_char { target_char } else { b };
        extend_mapped(output, input, mapper);
    }
    output
}
pub fn process_single_delete<'a>(
    input: &'a [u8],
    output: &'a mut Vec<u8>,
    delete_char: u8,
    keep: &[bool; 256],
) -> &'a [u8] {
    let count = bytecount::count(input, delete_char);
    if count == 0 {
        return input;
    }
    if count < input.len() / 128 {
        let mut start = 0;
        let mut search = crate::trusted::search_new(delete_char, input);
        loop {
            let next = crate::trusted::search_next(&mut search);
            let pos = match next {
                Some(pos) => pos,
                None => break,
            };
            output.extend_from_slice(&input[start..pos]);
            start = pos + 1;
        }
        output.extend_from_slice(&input[start..]);
    } else if count < input.len() {
        process_delete(input, output, keep);
    } else {
    }
    output
}
pub fn process_delete(input: &[u8], output: &mut Vec<u8>, keep: &[bool; 256]) {
    const BLOCK: usize = 1024;
    const FEW: usize = 64;
    let mut block = [0; BLOCK];
    let start = &input[..input.len().min(256)];
    let mut few_kept = count_kept(start, keep) * FEW < start.len();
    let chunk_iter = chunks(input, BLOCK);
    for chunk in chunk_iter {
        let mut kept = 0;
        if few_kept {
            for byte in chunk {
                let b = *byte;
                if keep[b as usize] {
                    block[kept % BLOCK] = b;
                    kept += 1;
                }
            }
        } else {
            for byte in chunk {
                let b = *byte;
                block[kept % BLOCK] = b;
                kept += usize::from(keep[b as usize]);
            }
        }
        output.extend_from_slice(&block[..kept]);
        few_kept = kept * FEW < chunk.len();
    }
}
pub fn process_input<R, W, P>(input: &mut R, output: &mut W, processor: &P) -> UResult<()>
where
    R: BufRead,
    W: Write,
    P: ChunkProcessor + ?Sized,
{
    const BUFFER_SIZE: usize = 32768;
    let mut buf = [0; BUFFER_SIZE];
    let mut output_buf = Vec::with_capacity(BUFFER_SIZE);
    loop {
        let length = match io_trusted::read(input, &mut buf[..]) {
            Ok(0) => break,
            Ok(len) => len,
            Err(e) => return Err(e),
        };
        output_buf.clear();
        let processed = processor.process_chunk(&buf[..length], &mut output_buf);
        if !processed.is_empty() {
            write_output(output, processed)?;
        }
    }
    Ok(())
}
#[inline(never)]
pub fn write_output<W: Write>(output: &mut W, buf: &[u8]) -> UResult<()> {
    return io_trusted::write_all(output, buf);
    #[cfg(windows)]
    match output.write_all(buf) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::BrokenPipe => {
            std::process::exit(13);
        }
        Err(err) => Err(err.map_err_context(|| translate!("tr-error-write-error"))),
    }
}
