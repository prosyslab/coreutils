// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

//! I/O processing infrastructure for tr operations with SIMD optimizations

#[cfg(not(verus_keep_ghost))]
use crate::operation::ChunkProcessor;
#[cfg(not(verus_keep_ghost))]
use std::io::{BufRead, Write};
#[cfg(not(verus_keep_ghost))]
use uucore::error::{FromIo, UResult};
#[cfg(not(verus_keep_ghost))]
use uucore::translate;

#[cfg(all(verus_keep_ghost, uutils_tr_delete))]
use crate::proof::{reference_prefix, reference_step, write_prefix};
#[cfg(all(verus_keep_ghost, uutils_tr_delete))]
use crate::trusted::{chunks, chunks_match, count_kept};
#[cfg(all(verus_keep_ghost, not(uutils_tr_delete)))]
use std::io::Write;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(all(verus_keep_ghost, not(uutils_tr_delete)))]
use crate::io_trusted;
#[cfg(all(verus_keep_ghost, not(uutils_tr_delete)))]
type UResult<T> = std::io::Result<T>;
#[cfg(not(verus_keep_ghost))]
use crate::operation::io_trusted;

#[cfg(any(not(verus_keep_ghost), uutils_tr_translate))]
#[path = "../../../../../tr/translate/trusted.rs"]
pub(crate) mod translation_trusted;

#[cfg(not(verus_keep_ghost))]
#[path = "../../../../../tr/delete/trusted.rs"]
mod trusted;
#[cfg(not(verus_keep_ghost))]
#[path = "../../../../../trusted_common.rs"]
pub(crate) mod trusted_common;
#[cfg(not(verus_keep_ghost))]
use trusted::{chunks, count_kept};

#[cfg(all(verus_keep_ghost, uutils_tr_translate))]
pub(crate) use crate::trusted_common::{closure_with_spec, extend_mapped};
#[cfg(not(verus_keep_ghost))]
pub(crate) use trusted_common::{closure_with_spec, extend_mapped};

/// Helper to detect single-character operations for optimization
#[cfg(any(not(verus_keep_ghost), uutils_tr_translate))]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec)]
pub fn find_single_change<T, F>(table: &[T; 256], check: F) -> Option<(u8, T)>
where
    F: Fn(usize, &T) -> bool,
    T: Copy,
{
    let matches: Vec<_> = table
        .iter()
        .enumerate()
        .filter_map(|(i, val)| check(i, val).then_some((i as u8, *val)))
        .take(2)
        .collect();

    (matches.len() == 1).then(|| matches[0])
}

/// SIMD-optimized single character replacement
#[inline]
#[cfg(any(not(verus_keep_ghost), uutils_tr_translate))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(output).len() == 0,
    ensures result@ == crate::proof::replace_prefix(input@, source_char, target_char, input@.len() as int),
))]
pub fn process_single_char_replace<'a>(
    input: &'a [u8],
    output: &'a mut Vec<u8>,
    source_char: u8,
    target_char: u8,
) -> &'a [u8] {
    let count = translation_trusted::count(input, source_char);
    if count == 0 {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::replace_absent(input@, source_char, target_char, input@.len() as int); }
        return input;
    }
    if count == input.len() {
        output.resize(output.len() + input.len(), target_char);
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::replace_all(input@, source_char, target_char, input@.len() as int); }
    } else {
        let mapper = closure_with_spec!(
            (result: u8 => ensures result == if b == source_char { target_char } else { b },),
            |b: u8| if b == source_char { target_char } else { b }
        );
        extend_mapped(output, input, mapper);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::replaced_map(input@, source_char, target_char, output@, input@.len() as int);
            assert(output@.take(input@.len() as int) =~= output@);
        }
    }
    output
}

/// SIMD-optimized delete operation for single character
///
/// `keep` must be false for `delete_char` only.
#[cfg(not(verus_keep_ghost))]
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
        // Below one match per 128 bytes, copying the runs between matches
        // beats `process_delete`.
        let mut start = 0;
        for pos in memchr::memchr_iter(delete_char, input) {
            output.extend_from_slice(&input[start..pos]);
            start = pos + 1;
        }
        output.extend_from_slice(&input[start..]);
    } else if count < input.len() {
        process_delete(input, output, keep);
    }
    // If count == input.len(), all deleted, output nothing
    output
}

/// Append to `output` the bytes of `input` whose `keep` entry is true.
#[cfg(any(not(verus_keep_ghost), uutils_tr_delete))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + reference_prefix(input@, keep@, input@.len() as int),
))]
pub fn process_delete(input: &[u8], output: &mut Vec<u8>, keep: &[bool; 256]) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = output@; }
    // The index is always below `BLOCK` (a power of two), so the modulo is a
    // mask that only serves to drop the bounds check.
    const BLOCK: usize = 1024;
    // Below one kept byte in `FEW`, a branch per byte is well predicted and
    // stores less.
    const FEW: usize = 64;
    let mut block = [0; BLOCK];
    // Guess for the first block from its start, then go by the previous one.
    let start = &input[..input.len().min(256)];
    let mut few_kept = count_kept(start, keep) * FEW < start.len();
    let chunk_iter = chunks(input, BLOCK);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost all_chunks = chunk_iter.values(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(chunk_state =>
        invariant
            chunk_state.seq() == all_chunks,
            chunks_match(input@, all_chunks, BLOCK as int),
            output@ == initial + reference_prefix(input@, keep@,
                if chunk_state.index() * BLOCK < input.len() {
                    chunk_state.index() * BLOCK
                } else { input.len() as int }),
    ))]
    for chunk in chunk_iter {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost offset = chunk_state.index() * BLOCK; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0 <= chunk_state.index() < all_chunks.len());
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(input.len() + 1023, 1024);
            vstd::arithmetic::div_mod::lemma_mod_bound(input.len() + 1023, 1024);
            assert(0 <= offset < input.len());
            assert(chunk@ == input@.subrange(offset, offset + chunk.len()));
        }
        let mut kept = 0;
        if few_kept {
            // Only store the kept bytes.
            #[cfg_attr(verus_keep_ghost, verus_spec(byte_state =>
                invariant
                    0 < chunk.len() <= BLOCK,
                    0 <= offset,
                    offset + chunk.len() <= input.len(),
                    chunk@ == input@.subrange(offset, offset + chunk.len()),
                    kept <= byte_state.index(),
                    byte_state.seq() == chunk@.as_ref(),
                    output@ + block@.take(kept as int)
                        == initial + reference_prefix(input@, keep@, offset + byte_state.index()),
            ))]
            for byte in chunk {
                let b = *byte;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(0 <= byte_state.index() < chunk.len());
                    assert(b == input@[offset + byte_state.index()]);
                    reference_step(input@, keep@, offset + byte_state.index());
                }
                if keep[b as usize] {
                    #[cfg(verus_keep_ghost)]
                    proof! { write_prefix(block@, kept as int, b, output@); }
                    block[kept % BLOCK] = b;
                    kept += 1;
                }
            }
        } else {
            // Store every byte and only advance past kept ones: no branch.
            #[cfg_attr(verus_keep_ghost, verus_spec(byte_state =>
                invariant
                    0 < chunk.len() <= BLOCK,
                    0 <= offset,
                    offset + chunk.len() <= input.len(),
                    chunk@ == input@.subrange(offset, offset + chunk.len()),
                    kept <= byte_state.index(),
                    byte_state.seq() == chunk@.as_ref(),
                    output@ + block@.take(kept as int)
                        == initial + reference_prefix(input@, keep@, offset + byte_state.index()),
            ))]
            for byte in chunk {
                let b = *byte;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(0 <= byte_state.index() < chunk.len());
                    assert(b == input@[offset + byte_state.index()]);
                    reference_step(input@, keep@, offset + byte_state.index());
                    write_prefix(block@, kept as int, b, output@);
                }
                block[kept % BLOCK] = b;
                kept += usize::from(keep[b as usize]);
            }
        }
        output.extend_from_slice(&block[..kept]);
        few_kept = kept * FEW < chunk.len();
    }
}

/// Unified I/O processing for all operations
#[cfg(not(verus_keep_ghost))]
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
        let length = match input.read(&mut buf[..]) {
            Ok(0) => break,
            Ok(len) => len,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e.map_err_context(|| translate!("tr-error-read-error"))),
        };

        output_buf.clear();
        let processed = processor.process_chunk(&buf[..length], &mut output_buf);

        if !processed.is_empty() {
            write_output(output, processed)?;
        }
    }

    Ok(())
}

/// Helper function to handle platform-specific write operations
// Kept out of line: inlined into `translate_input`, the raw `write` made the
// translator state go to memory on every byte, doubling the time of `tr -s`.
#[inline(never)]
#[cfg(any(
    not(verus_keep_ghost),
    uutils_tr_squeeze,
    uutils_tr_delete_and_squeeze,
    uutils_tr_translate_and_squeeze
))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires io_trusted::writable(old(output)),
    ensures result is Ok, io_trusted::writable(final(output)),
        io_trusted::written(final(output)) == io_trusted::written(old(output)) + buf@,
))]
pub fn write_output<W: Write>(output: &mut W, buf: &[u8]) -> UResult<()> {
    #[cfg(verus_keep_ghost)]
    return io_trusted::write_all(output, buf);

    #[cfg(not(verus_keep_ghost))]
    #[cfg(not(windows))]
    return io_trusted::write_all(output, buf)
        .map_err_context(|| translate!("tr-error-write-error"));

    #[cfg(windows)]
    match output.write_all(buf) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::BrokenPipe => {
            std::process::exit(13);
        }
        Err(err) => Err(err.map_err_context(|| translate!("tr-error-write-error"))),
    }
}
