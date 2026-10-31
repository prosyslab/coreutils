// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

// spell-checker:ignore ELEMS

//! Utilities for reading files as chunks.

#![allow(dead_code)]
// Ignores non-used warning for `borrow_buffer` in `Chunk`

use std::{
    io::{ErrorKind, Read},
    ops::Range,
    sync::mpsc::SyncSender,
};

use memchr::memchr_iter;
use self_cell::self_cell;
use crate::SortResult as UResult;

use crate::{
    GeneralBigDecimalParseResult, GlobalSettings, Line, SortError, numeric_str_cmp::NumInfo,
};
#[cfg(verus_keep_ghost)]
use vstd::{prelude::*, std_specs::iter::IteratorSpec};

#[cfg_attr(verus_keep_ghost, verus_verify)]
const ALLOC_CHUNK_SIZE: usize = 64 * 1024;
const MAX_TOKEN_BUFFER_BYTES: usize = 4 * 1024 * 1024;
const MAX_TOKEN_BUFFER_ELEMS: usize = MAX_TOKEN_BUFFER_BYTES / size_of::<Range<usize>>();

self_cell!(
    /// The chunk that is passed around between threads.
    pub struct Chunk {
        owner: Vec<u8>,

        #[covariant]
        dependent: ChunkContents,
    }

    impl {Debug}
);

#[derive(Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct ChunkContents<'a> {
    pub lines: Vec<Line<'a>>,
    pub line_data: LineData<'a>,
    pub token_buffer: Vec<Range<usize>>,
    pub line_count_hint: usize,
}

#[derive(Debug, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct LineData<'a> {
    pub selections: Vec<&'a [u8]>,
    pub num_infos: Vec<NumInfo>,
    pub parsed_floats: Vec<GeneralBigDecimalParseResult>,
    pub line_num_floats: Vec<Option<f64>>,
    /// Arena buffer holding all collation sort keys concatenated.
    pub collation_key_buffer: Vec<u8>,
    /// End offsets into `collation_key_buffer` for each line's sort key.
    pub collation_key_ends: Vec<usize>,
}

impl LineData<'_> {
    /// Get the collation sort key for a line at the given index.
    pub fn collation_key(&self, index: usize) -> &[u8] {
        let start = if index == 0 {
            0
        } else {
            self.collation_key_ends[index - 1]
        };
        let end = self.collation_key_ends[index];
        &self.collation_key_buffer[start..end]
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::proof::input::recycled_empty(&result), result.buffer.len() == 0,
        result.line_count_hint == old(contents).line_count_hint,
        crate::proof::input::contents_empty(final(contents)),
        final(contents).line_count_hint == old(contents).line_count_hint,
))]
fn recycle_contents(_owner: &Vec<u8>, contents: &mut ChunkContents<'_>) -> RecycledChunk {
    contents.lines.clear();
    contents.line_data.selections.clear();
    contents.line_data.num_infos.clear();
    contents.line_data.parsed_floats.clear();
    contents.line_data.line_num_floats.clear();
    contents.line_data.collation_key_buffer.clear();
    contents.line_data.collation_key_ends.clear();
    contents.token_buffer.clear();
    #[cfg(not(verus_keep_ghost))]
    let lines = unsafe {
        // SAFETY: It is safe to (temporarily) transmute to a vector of lines with a longer lifetime,
        // because the vector is empty.
        // Transmuting is necessary to make recycling possible. See https://github.com/rust-lang/rfcs/pull/2802
        // for a rfc to make this unnecessary. Its example is similar to the code here.
        std::mem::transmute::<Vec<Line<'_>>, Vec<Line<'static>>>(std::mem::take(
            &mut contents.lines,
        ))
    };
    #[cfg(verus_keep_ghost)]
    let lines = crate::trusted::ownership::cast_empty_lines(std::mem::take(&mut contents.lines));
    #[cfg(not(verus_keep_ghost))]
    let selections = unsafe {
        // SAFETY: (same as above) It is safe to (temporarily) transmute to a vector of &str with a longer lifetime,
        // because the vector is empty.
        std::mem::transmute::<Vec<&'_ [u8]>, Vec<&'static [u8]>>(std::mem::take(
            &mut contents.line_data.selections,
        ))
    };
    #[cfg(verus_keep_ghost)]
    let selections = crate::trusted::ownership::cast_empty_selections(
        std::mem::take(&mut contents.line_data.selections));
    let result = RecycledChunk {
        lines,
        selections,
        num_infos: std::mem::take(&mut contents.line_data.num_infos),
        parsed_floats: std::mem::take(&mut contents.line_data.parsed_floats),
        line_num_floats: std::mem::take(&mut contents.line_data.line_num_floats),
        collation_key_buffer: std::mem::take(&mut contents.line_data.collation_key_buffer),
        collation_key_ends: std::mem::take(&mut contents.line_data.collation_key_ends),
        token_buffer: std::mem::take(&mut contents.token_buffer),
        line_count_hint: contents.line_count_hint,
        // buffer is set below after we consume `self`
        buffer: Vec::new(),
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::input::establish_recycled_empty(&result); }
    result
}

impl Chunk {
    /// Destroy this chunk and return its components to be reused.
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::proof::input::recycled_empty(&result),
            crate::proof::input::recycled_buffer(&result) == crate::trusted::ownership::owner(&self)@,
            crate::proof::input::recycled_hint(&result) == crate::trusted::ownership::contents(&self).line_count_hint,
    ))]
    pub fn recycle(self) -> RecycledChunk {
        let mut chunk = self;
        let mut recycled_contents = chunk.with_dependent_mut(recycle_contents);
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::input::recycled_empty_facts(&recycled_contents); }
        recycled_contents.buffer = chunk.into_owner();
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::input::establish_recycled_empty(&recycled_contents);
            crate::proof::input::recycled_values(&recycled_contents);
        }
        recycled_contents
    }

    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == crate::trusted::ownership::contents(self).lines@,
    ))]
    pub fn lines(&self) -> &Vec<Line<'_>> {
        &self.borrow_dependent().lines
    }

    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures *result == crate::trusted::ownership::contents(self).line_data,
    ))]
    pub fn line_data(&self) -> &LineData<'_> {
        &self.borrow_dependent().line_data
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct RecycledChunk {
    pub(crate) lines: Vec<Line<'static>>,
    pub(crate) selections: Vec<&'static [u8]>,
    pub(crate) num_infos: Vec<NumInfo>,
    pub(crate) parsed_floats: Vec<GeneralBigDecimalParseResult>,
    pub(crate) line_num_floats: Vec<Option<f64>>,
    pub(crate) collation_key_buffer: Vec<u8>,
    pub(crate) collation_key_ends: Vec<usize>,
    pub(crate) token_buffer: Vec<Range<usize>>,
    pub(crate) line_count_hint: usize,
    pub(crate) buffer: Vec<u8>,
}

impl RecycledChunk {
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::proof::input::recycled_empty(&result),
            crate::proof::input::recycled_buffer(&result).len() == capacity,
    ))]
    pub fn new(capacity: usize) -> Self {
        let result = Self {
            lines: Vec::new(),
            selections: Vec::new(),
            num_infos: Vec::new(),
            parsed_floats: Vec::new(),
            line_num_floats: Vec::new(),
            collation_key_buffer: Vec::new(),
            collation_key_ends: Vec::new(),
            token_buffer: Vec::new(),
            line_count_hint: 0,
            buffer: vec![0; capacity],
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::input::establish_recycled_empty(&result);
            crate::proof::input::recycled_values(&result);
        }
        result
    }
}

/// Read a chunk, parse lines and send them.
///
/// No empty chunk will be sent. If we reach the end of the input, `false` is returned.
/// However, if this function returns `true`, it is not guaranteed that there is still
/// input left: If the input fits _exactly_ into a buffer, we will only notice that there's
/// nothing more to read at the next invocation. In case there is no input left, nothing will
/// be sent.
///
/// # Arguments
///
/// (see also `read_to_chunk` for a more detailed documentation)
///
/// * `sender`: The sender to send the lines to the sorter.
/// * `recycled_chunk`: The recycled chunk, as returned by `Chunk::recycle`.
///   (i.e. `buffer.len()` should be equal to `buffer.capacity()`)
/// * `max_buffer_size`: How big `buffer` can be.
/// * `carry_over`: The bytes that must be carried over in between invocations.
/// * `file`: The current file.
/// * `next_files`: What `file` should be updated to next.
/// * `separator`: The line separator.
/// * `settings`: The global settings.
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(state): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>,
    requires crate::proof::input::recycled_empty(&recycled_chunk),
        crate::proof::native_settings_valid(settings),
        crate::trusted_common::io::readable(old(file)),
        old(next_files).obeys_prophetic_iter_laws(), old(next_files).will_return_none(),
        old(next_files).decrease() is Some,
        crate::proof::input::valid_files(old(next_files).remaining()),
        crate::trusted::concurrency::sender_id(sender) == old(state).id(),
        !old(state).own_closed(),
        crate::proof::input::allows_read(old(state).rule(), old(state).index(),
            crate::proof::input::pending(old(carry_over)@, old(file), old(next_files).remaining(), separator), separator, settings),
        old(state).index() + crate::proof::input::pending(old(carry_over)@, old(file), old(next_files).remaining(), separator).len()
            <= old(state).limit(),
    ensures result is Ok, crate::trusted_common::io::readable(final(file)),
        (&*final(next_files)).obeys_prophetic_iter_laws(), (&*final(next_files)).will_return_none(),
        (&*final(next_files)).decrease() is Some,
        crate::proof::input::valid_files((&*final(next_files)).remaining()),
        final(state).id() == old(state).id(), final(state).rule() == old(state).rule(),
        final(state).template() == old(state).template(), final(state).dependency() == old(state).dependency(),
        final(state).peer_closed() == old(state).peer_closed(),
        final(state).own_closed() == old(state).own_closed(),
        final(state).limit() == old(state).limit(), final(state).index() <= final(state).limit(),
        result->Ok_0 ==> final(state).index()
            + crate::proof::input::pending(final(carry_over)@, final(file), (&*final(next_files)).remaining(), separator).len()
                <= old(state).index() + crate::proof::input::pending(old(carry_over)@, old(file), old(next_files).remaining(), separator).len(),
        crate::proof::input::read_effect(crate::proof::input::pending(old(carry_over)@, old(file), old(next_files).remaining(), separator), final(carry_over)@, final(file),
            (&*final(next_files)).remaining(), separator, settings,
            old(state).id(), old(state).index(), final(state).index(), result->Ok_0),
))]
pub fn read<T: Read>(
    sender: &SyncSender<Chunk>,
    recycled_chunk: RecycledChunk,
    max_buffer_size: Option<usize>,
    carry_over: &mut Vec<u8>,
    file: &mut T,
    next_files: &mut impl Iterator<Item = UResult<T>>,
    separator: u8,
    settings: &GlobalSettings,
) -> UResult<bool> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_index = state.index(); let ghost initial_id = state.id();
        let ghost expected = crate::proof::input::pending(carry_over@, file, next_files.remaining(), separator);
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::input::recycled_empty_facts(&recycled_chunk); }
    let RecycledChunk {
        lines,
        selections,
        num_infos,
        parsed_floats,
        line_num_floats,
        collation_key_buffer,
        collation_key_ends,
        mut token_buffer,
        mut line_count_hint,
        mut buffer,
    } = recycled_chunk;
    if buffer.len() < carry_over.len() {
        // Separate carry_over and copy them to avoid cost of 0 fill buffer
        buffer.extend_from_slice(&carry_over[buffer.len()..]);
    }
    #[cfg(not(verus_keep_ghost))]
    buffer[..carry_over.len()].copy_from_slice(carry_over);
    #[cfg(verus_keep_ghost)]
    crate::trusted::input::copy_prefix(&mut buffer, carry_over);
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::std_specs::vec::axiom_spec_len(carry_over);
        assert(buffer@.take(carry_over.len() as int) == carry_over@);
    }
    #[cfg(verus_keep_ghost)]
    proof_with! { Ghost((state.limit() - state.index()) as nat) }
    let (read, should_continue) = read_to_buffer(
        file,
        next_files,
        &mut buffer,
        max_buffer_size,
        carry_over.len(),
        separator,
    )?;
    carry_over.clear();
    carry_over.extend_from_slice(&buffer[read..]);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost consumed = buffer@.take(read as int); let ghost full_buffer = buffer@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(carry_over@ == buffer@.skip(read as int));
        if should_continue {
            assert(expected == consumed + crate::proof::input::pending(buffer@.skip(read as int),
                &*file, (&*next_files).remaining(), separator));
            crate::proof::input::prefix_of_sum(consumed,
                crate::proof::input::pending(carry_over@, file, (&*next_files).remaining(), separator), expected);
        } else { crate::proof::input::prefix_of_sum(consumed, Seq::empty(), expected); }
    }

    if read != 0 {
        #[cfg(not(verus_keep_ghost))]
        let payload: UResult<Chunk> = Chunk::try_new(buffer, |buffer| {
            build_chunk_contents(buffer, read, lines, selections, num_infos, parsed_floats,
                line_num_floats, collation_key_buffer, collation_key_ends, token_buffer,
                line_count_hint, separator, settings)
        });
        #[cfg(verus_keep_ghost)]
        let payload: UResult<Chunk> = verus_exec_expr! {
            Chunk::try_new(buffer, |buffer: &Vec<u8>| -> (result: UResult<ChunkContents<'_>>)
                requires 0 < read <= buffer.len(), lines.len() == 0, selections.len() == 0,
                    num_infos.len() == 0, parsed_floats.len() == 0, line_num_floats.len() == 0,
                    collation_key_buffer.len() == 0, collation_key_ends.len() == 0,
                    crate::proof::native_settings_valid(settings),
                ensures result is Ok, crate::proof::input::parsed_contents(&result->Ok_0,
                    buffer@.take(read as int), separator, settings),
            {
                build_chunk_contents(buffer, read, lines, selections, num_infos, parsed_floats,
                    line_num_floats, collation_key_buffer, collation_key_ends, token_buffer,
                    line_count_hint, separator, settings)
            })
        };
        let payload = payload?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::proof::input::parsed_contents(&crate::trusted::ownership::contents(&payload),
                consumed, separator, settings));
            assert(consumed.len() == expected.len() || consumed.last() == separator);
            assert(state.rule()(state.index(), payload));
            assert(consumed.len() > 0);
            assert(state.index() < state.limit());
        }
        #[cfg(not(verus_keep_ghost))]
        sender.send(payload).unwrap();
        #[cfg(verus_keep_ghost)]
        verus_exec_expr! {
            crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send(sender, payload, Tracked(state)))
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::proof::input::read_effect(expected, carry_over@, file,
                (&*next_files).remaining(), separator, settings, initial_id, initial_index,
                state.index(), should_continue));
        }
    }
    Ok(should_continue)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < read <= buffer.len(), lines.len() == 0, selections.len() == 0,
        num_infos.len() == 0, parsed_floats.len() == 0, line_num_floats.len() == 0,
        collation_key_buffer.len() == 0, collation_key_ends.len() == 0,
        crate::proof::native_settings_valid(settings),
    ensures result is Ok, crate::proof::input::parsed_contents(&result->Ok_0,
        buffer@.take(read as int), separator, settings),
))]
fn build_chunk_contents<'a>(
    buffer: &'a Vec<u8>, read: usize, lines: Vec<Line<'static>>, selections: Vec<&'static [u8]>,
    num_infos: Vec<NumInfo>, parsed_floats: Vec<GeneralBigDecimalParseResult>, line_num_floats: Vec<Option<f64>>,
    collation_key_buffer: Vec<u8>, collation_key_ends: Vec<usize>, mut token_buffer: Vec<Range<usize>>,
    mut line_count_hint: usize, separator: u8, settings: &GlobalSettings,
) -> UResult<ChunkContents<'a>> {
    #[cfg(not(verus_keep_ghost))]
    let selections = unsafe {
        // SAFETY: The vector is empty; only its lifetime changes.
        std::mem::transmute::<Vec<&'static [u8]>, Vec<&'_ [u8]>>(selections)
    };
    #[cfg(verus_keep_ghost)]
    let selections = crate::trusted::ownership::cast_empty_selections(selections);
    #[cfg(not(verus_keep_ghost))]
    let mut lines = unsafe {
        // SAFETY: The vector is empty; only its lifetime changes.
        std::mem::transmute::<Vec<Line<'static>>, Vec<Line<'_>>>(lines)
    };
    #[cfg(verus_keep_ghost)]
    let mut lines = crate::trusted::ownership::cast_empty_lines(lines);
    let read = &buffer[..read];
    #[cfg(verus_keep_ghost)]
    let read = crate::trusted::bounded_bytes(read);
    let mut line_data = LineData {
        selections, num_infos, parsed_floats, line_num_floats, collation_key_buffer, collation_key_ends,
    };
    parse_lines(read, &mut lines, &mut line_data, &mut token_buffer, &mut line_count_hint, separator, settings);
    let result = ChunkContents { lines, line_data, token_buffer, line_count_hint };
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::input::establish_parsed_contents(&result, read@, separator, settings); }
    Ok(result)
}

/// Split `read` into `Line`s, and add them to `lines`.
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires read@.len() > 0, read@.len() <= isize::MAX,
        old(lines).len() == 0, crate::proof::native_settings_valid(settings),
        old(line_data).selections.len() == 0, old(line_data).num_infos.len() == 0,
        old(line_data).parsed_floats.len() == 0, old(line_data).line_num_floats.len() == 0,
        old(line_data).collation_key_buffer.len() == 0, old(line_data).collation_key_ends.len() == 0,
    ensures crate::proof::sorting::native_owned(final(lines)@)
            == crate::proof::sorting::rows_of(read@, separator),
        crate::proof::sorting::cache_shape(final(line_data), settings, final(lines).len() as int),
        forall|i: int| 0 <= i < final(lines).len() ==>
            crate::proof::cached_line(&#[trigger] final(lines)@[i], settings, final(line_data)),
))]
fn parse_lines<'a>(
    read: &'a [u8],
    lines: &mut Vec<Line<'a>>,
    line_data: &mut LineData<'a>,
    token_buffer: &mut Vec<Range<usize>>,
    line_count_hint: &mut usize,
    separator: u8,
    settings: &GlobalSettings,
) {
    const SMALL_CHUNK_BYTES: usize = 64 * 1024;

    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_read = read@; }
    #[cfg(not(verus_keep_ghost))]
    let read = read.strip_suffix(&[separator]).unwrap_or(read);
    #[cfg(verus_keep_ghost)]
    let terminator = [separator];
    #[cfg(verus_keep_ghost)]
    let read = match crate::trusted_common::strip_suffix(read, &terminator) {
        Some(prefix) => prefix, None => read,
    };

    #[cfg(not(verus_keep_ghost))]
    {
    assert!(lines.is_empty());
    assert!(line_data.selections.is_empty());
    assert!(line_data.num_infos.is_empty());
    assert!(line_data.parsed_floats.is_empty());
    assert!(line_data.line_num_floats.is_empty());
    assert!(line_data.collation_key_buffer.is_empty());
    assert!(line_data.collation_key_ends.is_empty());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(terminator@ == seq![separator]);
        crate::proof_common::has_byte_suffix(initial_read, separator);
        assert(read@ == crate::proof::input::stripped(initial_read, separator));
        crate::proof::input::stripped_rows(initial_read, separator);
        assert(crate::proof::sorting::cache_shape(line_data, settings, 0));
    }
    token_buffer.clear();
    let mut estimated = (*line_count_hint).max(1);
    let mut exact_line_count = None;
    if *line_count_hint == 0 || read.len() <= SMALL_CHUNK_BYTES {
        let count = if read.is_empty() {
            1
        } else {
            #[cfg(not(verus_keep_ghost))]
            let separators = memchr_iter(separator, read).count();
            #[cfg(verus_keep_ghost)]
            let separators = crate::trusted::input::separator_positions(separator, read).len();
            separators + 1
        };
        exact_line_count = Some(count);
        estimated = count;
    } else if estimated == 1 {
        const LINE_LEN_HINT: usize = 128;
        #[cfg(not(verus_keep_ghost))]
        { estimated = (read.len() / LINE_LEN_HINT).clamp(1, 1024); }
        #[cfg(verus_keep_ghost)]
        { estimated = (read.len() / LINE_LEN_HINT).max(1).min(1024); }
    }
    lines.reserve(estimated);
    if settings.precomputed.selections_per_line > 0 {
        line_data
            .selections
            .reserve(estimated.saturating_mul(settings.precomputed.selections_per_line));
    }
    if settings.precomputed.num_infos_per_line > 0 {
        line_data
            .num_infos
            .reserve(estimated.saturating_mul(settings.precomputed.num_infos_per_line));
    }
    if settings.precomputed.floats_per_line > 0 {
        line_data
            .parsed_floats
            .reserve(estimated.saturating_mul(settings.precomputed.floats_per_line));
    }
    if settings.precomputed.whole_line_numeric {
        line_data.line_num_floats.reserve(estimated);
    }
    let mut start = 0usize;
    let mut index = 0usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::std_specs::vec::axiom_spec_len(lines);
        crate::proof::input::begin_rows(lines@, read@, separator);
    }
    #[cfg(not(verus_keep_ghost))]
    let separator_iter = memchr_iter(separator, read);
    #[cfg(verus_keep_ghost)]
    let separator_iter = crate::trusted::input::separator_positions(separator, read);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost all_positions = separator_iter@; }
    #[cfg_attr(verus_keep_ghost, verus_spec(separator_state =>
        invariant read@ == crate::proof::input::stripped(initial_read, separator),
            read@.len() <= isize::MAX,
            crate::proof::input::plain_rows(read@, separator)
                == crate::proof::sorting::rows_of(initial_read, separator),
            crate::proof::native_settings_valid(settings),
            separator_state.seq() == all_positions,
            crate::proof::input::separator_gaps(read@, separator, separator_state.seq()),
            index == separator_state.index(), lines.len() == index,
            start == crate::proof::input::separator_start(separator_state.seq(), separator_state.index()),
            crate::proof::sorting::native_owned(lines@)
                    + crate::proof::input::plain_rows(read@.skip(start as int), separator)
                == crate::proof::input::plain_rows(read@, separator),
            crate::proof::sorting::cache_shape(line_data, settings, index as int),
            forall|i: int| 0 <= i < lines.len() ==>
                crate::proof::cached_line(&#[trigger] lines@[i], settings, line_data),
    ))]
    for sep_idx in separator_iter {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::input::plain_gap(read@, separator, separator_state.seq(), separator_state.index());
            crate::proof::input::advance_rows(crate::proof::sorting::native_owned(lines@),
                read@, separator, separator_state.seq(), separator_state.index());
        }
        let line = &read[start..sep_idx];
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_data = *line_data; }
        let created = Line::create(line, index, line_data, token_buffer, settings);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i < lines.len() implies
                crate::proof::cached_line(&#[trigger] lines@[i], settings, line_data) by {
                crate::proof::sorting::preserve_cached(&lines@[i], settings, &previous_data, line_data);
            };
            crate::proof::input::owned_push(lines@, &created);
            assert(crate::proof::sorting::cache_shape(line_data, settings, index as int + 1));
        }
        lines.push(created);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::proof::sorting::native_owned(lines@)
                + crate::proof::input::plain_rows(read@.skip(sep_idx as int + 1), separator)
                == crate::proof::input::plain_rows(read@, separator));
        }
        index += 1;
        start = sep_idx + 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::input::plain_tail(read@, separator, all_positions); }
    let line = &read[start..];
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost previous_data = *line_data; }
    let created = Line::create(line, index, line_data, token_buffer, settings);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: int| 0 <= i < lines.len() implies
            crate::proof::cached_line(&#[trigger] lines@[i], settings, line_data) by {
            crate::proof::sorting::preserve_cached(&lines@[i], settings, &previous_data, line_data);
        };
        crate::proof::input::owned_push(lines@, &created);
    }
    lines.push(created);
    *line_count_hint = exact_line_count.unwrap_or(index + 1);
}

/// Read from `file` into `buffer`.
///
/// This function makes sure that at least two lines are read (unless we reach EOF and there's no next file),
/// growing the buffer if necessary.
/// The last line is likely to not have been fully read into the buffer. Its bytes must be copied to
/// the front of the buffer for the next invocation so that it can be continued to be read
/// (see the return values and `start_offset`).
///
/// # Arguments
///
/// * `file`: The file to start reading from.
/// * `next_files`: When `file` reaches EOF, it is updated to `next_files.next()` if that is `Some`,
///   and this function continues reading.
/// * `buffer`: The buffer that is filled with bytes. Its contents will mostly be overwritten (see `start_offset`
///   as well). It will be grown up to `max_buffer_size` if necessary, but it will always grow to read at least two lines.
/// * `max_buffer_size`: Grow the buffer to at most this length. If None, the buffer will not grow, unless needed to read at least two lines.
/// * `start_offset`: The amount of bytes at the start of `buffer` that were carried over
///   from the previous read and should not be overwritten.
/// * `separator`: The byte that separates lines.
///
/// # Returns
///
/// * The amount of bytes in `buffer` that can now be interpreted as lines.
///   The remaining bytes must be copied to the start of the buffer for the next invocation,
///   if another invocation is necessary, which is determined by the other return value.
/// * Whether this function should be called again.
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Ghost(budget): Ghost<nat>,
    requires start_offset <= old(buffer).len(),
        crate::trusted_common::io::readable(old(file)),
        old(next_files).obeys_prophetic_iter_laws(), old(next_files).will_return_none(),
        old(next_files).decrease() is Some,
        crate::proof::input::valid_files(old(next_files).remaining()),
        crate::proof::input::pending(old(buffer)@.take(start_offset as int), old(file),
            old(next_files).remaining(), separator).len() <= budget,
    ensures result is Ok,
        crate::trusted_common::io::readable(final(file)),
        (&*final(next_files)).obeys_prophetic_iter_laws(), (&*final(next_files)).will_return_none(),
        (&*final(next_files)).decrease() is Some,
        crate::proof::input::valid_files((&*final(next_files)).remaining()),
        result->Ok_0.0 <= final(buffer).len(),
        if result->Ok_0.1 {
            &&& result->Ok_0.0 > 0
            &&& final(buffer)@[result->Ok_0.0 - 1] == separator
            &&& crate::proof::input::pending(old(buffer)@.take(start_offset as int), old(file), old(next_files).remaining(), separator)
                == final(buffer)@.take(result->Ok_0.0 as int)
                    + crate::proof::input::pending(final(buffer)@.skip(result->Ok_0.0 as int), final(file),
                        (&*final(next_files)).remaining(), separator)
        } else {
            crate::proof::input::pending(old(buffer)@.take(start_offset as int), old(file), old(next_files).remaining(), separator)
                == final(buffer)@.take(result->Ok_0.0 as int)
        },
))]
fn read_to_buffer<T: Read>(
    file: &mut T,
    next_files: &mut impl Iterator<Item = UResult<T>>,
    buffer: &mut Vec<u8>,
    max_buffer_size: Option<usize>,
    start_offset: usize,
    separator: u8,
) -> UResult<(usize, bool)> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost expected = crate::proof::input::pending(buffer@.take(start_offset as int), file, next_files.remaining(), separator);
        let ghost total = expected;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::input::terminated_length(buffer@.take(start_offset as int)
        + crate::trusted_common::io::remaining(file), separator); }
    let mut read_start = start_offset;
    let mut newline_search_offset = 0;
    let mut found_newline = false;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant total == expected, total.len() <= budget,
            total == crate::proof::input::pending(old(buffer)@.take(start_offset as int), old(file),
                old(next_files).remaining(), separator),
            read_start <= buffer.len(), newline_search_offset <= read_start,
            crate::trusted_common::io::readable(file),
            vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(&*next_files),
            vstd::std_specs::iter::IteratorSpec::will_return_none(&*next_files),
            vstd::std_specs::iter::IteratorSpec::decrease(&*next_files) is Some,
            crate::proof::input::valid_files(vstd::std_specs::iter::IteratorSpec::remaining(&*next_files)),
            total == crate::proof::input::pending(buffer@.take(read_start as int), file,
                vstd::std_specs::iter::IteratorSpec::remaining(&*next_files), separator),
            read_start <= total.len(),
        decreases budget - read_start, vstd::std_specs::iter::IteratorSpec::decrease(&*next_files)->Some_0,
            if read_start == buffer.len() { 1int } else { 0int },
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_prefix = buffer@.take(read_start as int);
            let ghost previous_rest = crate::trusted_common::io::remaining(file);
            let ghost previous_start = read_start;
            let ghost previous_decrease = vstd::std_specs::iter::IteratorSpec::decrease(&*next_files);
            let ghost previous_full = read_start == buffer.len(); }
        #[cfg(not(verus_keep_ghost))]
        let read_result = file.read(&mut buffer[read_start..]);
        #[cfg(verus_keep_ghost)]
        let read_result = crate::trusted::input::read_buffer(file, buffer, read_start);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(buffer@.take(read_start + read_result->Ok_0 as int)
                + crate::trusted_common::io::remaining(file) =~= previous_prefix + previous_rest);
        }
        match read_result {
            Ok(0) => {
                if read_start == buffer.len() {
                    // chunk is full
                    if match max_buffer_size { Some(max_buf_size) => max_buf_size > buffer.len(), None => false } {
                        // we can grow the buffer
                        let prev_len = buffer.len();
                        #[cfg(verus_keep_ghost)]
                        let _ = crate::trusted::bounded_bytes(buffer);
                        buffer.resize(prev_len + ALLOC_CHUNK_SIZE, 0);
                        read_start = prev_len;
                        continue;
                    }

                    let search_start = newline_search_offset;
                    #[cfg(not(verus_keep_ghost))]
                    let mut sep_iter = memchr_iter(separator, &buffer[search_start..buffer.len()]).rev();
                    #[cfg(verus_keep_ghost)]
                    let mut sep_iter = crate::trusted::input::separator_positions(
                        separator, &buffer[search_start..buffer.len()]).into_iter().rev();
                    newline_search_offset = buffer.len();
                    if let Some(last_line_end) = sep_iter.next() {
                        if found_newline || sep_iter.next().is_some() {
                            // We read enough lines.
                            // We want to include the separator here, because it shouldn't be carried over.
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                crate::proof::input::split_pending(buffer@,
                                    search_start + last_line_end + 1, file,
                                    vstd::std_specs::iter::IteratorSpec::remaining(&*next_files), separator);
                                assert(buffer@.take(read_start as int) =~= buffer@);
                                assert(total == buffer@.take(search_start + last_line_end + 1)
                                    + crate::proof::input::pending(buffer@.skip(search_start + last_line_end + 1),
                                        file, vstd::std_specs::iter::IteratorSpec::remaining(&*next_files), separator));
                            }
                            return Ok((search_start + last_line_end + 1, true));
                        }
                        found_newline = true;
                    }

                    // We need to read more lines
                    let len = buffer.len();
                    #[cfg(verus_keep_ghost)]
                    let _ = crate::trusted::bounded_bytes(buffer);
                    buffer.resize(len + ALLOC_CHUNK_SIZE, 0);
                    read_start = len;
                } else {
                    // This file has been fully read.
                    let mut leftover_len = buffer.len() - read_start;
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(crate::trusted_common::io::remaining(file).len() == 0);
                        assert(buffer@.take(read_start as int) + crate::trusted_common::io::remaining(file)
                            =~= buffer@.take(read_start as int));
                    }
                    // Decide from buffered bytes: a file may span calls, so a 0-byte read can
                    // still leave an unterminated tail that must be separated from the next file.
                    let read_len = buffer.len() - leftover_len;
                    if read_len > 0 && buffer[read_len - 1] != separator {
                        // The data so far does not end with a separator. We have to insert one.
                        // `read_target` is non-empty here, so `buffer[read_len]` is in bounds.
                        buffer[read_len] = separator;
                        leftover_len -= 1;
                    }
                    let read_len = buffer.len() - leftover_len;
                    read_start = read_len;
                    #[cfg(verus_keep_ghost)]
                    proof_decl! { let ghost next = vstd::std_specs::iter::IteratorSpec::remaining(&*next_files); }
                    if let Some(next_file) = next_files.next() {
                        // There is another file.
                        #[cfg(verus_keep_ghost)]
                        proof! { crate::proof::input::advance_file(buffer@.take(read_start as int), next, separator); }
                        *file = next_file?;
                    } else {
                        // This was the last file.
                        let read_len = buffer.len() - leftover_len;
                        #[cfg(verus_keep_ghost)]
                        proof! { assert(total == buffer@.take(read_len as int)); }
                        return Ok((read_len, false));
                    }
                }
            }
            Ok(n) => {
                read_start += n;
                #[cfg(verus_keep_ghost)]
                proof! { crate::proof::input::terminated_length(buffer@.take(read_start as int)
                    + crate::trusted_common::io::remaining(file), separator); }
            }
            #[cfg(not(verus_keep_ghost))]
            Err(e) if e.kind() == ErrorKind::Interrupted => {
                // retry
            }
            #[cfg(not(verus_keep_ghost))]
            Err(error) => {
                return Err(SortError::ChunkReadFailed { error }.into());
            }
            #[cfg(verus_keep_ghost)]
            Err(error) => { proof! { assert(false); } return Err(error.into()); }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(read_start > previous_start
                || (read_start == previous_start
                    && vstd::std_specs::iter::IteratorSpec::decrease(&*next_files)->Some_0 < previous_decrease->Some_0)
                || (read_start == previous_start
                    && vstd::std_specs::iter::IteratorSpec::decrease(&*next_files) == previous_decrease
                    && previous_full && read_start < buffer.len()));
        }
    }
}

/// Parse a buffer into a `ChunkContents` suitable for `Chunk::try_new`.
/// Used by the WASI single-threaded sort path.
#[cfg(target_os = "wasi")]
pub fn parse_into_chunk<'a>(
    buffer: &'a [u8],
    separator: u8,
    settings: &GlobalSettings,
) -> ChunkContents<'a> {
    let mut lines = Vec::new();
    let mut line_data = LineData::default();
    let mut token_buffer = Vec::new();
    let mut line_count_hint = 0;
    parse_lines(
        buffer,
        &mut lines,
        &mut line_data,
        &mut token_buffer,
        &mut line_count_hint,
        separator,
        settings,
    );
    ChunkContents {
        lines,
        line_data,
        token_buffer,
        line_count_hint,
    }
}
