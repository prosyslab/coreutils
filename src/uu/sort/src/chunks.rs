// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

#![allow(dead_code)]
use crate::SortResult as UResult;
use crate::{
    GeneralBigDecimalParseResult, GlobalSettings, Line, SortError, numeric_str_cmp::NumInfo,
};
use memchr::memchr_iter;
use self_cell::self_cell;
use std::{
    io::{ErrorKind, Read},
    ops::Range,
    sync::mpsc::SyncSender,
};
const ALLOC_CHUNK_SIZE: usize = 64 * 1024;
const MAX_TOKEN_BUFFER_BYTES: usize = 4 * 1024 * 1024;
const MAX_TOKEN_BUFFER_ELEMS: usize = MAX_TOKEN_BUFFER_BYTES / size_of::<Range<usize>>();
self_cell ! (# [doc = " The chunk that is passed around between threads."] pub struct Chunk { owner : Vec < u8 >, # [covariant] dependent : ChunkContents , } impl { Debug });
#[derive(Debug)]
pub struct ChunkContents<'a> {
    pub lines: Vec<Line<'a>>,
    pub line_data: LineData<'a>,
    pub token_buffer: Vec<Range<usize>>,
    pub line_count_hint: usize,
}
#[derive(Debug, Default)]
pub struct LineData<'a> {
    pub selections: Vec<&'a [u8]>,
    pub num_infos: Vec<NumInfo>,
    pub parsed_floats: Vec<GeneralBigDecimalParseResult>,
    pub line_num_floats: Vec<Option<f64>>,
    pub collation_key_buffer: Vec<u8>,
    pub collation_key_ends: Vec<usize>,
}
impl LineData<'_> {
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
fn recycle_contents(_owner: &Vec<u8>, contents: &mut ChunkContents<'_>) -> RecycledChunk {
    contents.lines.clear();
    contents.line_data.selections.clear();
    contents.line_data.num_infos.clear();
    contents.line_data.parsed_floats.clear();
    contents.line_data.line_num_floats.clear();
    contents.line_data.collation_key_buffer.clear();
    contents.line_data.collation_key_ends.clear();
    contents.token_buffer.clear();
    let lines = crate::trusted::ownership::cast_empty_lines(std::mem::take(&mut contents.lines));
    let selections = crate::trusted::ownership::cast_empty_selections(std::mem::take(
        &mut contents.line_data.selections,
    ));
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
        buffer: Vec::new(),
    };
    result
}
impl Chunk {
    pub fn recycle(self) -> RecycledChunk {
        let mut chunk = self;
        let mut recycled_contents = chunk.with_dependent_mut(recycle_contents);
        recycled_contents.buffer = chunk.into_owner();
        recycled_contents
    }
    pub fn lines(&self) -> &Vec<Line<'_>> {
        &self.borrow_dependent().lines
    }
    pub fn line_data(&self) -> &LineData<'_> {
        &self.borrow_dependent().line_data
    }
}
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
        result
    }
}
#[allow(clippy::too_many_arguments)]
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
        buffer.extend_from_slice(&carry_over[buffer.len()..]);
    }
    crate::trusted::input::copy_prefix(&mut buffer, carry_over);
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
    if read != 0 {
        let payload: UResult<Chunk> =
            Chunk::try_new(buffer, |buffer: &Vec<u8>| -> UResult<ChunkContents<'_>> {
                build_chunk_contents(
                    buffer,
                    read,
                    lines,
                    selections,
                    num_infos,
                    parsed_floats,
                    line_num_floats,
                    collation_key_buffer,
                    collation_key_ends,
                    token_buffer,
                    line_count_hint,
                    separator,
                    settings,
                )
            });
        let payload = payload?;
        crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send(sender, payload));
    }
    Ok(should_continue)
}
#[allow(clippy::too_many_arguments)]
fn build_chunk_contents<'a>(
    buffer: &'a Vec<u8>,
    read: usize,
    lines: Vec<Line<'static>>,
    selections: Vec<&'static [u8]>,
    num_infos: Vec<NumInfo>,
    parsed_floats: Vec<GeneralBigDecimalParseResult>,
    line_num_floats: Vec<Option<f64>>,
    collation_key_buffer: Vec<u8>,
    collation_key_ends: Vec<usize>,
    mut token_buffer: Vec<Range<usize>>,
    mut line_count_hint: usize,
    separator: u8,
    settings: &GlobalSettings,
) -> UResult<ChunkContents<'a>> {
    let selections = crate::trusted::ownership::cast_empty_selections(selections);
    let mut lines = crate::trusted::ownership::cast_empty_lines(lines);
    let read = &buffer[..read];
    let read = crate::trusted::bounded_bytes(read);
    let mut line_data = LineData {
        selections,
        num_infos,
        parsed_floats,
        line_num_floats,
        collation_key_buffer,
        collation_key_ends,
    };
    parse_lines(
        read,
        &mut lines,
        &mut line_data,
        &mut token_buffer,
        &mut line_count_hint,
        separator,
        settings,
    );
    let result = ChunkContents {
        lines,
        line_data,
        token_buffer,
        line_count_hint,
    };
    Ok(result)
}
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
    let terminator = [separator];
    let read = match crate::trusted_common::strip_suffix(read, &terminator) {
        Some(prefix) => prefix,
        None => read,
    };
    token_buffer.clear();
    let mut estimated = (*line_count_hint).max(1);
    let mut exact_line_count = None;
    if *line_count_hint == 0 || read.len() <= SMALL_CHUNK_BYTES {
        let count = if read.is_empty() {
            1
        } else {
            let separators = crate::trusted::input::separator_positions(separator, read).len();
            separators + 1
        };
        exact_line_count = Some(count);
        estimated = count;
    } else if estimated == 1 {
        const LINE_LEN_HINT: usize = 128;
        {
            estimated = (read.len() / LINE_LEN_HINT).max(1).min(1024);
        }
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
    let separator_iter = crate::trusted::input::separator_positions(separator, read);
    for sep_idx in separator_iter {
        let line = &read[start..sep_idx];
        let created = Line::create(line, index, line_data, token_buffer, settings);
        lines.push(created);
        index += 1;
        start = sep_idx + 1;
    }
    let line = &read[start..];
    let created = Line::create(line, index, line_data, token_buffer, settings);
    lines.push(created);
    *line_count_hint = exact_line_count.unwrap_or(index + 1);
}
fn read_to_buffer<T: Read>(
    file: &mut T,
    next_files: &mut impl Iterator<Item = UResult<T>>,
    buffer: &mut Vec<u8>,
    max_buffer_size: Option<usize>,
    start_offset: usize,
    separator: u8,
) -> UResult<(usize, bool)> {
    let mut read_start = start_offset;
    let mut newline_search_offset = 0;
    let mut found_newline = false;
    loop {
        let read_result = crate::trusted::input::read_buffer(file, buffer, read_start);
        match read_result {
            Ok(0) => {
                if read_start == buffer.len() {
                    if match max_buffer_size {
                        Some(max_buf_size) => max_buf_size > buffer.len(),
                        None => false,
                    } {
                        let prev_len = buffer.len();
                        let _ = crate::trusted::bounded_bytes(buffer);
                        buffer.resize(prev_len + ALLOC_CHUNK_SIZE, 0);
                        read_start = prev_len;
                        continue;
                    }
                    let search_start = newline_search_offset;
                    let mut sep_iter = crate::trusted::input::separator_positions(
                        separator,
                        &buffer[search_start..buffer.len()],
                    )
                    .into_iter()
                    .rev();
                    newline_search_offset = buffer.len();
                    if let Some(last_line_end) = sep_iter.next() {
                        if found_newline || sep_iter.next().is_some() {
                            return Ok((search_start + last_line_end + 1, true));
                        }
                        found_newline = true;
                    }
                    let len = buffer.len();
                    let _ = crate::trusted::bounded_bytes(buffer);
                    buffer.resize(len + ALLOC_CHUNK_SIZE, 0);
                    read_start = len;
                } else {
                    let mut leftover_len = buffer.len() - read_start;
                    let read_len = buffer.len() - leftover_len;
                    if read_len > 0 && buffer[read_len - 1] != separator {
                        buffer[read_len] = separator;
                        leftover_len -= 1;
                    }
                    let read_len = buffer.len() - leftover_len;
                    read_start = read_len;
                    if let Some(next_file) = next_files.next() {
                        *file = next_file?;
                    } else {
                        let read_len = buffer.len() - leftover_len;
                        return Ok((read_len, false));
                    }
                }
            }
            Ok(n) => {
                read_start += n;
            }
            Err(error) => {
                return Err(error.into());
            }
        }
    }
}
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
