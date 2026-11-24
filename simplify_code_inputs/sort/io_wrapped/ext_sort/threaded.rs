// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::original::Output;
use crate::original::SortResult as UResult;
use crate::original::chunks::RecycledChunk;
use crate::original::merge::WriteableCompressedTmpFile;
use crate::original::merge::WriteablePlainTmpFile;
use crate::original::merge::WriteableTmpFile;
use crate::original::tmp_dir::{TmpDirWrapper, TmpPath};
use crate::original::{
    GlobalSettings, Line,
    chunks::{self, Chunk},
    compare_by, merge, print_sorted, sort_by,
};
use itertools::Itertools;
use std::cmp::Ordering;
use std::fs::File;
use std::io::{Read, Write, stderr};
use std::iter;
use std::sync::mpsc::{Receiver, SyncSender};
use std::thread;
use uucore::error::strip_errno;
use vstd::prelude::*;
type SortReceiver = crate::original::trusted::concurrency::PipeConsumer<Chunk, Chunk, SortPipeTask>;
type SortSender<'a> =
    crate::original::trusted::concurrency::PipeProducer<'a, Chunk, Chunk, SortPipeTask>;
const DEFAULT_BUF_SIZE: usize = 8 * 1024;
pub struct SortPipeTask {
    pub(crate) settings: GlobalSettings,
}
impl crate::original::trusted::concurrency::PipeTask<Chunk, Chunk> for SortPipeTask {
    fn run(&self, receiver: &Receiver<Chunk>, sender: &SyncSender<Chunk>) {
        sorter(receiver, sender, &self.settings);
    }
}
pub(crate) fn pipe_complete(
    receiver: &crate::original::trusted::concurrency::PipeConsumer<Chunk, Chunk, SortPipeTask>,
) {
    receiver.completed();
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub fn ext_sort(
    files: &mut impl Iterator<Item = UResult<crate::original::InputReader>>,
    settings: &GlobalSettings,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    let (recycled_sender, recycled_receiver) = crate::original::trusted::concurrency::channel(1);
    let (sorted_sender, sorted_receiver) = crate::original::trusted::concurrency::channel(1);
    let (pending_sender, sorted_receiver) = {
        let task = SortPipeTask {
            settings: crate::original::trusted::concurrency::clone_settings(settings),
        };
        crate::original::trusted::concurrency::launch_pipe(
            recycled_sender,
            recycled_receiver,
            sorted_sender,
            sorted_receiver,
            task,
        )
    };
    let recycled_sender =
        crate::original::trusted::concurrency::bind_producer(pending_sender, &sorted_receiver);
    let effective_settings = crate::original::trusted::concurrency::clone_settings(settings);
    if effective_settings.compress_prog.is_some() {
        { Ok(()) }
    } else {
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = reader_writer::<_, WriteablePlainTmpFile>(
                files,
                &effective_settings,
                &sorted_receiver,
                recycled_sender,
                output,
                tmp_dir,
            );
            io_result
        }
    }
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
fn reader_writer<
    F: Iterator<Item = UResult<crate::original::InputReader>>,
    Tmp: WriteableTmpFile + 'static,
>(
    files: F,
    settings: &GlobalSettings,
    receiver: &SortReceiver,
    sender: SortSender<'_>,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    let separator = settings.line_ending.into();
    let mut buffer_size = settings.buffer_size;
    if settings.buffer_size_is_explicit || buffer_size > 512 * 1024 * 1024 {
        buffer_size /= 2;
    }
    if !settings.buffer_size_is_explicit {
        buffer_size = buffer_size.max(8 * 1024 * 1024);
    }
    let read_result: ReadResult<Tmp> = read_write_loop(
        files,
        tmp_dir,
        separator,
        buffer_size,
        settings,
        receiver,
        sender,
    )?;
    match read_result {
        ReadResult::WroteChunksToFile { tmp_files } => {
            let files = merge::reopen_files(tmp_files);
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result =
                    merge::merge_with_file_limit::<_, _, Tmp>(files, settings, output, tmp_dir);
                io_result
            }?;
        }
        ReadResult::SortedSingleChunk(chunk) => {
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = print_memory_chunk(&chunk, settings, output);
                io_result
            }?;
        }
        ReadResult::SortedTwoChunks(pair) => {
            let a = &pair[0];
            let b = &pair[1];
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = print_memory_chunks(a, b, settings, output);
                io_result
            }?;
        }
        ReadResult::EmptyInput => {
            let empty = crate::original::trusted::iteration::empty::<&Line<'_>>();
            {
                # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
                let io_result = print_sorted(empty, settings, output);
                io_result
            }?;
        }
    }
    Ok(())
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
fn print_memory_chunk(chunk: &Chunk, settings: &GlobalSettings, output: Output) -> UResult<()> {
    {
        let lines = chunk.lines();
        let line_data = chunk.line_data();
        let stream = crate::original::trusted::iteration::slice(&lines[..]);
        let stream = if settings.unique {
            let predicate = |a: &&Line<'_>, b: &&Line<'_>| -> bool {
                matches!(
                    compare_by(a, b, settings, line_data, line_data),
                    Ordering::Equal
                )
            };
            crate::original::trusted::iteration::dedup_by(stream, predicate)
        } else {
            stream
        };
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = print_sorted(stream, settings, output);
            io_result
        }?;
    }
    Ok(())
}
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
fn print_memory_chunks(
    a: &Chunk,
    b: &Chunk,
    settings: &GlobalSettings,
    output: Output,
) -> UResult<()> {
    {
        let a_lines = a.lines();
        let b_lines = b.lines();
        let a_stream = crate::original::trusted::iteration::slice(&a_lines[..]);
        let b_stream = crate::original::trusted::iteration::slice(&b_lines[..]);
        let a_stream = crate::original::trusted::iteration::map(
            a_stream,
            |line: &Line<'_>| -> (&Line<'_>, &Chunk) { (line, a) },
        );
        let b_stream = crate::original::trusted::iteration::map(
            b_stream,
            |line: &Line<'_>| -> (&Line<'_>, &Chunk) { (line, b) },
        );
        let before = |left: &(&Line<'_>, &Chunk), right: &(&Line<'_>, &Chunk)| -> bool {
            !matches!(
                compare_by(
                    left.0,
                    right.0,
                    settings,
                    left.1.line_data(),
                    right.1.line_data()
                ),
                Ordering::Greater
            )
        };
        let merged = crate::original::trusted::iteration::merge_by(a_stream, b_stream, before);
        let merged = if settings.unique {
            let equal = |left: &(&Line<'_>, &Chunk), right: &(&Line<'_>, &Chunk)| -> bool {
                matches!(
                    compare_by(
                        left.0,
                        right.0,
                        settings,
                        left.1.line_data(),
                        right.1.line_data()
                    ),
                    Ordering::Equal
                )
            };
            crate::original::trusted::iteration::dedup_by(merged, equal)
        } else {
            merged
        };
        let lines = crate::original::trusted::iteration::map(
            merged,
            |pair: (&Line<'_>, &Chunk)| -> &Line<'_> { pair.0 },
        );
        {
            # [cfg_attr (verus_keep_ghost , verus_spec (with & mut * state))]
            let io_result = print_sorted(lines, settings, output);
            io_result
        }?;
    }
    Ok(())
}
fn sorter(receiver: &Receiver<Chunk>, sender: &SyncSender<Chunk>, settings: &GlobalSettings) {
    while let Ok(mut payload) = { { crate::original::trusted::concurrency::recv(receiver) } } {
        sort_payload(&mut payload, settings);
        let sent = crate::original::trusted::concurrency::send(sender, payload);
        if matches!(sent, Err(_)) {
            return;
        }
    }
}
struct SortContents<'s> {
    settings: &'s GlobalSettings,
}
impl<'s> crate::original::proof::unwind::ContentsMutator for SortContents<'s> {
    type Output = ();
    fn run<'a>(
        &self,
        _owner: &'a Vec<u8>,
        contents: &mut crate::original::chunks::ChunkContents<'a>,
    ) {
        sort_by(&mut contents.lines, self.settings, &contents.line_data);
    }
}
fn sort_payload(payload: &mut Chunk, settings: &GlobalSettings) {
    crate::original::trusted::unwind::with_dependent_mut(payload, &SortContents { settings });
}
pub(crate) enum ReadResult<I: WriteableTmpFile> {
    #[doc = " The input was empty. Nothing was read."]
    EmptyInput,
    #[doc = " The input fits into a single Chunk, which was kept in memory."]
    SortedSingleChunk(Chunk),
    #[doc = " The input fits into two chunks, which were kept in memory."]
    SortedTwoChunks([Chunk; 2]),
    #[doc = " The input was read into multiple chunks, which were written to auxiliary files."]
    WroteChunksToFile { tmp_files: Vec<I::Closed> },
}
fn read_write_loop<I: WriteableTmpFile>(
    mut files: impl Iterator<Item = UResult<crate::original::InputReader>>,
    tmp_dir: &mut TmpDirWrapper,
    separator: u8,
    buffer_size: usize,
    settings: &GlobalSettings,
    receiver: &SortReceiver,
    sender: SortSender<'_>,
) -> UResult<ReadResult<I>> {
    let consumer = receiver;
    let receiver = consumer.receiver();
    let mut file = files.next().unwrap()?;
    let mut carry_over = vec![];
    for _ in 0..2 {
        let raw_sender = sender.sender();
        let should_continue = chunks::read(
            raw_sender,
            RecycledChunk::new(buffer_size.min(DEFAULT_BUF_SIZE)),
            Some(buffer_size),
            &mut carry_over,
            &mut file,
            &mut files,
            separator,
            settings,
        )?;
        if !should_continue {
            sender.close();
            {
                let first = crate::original::trusted::concurrency::recv(receiver);
                let result: ReadResult<I> = if let Ok(first_chunk) = first {
                    let second = crate::original::trusted::concurrency::recv(receiver);
                    if let Ok(second_chunk) = second {
                        ReadResult::SortedTwoChunks([first_chunk, second_chunk])
                    } else {
                        pipe_complete(consumer);
                        ReadResult::SortedSingleChunk(first_chunk)
                    }
                } else {
                    pipe_complete(consumer);
                    ReadResult::EmptyInput
                };
                return Ok(result);
            }
        }
    }
    let mut sender_option = Some(sender);
    let mut tmp_files = vec![];
    loop {
        let message = { { crate::original::trusted::concurrency::recv(receiver) } };
        let Ok(chunk) = message else {
            if let Some(producer) = &sender_option {
                producer.reject_eof();
            }
            pipe_complete(consumer);
            {
                let result = ReadResult::<I>::WroteChunksToFile { tmp_files };
                return Ok(result);
            }
        };
        let (new_file,) = crate::original::trusted::temporary::new_file(tmp_dir);
        let compress_prog =
            crate::original::trusted::temporary::optional_str(&settings.compress_prog);
        let tmp_file = write::<I>(&chunk, new_file?, compress_prog, separator)?;
        tmp_files.push(tmp_file);
        let recycled_chunk = chunk.recycle();
        if let Some(sender) = &sender_option {
            let sender = sender.sender();
            let should_continue = chunks::read(
                sender,
                recycled_chunk,
                None,
                &mut carry_over,
                &mut file,
                &mut files,
                separator,
                settings,
            )?;
            if !should_continue {
                {
                    let producer = sender_option.take().unwrap();
                    producer.close();
                }
            }
        }
    }
}
fn write<I: WriteableTmpFile>(
    chunk: &Chunk,
    file: (File, TmpPath),
    compress_prog: Option<&str>,
    separator: u8,
) -> UResult<I::Closed> {
    let mut tmp_file = I::create(file, compress_prog)?;
    write_lines(chunk.lines(), tmp_file.as_write(), separator)?;
    { tmp_file.finished_writing() }
}
fn write_lines<T: Write>(lines: &[Line], writer: &mut T, separator: u8) -> std::io::Result<()> {
    for s in lines {
        crate::original::trusted::write_output(writer, s.line)?;
        crate::original::trusted::write_output(writer, &[separator])?;
    }
    Ok(())
}
