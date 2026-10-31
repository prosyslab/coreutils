// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

//! Threaded external sort: read input in chunks, sort them in a background
//! thread, and spill to temporary files when memory is exceeded.

use std::cmp::Ordering;
use std::fs::File;
use std::io::{Read, Write, stderr};
use std::iter;
use std::sync::mpsc::{Receiver, SyncSender};
use std::thread;

use itertools::Itertools;
use uucore::error::strip_errno;
use crate::SortResult as UResult;

use crate::Output;
use crate::chunks::RecycledChunk;
use crate::merge::WriteableCompressedTmpFile;
use crate::merge::WriteablePlainTmpFile;
use crate::merge::WriteableTmpFile;
use crate::tmp_dir::{TmpDirWrapper, TmpPath};
use crate::{
    GlobalSettings, Line,
    chunks::{self, Chunk},
    compare_by, merge, print_sorted, sort_by,
};
#[cfg(verus_keep_ghost)]
use vstd::{prelude::*, std_specs::iter::IteratorSpec};
#[cfg(verus_keep_ghost)]
use crate::_VERUS_VERIFIED_print_sorted;
#[cfg(verus_keep_ghost)]
use crate::proof::temporary::{WriterModel, ClosedModel, InputModel};

#[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
type SortReceiver = Receiver<Chunk>;
#[cfg(all(verus_keep_ghost, uutils_sort_full))]
type SortReceiver = crate::trusted::concurrency::PipeConsumer<Chunk, Chunk, SortPipeTask>;
#[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
type SortSender<'a> = SyncSender<Chunk>;
#[cfg(all(verus_keep_ghost, uutils_sort_full))]
type SortSender<'a> = crate::trusted::concurrency::PipeProducer<'a, Chunk, Chunk, SortPipeTask>;

// Note: update `test_sort::test_start_buffer` if this size is changed
// Fixed to 8 KiB (equivalent to `std::sys::io::DEFAULT_BUF_SIZE` on most targets)
#[cfg_attr(verus_keep_ghost, verus_verify)]
const DEFAULT_BUF_SIZE: usize = 8 * 1024;

#[cfg(verus_keep_ghost)]
#[verus_verify]
pub struct SortPipeTask { pub(crate) settings: GlobalSettings }

#[cfg(verus_keep_ghost)]
verus! {
    impl crate::trusted::concurrency::PipeTask<Chunk, Chunk> for SortPipeTask {
        #[verifier::prophetic]
        closed spec fn ready(&self, input: &crate::trusted::concurrency::RecvState<Chunk>,
            output: &crate::trusted::concurrency::SendState<Chunk>) -> bool
        {
            &&& crate::proof::native_settings_valid(&self.settings)
            &&& crate::trusted::unwind::rayon_ready()
            &&& input.index() == 0 && output.index() == 0 && input.limit() == output.limit()
            &&& !input.peer_closed() && !output.peer_closed()
            &&& !output.own_closed()
            &&& forall|i: nat, chunk: Chunk| #[trigger] input.rule()(i, chunk)
                ==> crate::proof::pipeline::input_message(chunk, &self.settings)
            &&& forall|i: nat, chunk: Chunk| i < crate::trusted::concurrency::channel_trace::<Chunk>(input.id()).len()
                && crate::proof::pipeline::sorted_message(
                    crate::trusted::concurrency::channel_trace::<Chunk>(input.id())[i as int], chunk, &self.settings)
                ==> #[trigger] output.rule()(i, chunk)
        }
        #[verifier::prophetic]
        closed spec fn post(&self, input_before: &crate::trusted::concurrency::RecvState<Chunk>,
            output_before: &crate::trusted::concurrency::SendState<Chunk>,
            input_after: &crate::trusted::concurrency::RecvState<Chunk>,
            output_after: &crate::trusted::concurrency::SendState<Chunk>) -> bool
        {
            &&& input_after.id() == input_before.id() && output_after.id() == output_before.id()
            &&& input_after.rule() == input_before.rule() && output_after.rule() == output_before.rule()
            &&& input_after.limit() == input_before.limit() && output_after.limit() == output_before.limit()
            &&& output_after.index() <= input_after.index() <= output_after.index() + 1
            &&& crate::proof::pipeline::forwarded(input_before.id(), output_before.id(), output_after.index(), &self.settings)
            &&& (input_after.peer_closed() ==> input_after.index() == output_after.index()
                && input_after.index() == crate::trusted::concurrency::channel_trace::<Chunk>(input_before.id()).len())
        }
        fn run(&self, receiver: &Receiver<Chunk>, sender: &SyncSender<Chunk>,
            Tracked(input): Tracked<&mut crate::trusted::concurrency::RecvState<Chunk>>,
            Tracked(output): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>)
        {
            proof! {
                reveal(<SortPipeTask as crate::trusted::concurrency::PipeTask<Chunk, Chunk>>::ready);
                reveal(<SortPipeTask as crate::trusted::concurrency::PipeTask<Chunk, Chunk>>::post);
            }
            _VERUS_VERIFIED_sorter(receiver, sender, &self.settings, Tracked(&mut *input), Tracked(&mut *output));
        }
    }

    pub(crate) fn pipe_complete(
        receiver: &crate::trusted::concurrency::PipeConsumer<Chunk, Chunk, SortPipeTask>,
        Tracked(received): Tracked<&crate::trusted::concurrency::RecvState<Chunk>>,
    )
        requires received.id() == receiver.output_before().id(), received.peer_closed(),
            received.index() == crate::trusted::concurrency::channel_trace::<Chunk>(receiver.output_before().id()).len(),
        ensures received.index() == crate::trusted::concurrency::channel_trace::<Chunk>(receiver.input_before().id()).len(),
            crate::trusted::concurrency::channel_trace::<Chunk>(receiver.input_before().id()).len()
                == crate::trusted::concurrency::channel_trace::<Chunk>(receiver.output_before().id()).len(),
            crate::proof::pipeline::forwarded(receiver.input_before().id(), receiver.output_before().id(),
                received.index(), &receiver.task().settings),
        no_unwind
    {
        receiver.completed(Tracked(received));
        proof! { reveal(<SortPipeTask as crate::trusted::concurrency::PipeTask<Chunk, Chunk>>::post); }
    }
}

/// Sort files by using auxiliary files for storing intermediate chunks (if needed), and output the result.
///
/// Two threads cooperate: one reads input and writes temporary chunk files,
/// while the other sorts each chunk in memory. Once all chunks are written,
/// they are merged back together for final output.
#[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(result =>
    with Ghost(bytes): Ghost<Seq<u8>>, Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires crate::proof::native_settings_valid(settings), crate::trusted::unwind::rayon_ready(),
        old(log).session() == crate::trusted::output_session(output),
        vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(old(files)),
        vstd::std_specs::iter::IteratorSpec::will_return_none(old(files)),
        vstd::std_specs::iter::IteratorSpec::decrease(old(files)) is Some,
        crate::proof::input::valid_files(vstd::std_specs::iter::IteratorSpec::remaining(old(files))),
        vstd::std_specs::iter::IteratorSpec::remaining(old(files)).len() > 0,
        bytes == crate::proof::input::file_bytes(vstd::std_specs::iter::IteratorSpec::remaining(old(files)),
            crate::proof::native_ending(settings)),
    ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
        final(log).bytes() == crate::proof::upstream_output(bytes, settings),
))]
pub fn ext_sort(
    files: &mut impl Iterator<Item = UResult<crate::InputReader>>,
    settings: &GlobalSettings,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! { crate::proof::native_settings_facts(settings); }
    #[cfg(any(not(verus_keep_ghost), not(uutils_sort_full)))]
    let (sorted_sender, sorted_receiver) = std::sync::mpsc::sync_channel(1);
    #[cfg(any(not(verus_keep_ghost), not(uutils_sort_full)))]
    let (recycled_sender, recycled_receiver) = std::sync::mpsc::sync_channel(1);
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let (recycled_sender, recycled_receiver, input_sending, input_receiving) = verus_exec_expr! {
        crate::trusted::concurrency::channel(1, Ghost(0),
            Ghost(crate::proof::pipeline::input_template(settings)), Ghost(bytes.len()))
    };
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let (sorted_sender, sorted_receiver, output_sending, output_receiving) = verus_exec_expr! {
        crate::trusted::concurrency::channel(1, Ghost(input_sending@.id()),
            Ghost(crate::proof::pipeline::output_template(settings)), Ghost(bytes.len()))
    };
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! { crate::proof::producer::establish_payloads(input_sending@.id(), output_receiving@.id(), settings); }
    #[cfg(any(not(verus_keep_ghost), not(uutils_sort_full)))]
    thread::spawn({
        let settings = settings.clone();
        move || sorter(&recycled_receiver, &sorted_sender, &settings)
    });
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let (pending_sender, sorted_receiver, input_sending, output_receiving) = verus_exec_expr! { {
        let task = SortPipeTask { settings: crate::trusted::concurrency::clone_settings(settings) };
        proof! {
            reveal(<SortPipeTask as crate::trusted::concurrency::PipeTask<Chunk, Chunk>>::ready);
            assert forall|i: nat, chunk: Chunk| #[trigger] input_receiving@.rule()(i, chunk)
                implies crate::proof::pipeline::input_message(chunk, &task.settings) by { };
            assert forall|i: nat, chunk: Chunk| i < crate::trusted::concurrency::channel_trace::<Chunk>(input_receiving@.id()).len()
                && crate::proof::pipeline::sorted_message(
                    crate::trusted::concurrency::channel_trace::<Chunk>(input_receiving@.id())[i as int], chunk, &task.settings)
                implies #[trigger] output_sending@.rule()(i, chunk) by { };
        }
        crate::trusted::concurrency::launch_pipe(
            recycled_sender, recycled_receiver, sorted_sender, sorted_receiver, task,
            input_sending, input_receiving, output_sending, output_receiving)
    } };
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let recycled_sender = crate::trusted::concurrency::bind_producer(pending_sender, &sorted_receiver);

    // Test if compression program exists and works, disable if not
    #[cfg(not(verus_keep_ghost))]
    let mut effective_settings = settings.clone();
    #[cfg(verus_keep_ghost)]
    let effective_settings = crate::trusted::concurrency::clone_settings(settings);
    #[cfg(not(verus_keep_ghost))]
    if let Some(ref prog) = settings.compress_prog {
        // Test the compression program by trying to spawn it
        match std::process::Command::new(prog)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
        {
            Ok(mut child) => {
                // Kill the test process immediately
                let _ = child.kill();
            }
            Err(err) => {
                // Print the error and disable compression
                let _ = writeln!(
                    stderr(),
                    "sort: could not run compress program '{prog}': {}",
                    strip_errno(&err)
                );
                effective_settings.compress_prog = None;
            }
        }
    }

    if effective_settings.compress_prog.is_some() {
        #[cfg(not(verus_keep_ghost))]
        {
            reader_writer::<_, WriteableCompressedTmpFile>(
                files,
                &effective_settings,
                &sorted_receiver,
                recycled_sender,
                output,
                tmp_dir,
            )
        }
        #[cfg(verus_keep_ghost)]
        { proof! { assert(false); } Ok(()) }
    } else {
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_decl! {
            let tracked mut sending = input_sending.get();
            let tracked mut receiving = output_receiving.get();
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Ghost(bytes), Tracked(&mut *log), Tracked(&mut sending), Tracked(&mut receiving) }
        reader_writer::<_, WriteablePlainTmpFile>(
            files,
            &effective_settings,
            &sorted_receiver,
            recycled_sender,
            output,
            tmp_dir,
        )
    }
}

#[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(result =>
    with Ghost(bytes): Ghost<Seq<u8>>, Tracked(log): Tracked<&mut crate::proof::OutputLog>,
        Tracked(sending): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>,
        Tracked(receiving): Tracked<&mut crate::trusted::concurrency::RecvState<Chunk>>,
    requires crate::proof::native_settings_valid(settings), Tmp::supported(),
        crate::proof::producer::ready(&sender, receiver, old(sending), old(receiving), settings, bytes.len()),
        vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(&files),
        vstd::std_specs::iter::IteratorSpec::will_return_none(&files),
        vstd::std_specs::iter::IteratorSpec::decrease(&files) is Some,
        vstd::std_specs::iter::IteratorSpec::remaining(&files).len() > 0,
        crate::proof::input::valid_files(vstd::std_specs::iter::IteratorSpec::remaining(&files)),
        bytes == crate::proof::input::file_bytes(vstd::std_specs::iter::IteratorSpec::remaining(&files),
            crate::proof::native_ending(settings)),
        old(log).session() == crate::trusted::output_session(output),
    ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
        final(log).bytes() == crate::proof::upstream_output(bytes, settings),
))]
fn reader_writer<
    F: Iterator<Item = UResult<crate::InputReader>>,
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
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! {
        reveal_with_fuel(Seq::flatten, 3);
        crate::proof::native_settings_facts(settings);
        crate::proof::sorting::native_compare_model(settings);
        crate::proof::comparisons::order_lawful(&settings.specification@->Some_0);
        crate::proof::pipeline::output_model(bytes, settings);
    }

    // Two chunks are kept in memory, so split an explicit limit between them.
    // Keep the automatic sizing heuristic's cap and minimum growth allowance.
    let mut buffer_size = settings.buffer_size;
    if settings.buffer_size_is_explicit || buffer_size > 512 * 1024 * 1024 {
        buffer_size /= 2;
    }
    if !settings.buffer_size_is_explicit {
        buffer_size = buffer_size.max(8 * 1024 * 1024);
    }
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof_with! { Ghost(bytes), Tracked(&mut *sending), Tracked(&mut *receiving) }
    let read_result: ReadResult<Tmp> = read_write_loop(
        files,
        tmp_dir,
        separator,
        buffer_size,
        settings,
        receiver,
        sender,
    )?;
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof_decl! {
        let ghost canonical = crate::proof::sorting::canonical_lines(
            crate::proof::sorting::rows_of(bytes, separator), crate::proof::sorting::native_compare(settings));
        let ghost batches = crate::proof::producer::result_batches(&read_result, separator);
    }
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! { assert(crate::proof::sorting::canonical_lines(batches.flatten(), crate::proof::sorting::native_compare(settings)) == canonical); }
    match read_result {
        ReadResult::WroteChunksToFile { tmp_files } => {
            #[cfg(not(verus_keep_ghost))]
            let files = tmp_files.into_iter().map(merge::ClosedTmpFile::reopen);
            #[cfg(verus_keep_ghost)]
            let files = merge::reopen_files(tmp_files);
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_decl! { let ghost merged_rows = crate::proof::merging::input_rows(files.remaining(), settings); }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                assert(merged_rows =~= batches);
                crate::proof::merging::base_lawful(settings);
                crate::proof::sorting::canonical_properties(batches.flatten(), crate::proof::sorting::native_compare(settings));
                assert(crate::proof::merging::output(merged_rows, settings) == crate::proof::upstream_output(bytes, settings));
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Ghost(crate::proof::merging::MergeContext { files: batches }), Tracked(&mut *log) }
            merge::merge_with_file_limit::<_, _, Tmp>(
                files,
                settings,
                output,
                tmp_dir,
            )?;
        }
        ReadResult::SortedSingleChunk(chunk) => {
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                assert(batches =~= seq![crate::proof::producer::rows(&chunk)]);
                assert(batches.flatten() =~= crate::proof::producer::rows(&chunk));
                crate::proof::pipeline::sorted_identity(crate::proof::producer::rows(&chunk),
                    crate::proof::sorting::native_compare(settings));
                assert(crate::proof::producer::rows(&chunk) == canonical);
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Tracked(&mut *log) }
            print_memory_chunk(&chunk, settings, output)?;
        }
        ReadResult::SortedTwoChunks(pair) => {
            let a = &pair[0];
            let b = &pair[1];
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                assert(batches =~= seq![crate::proof::producer::rows(a), crate::proof::producer::rows(b)]);
                assert(batches.flatten() =~= crate::proof::producer::rows(a) + crate::proof::producer::rows(b));
                assert(crate::proof::sorting::canonical_lines(
                    crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                    crate::proof::sorting::native_compare(settings)) == canonical);
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Tracked(&mut *log) }
            print_memory_chunks(a, b, settings, output)?;
        }
        ReadResult::EmptyInput => {
            // output empty too, as coreutils does
            #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
            print_sorted(iter::empty::<&Line<'_>>(), settings, output)?;
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            {
                proof! {
                    crate::proof::sorting::canonical_properties(Seq::empty(), crate::proof::sorting::native_compare(settings));
                    assert(canonical =~= Seq::<crate::proof::sorting::Bytes>::empty());
                }
                let empty = crate::trusted::iteration::empty::<&Line<'_>>();
                proof_with! { Tracked(&mut *log) }
                print_sorted(empty, settings, output)?;
            }
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires crate::proof::native_settings_valid(settings), crate::proof::producer::valid_chunk(chunk, settings),
        old(log).session() == crate::trusted::output_session(output),
    ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
        final(log).bytes() == crate::proof::sorting::emit(crate::proof::sorting::selected_rows(
            crate::proof::producer::rows(chunk), crate::proof::producer::rows(chunk).len() as int,
            settings.unique, crate::proof::sorting::native_compare(settings)), crate::proof::native_ending(settings)),
))]
fn print_memory_chunk(chunk: &Chunk, settings: &GlobalSettings, output: Output) -> UResult<()> {
    #[cfg(not(verus_keep_ghost))]
    {
        if settings.unique {
            print_sorted(chunk.lines().iter().dedup_by(|a, b| {
                compare_by(a, b, settings, chunk.line_data(), chunk.line_data()) == Ordering::Equal
            }), settings, output)?;
        } else { print_sorted(chunk.lines().iter(), settings, output)?; }
    }
    #[cfg(verus_keep_ghost)]
    {
        proof! {
            crate::proof::native_settings_facts(settings);
            crate::proof::sorting::native_compare_model(settings);
            crate::proof::comparisons::order_lawful(&settings.specification@->Some_0);
        }
        let lines = chunk.lines();
        let line_data = chunk.line_data();
        let stream = crate::trusted::iteration::slice(&lines[..]);
        proof! {
            crate::proof::pipeline::refs_valid(stream.values(), &crate::trusted::ownership::contents(chunk), settings);
            assert(crate::proof::sorting::native_lines(stream.values()) == crate::proof::producer::rows(chunk));
        }
        let stream = if settings.unique {
            let predicate = verus_exec_expr! { |a: &&Line<'_>, b: &&Line<'_>| -> (equal: bool)
                requires crate::proof::native_settings_valid(settings),
                    crate::proof::cached_line(*a, settings, line_data), crate::proof::cached_line(*b, settings, line_data),
                ensures equal == (crate::proof::sorting::native_compare(settings)(
                    crate::proof::sorting::native_line(*a), crate::proof::sorting::native_line(*b)) == Ordering::Equal),
                { matches!(compare_by(a, b, settings, line_data, line_data), Ordering::Equal) }
            };
            crate::trusted::iteration::dedup_by(stream, predicate,
                verus_exec_expr! { Ghost(|line: &Line<'_>| crate::proof::sorting::native_line(line)) },
                verus_exec_expr! { Ghost(crate::proof::sorting::native_compare(settings)) })
        } else { stream };
        proof! {
            assert(crate::proof::sorting::native_lines(stream.values()) =~=
                crate::proof::sorting::selected_rows(crate::proof::producer::rows(chunk),
                    crate::proof::producer::rows(chunk).len() as int, settings.unique,
                    crate::proof::sorting::native_compare(settings)));
        }
        proof_with! { Tracked(&mut *log) }
        print_sorted(stream, settings, output)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires crate::proof::native_settings_valid(settings),
        crate::proof::producer::valid_chunk(a, settings), crate::proof::producer::valid_chunk(b, settings),
        old(log).session() == crate::trusted::output_session(output),
    ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
        final(log).bytes() == crate::proof::sorting::emit(crate::proof::sorting::selected_rows(
            crate::proof::sorting::canonical_lines(crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                crate::proof::sorting::native_compare(settings)),
            crate::proof::sorting::canonical_lines(crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                crate::proof::sorting::native_compare(settings)).len() as int,
            settings.unique, crate::proof::sorting::native_compare(settings)), crate::proof::native_ending(settings)),
))]
fn print_memory_chunks(a: &Chunk, b: &Chunk, settings: &GlobalSettings, output: Output) -> UResult<()> {
    #[cfg(not(verus_keep_ghost))]
    {
        let merged_iter = a.lines().iter().map(|line| (line, a)).merge_by(
            b.lines().iter().map(|line| (line, b)), |(line_a, a), (line_b, b)| {
                compare_by(line_a, line_b, settings, a.line_data(), b.line_data()) != Ordering::Greater
            });
        if settings.unique {
            print_sorted(merged_iter.dedup_by(|(line_a, a), (line_b, b)| {
                compare_by(line_a, line_b, settings, a.line_data(), b.line_data()) == Ordering::Equal
            }).map(|(line, _)| line), settings, output)?;
        } else { print_sorted(merged_iter.map(|(line, _)| line), settings, output)?; }
    }
    #[cfg(verus_keep_ghost)]
    {
        proof! {
            crate::proof::native_settings_facts(settings);
            crate::proof::sorting::native_compare_model(settings);
            crate::proof::comparisons::order_lawful(&settings.specification@->Some_0);
        }
        let a_lines = a.lines();
        let b_lines = b.lines();
        let a_stream = crate::trusted::iteration::slice(&a_lines[..]);
        let b_stream = crate::trusted::iteration::slice(&b_lines[..]);
        proof! {
            crate::proof::pipeline::refs_valid(a_stream.values(), &crate::trusted::ownership::contents(a), settings);
            crate::proof::pipeline::refs_valid(b_stream.values(), &crate::trusted::ownership::contents(b), settings);
        }
        let a_stream = crate::trusted::iteration::map(a_stream,
            verus_exec_expr! { |line: &Line<'_>| -> (pair: (&Line<'_>, &Chunk))
                ensures pair == (line, a), { (line, a) } },
            verus_exec_expr! { Ghost(|line: &Line<'_>| (line, a)) });
        let b_stream = crate::trusted::iteration::map(b_stream,
            verus_exec_expr! { |line: &Line<'_>| -> (pair: (&Line<'_>, &Chunk))
                ensures pair == (line, b), { (line, b) } },
            verus_exec_expr! { Ghost(|line: &Line<'_>| (line, b)) });
        proof! {
            assert(a_stream.values().map_values(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0))
                =~= crate::proof::producer::rows(a));
            assert(b_stream.values().map_values(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0))
                =~= crate::proof::producer::rows(b));
            assert((a_stream.values() + b_stream.values()).map_values(
                |pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0))
                =~= crate::proof::producer::rows(a) + crate::proof::producer::rows(b));
        }
        let before = verus_exec_expr! { |left: &(&Line<'_>, &Chunk), right: &(&Line<'_>, &Chunk)| -> (before: bool)
            requires crate::proof::native_settings_valid(settings),
                crate::proof::cached_line(left.0, settings, &crate::trusted::ownership::contents(left.1).line_data),
                crate::proof::cached_line(right.0, settings, &crate::trusted::ownership::contents(right.1).line_data),
            ensures before == (crate::proof::sorting::native_compare(settings)(
                crate::proof::sorting::native_line(left.0), crate::proof::sorting::native_line(right.0)) != Ordering::Greater),
            { !matches!(compare_by(left.0, right.0, settings, left.1.line_data(), right.1.line_data()), Ordering::Greater) }
        };
        let merged = crate::trusted::iteration::merge_by(a_stream, b_stream, before,
            verus_exec_expr! { Ghost(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0)) },
            verus_exec_expr! { Ghost(crate::proof::sorting::native_compare(settings)) });
        proof! {
            crate::proof::sorting::sort_canonical(crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                merged.values().map_values(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0)),
                true, crate::proof::sorting::native_compare(settings));
        }
        let merged = if settings.unique {
            let equal = verus_exec_expr! { |left: &(&Line<'_>, &Chunk), right: &(&Line<'_>, &Chunk)| -> (equal: bool)
                requires crate::proof::native_settings_valid(settings),
                    crate::proof::cached_line(left.0, settings, &crate::trusted::ownership::contents(left.1).line_data),
                    crate::proof::cached_line(right.0, settings, &crate::trusted::ownership::contents(right.1).line_data),
                ensures equal == (crate::proof::sorting::native_compare(settings)(
                    crate::proof::sorting::native_line(left.0), crate::proof::sorting::native_line(right.0)) == Ordering::Equal),
                { matches!(compare_by(left.0, right.0, settings, left.1.line_data(), right.1.line_data()), Ordering::Equal) }
            };
            crate::trusted::iteration::dedup_by(merged, equal,
                verus_exec_expr! { Ghost(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0)) },
                verus_exec_expr! { Ghost(crate::proof::sorting::native_compare(settings)) })
        } else { merged };
        proof_decl! {
            let ghost expected = crate::proof::sorting::selected_rows(
                crate::proof::sorting::canonical_lines(crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                    crate::proof::sorting::native_compare(settings)),
                crate::proof::sorting::canonical_lines(crate::proof::producer::rows(a) + crate::proof::producer::rows(b),
                    crate::proof::sorting::native_compare(settings)).len() as int, settings.unique,
                crate::proof::sorting::native_compare(settings));
        }
        proof! {
            assert(merged.values().map_values(|pair: (&Line<'_>, &Chunk)| crate::proof::sorting::native_line(pair.0))
                =~= expected);
        }
        let lines = crate::trusted::iteration::map(merged,
            verus_exec_expr! { |pair: (&Line<'_>, &Chunk)| -> (line: &Line<'_>) ensures line == pair.0, { pair.0 } },
            verus_exec_expr! { Ghost(|pair: (&Line<'_>, &Chunk)| pair.0) });
        proof! { assert(crate::proof::sorting::native_lines(lines.values()) =~= expected); }
        proof_with! { Tracked(&mut *log) }
        print_sorted(lines, settings, output)?;
    }
    Ok(())
}

/// The function that is executed on the sorter thread.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    with Tracked(input_state): Tracked<&mut crate::trusted::concurrency::RecvState<Chunk>>,
        Tracked(output_state): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>,
    requires crate::proof::native_settings_valid(settings),
        crate::trusted::unwind::rayon_ready(),
        crate::trusted::concurrency::receiver_id(receiver) == old(input_state).id(),
        crate::trusted::concurrency::sender_id(sender) == old(output_state).id(),
        old(input_state).index() == 0, old(output_state).index() == 0,
        !old(input_state).peer_closed(), !old(output_state).peer_closed(),
        !old(output_state).own_closed(),
        old(input_state).limit() == old(output_state).limit(),
        forall|i: nat, chunk: Chunk| #[trigger] old(input_state).rule()(i, chunk)
            ==> crate::proof::pipeline::input_message(chunk, settings),
        forall|i: nat, chunk: Chunk| 0 <= i < crate::trusted::concurrency::channel_trace::<Chunk>(old(input_state).id()).len()
            && crate::proof::pipeline::sorted_message(
                crate::trusted::concurrency::channel_trace::<Chunk>(old(input_state).id())[i as int], chunk, settings)
            ==> #[trigger] old(output_state).rule()(i, chunk),
    ensures final(input_state).id() == old(input_state).id(), final(output_state).id() == old(output_state).id(),
        final(input_state).rule() == old(input_state).rule(), final(output_state).rule() == old(output_state).rule(),
        final(input_state).limit() == old(input_state).limit(), final(output_state).limit() == old(output_state).limit(),
        crate::trusted::concurrency::same_recv_channel(old(input_state), final(input_state)),
        crate::trusted::concurrency::same_send_channel(old(output_state), final(output_state)),
        final(output_state).index() <= final(input_state).index() <= final(output_state).index() + 1,
        final(input_state).peer_closed() || final(output_state).peer_closed(),
        final(input_state).peer_closed() ==> final(input_state).index() == final(output_state).index()
            && final(input_state).index() == crate::trusted::concurrency::channel_trace::<Chunk>(old(input_state).id()).len(),
        crate::proof::pipeline::forwarded(old(input_state).id(), old(output_state).id(), final(output_state).index(), settings),
        crate::trusted::concurrency::receiver_retained(sender) ==>
            final(input_state).index() == final(output_state).index()
                && final(input_state).index() == crate::trusted::concurrency::channel_trace::<Chunk>(old(input_state).id()).len(),
    no_unwind
))]
fn sorter(receiver: &Receiver<Chunk>, sender: &SyncSender<Chunk>, settings: &GlobalSettings) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input_id = input_state.id();
        let ghost output_id = output_state.id();
        let ghost input_rule = input_state.rule();
        let ghost output_rule = output_state.rule();
        let ghost limit = input_state.limit();
        let ghost input_dependency = input_state.dependency();
        let ghost output_dependency = output_state.dependency();
        let ghost input_template = input_state.template();
        let ghost output_template = output_state.template();
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant crate::proof::native_settings_valid(settings),
            crate::trusted::unwind::rayon_ready(),
            input_id == old(input_state).id(), output_id == old(output_state).id(),
            input_rule == old(input_state).rule(), output_rule == old(output_state).rule(),
            limit == old(input_state).limit(), limit == old(output_state).limit(),
            old(input_state).index() == 0, old(output_state).index() == 0,
            !old(output_state).own_closed(),
            input_dependency == old(input_state).dependency(), output_dependency == old(output_state).dependency(),
            input_template == old(input_state).template(), output_template == old(output_state).template(),
            crate::trusted::concurrency::receiver_id(receiver) == input_id,
            crate::trusted::concurrency::sender_id(sender) == output_id,
            input_state.id() == input_id, output_state.id() == output_id,
            input_state.rule() == input_rule, output_state.rule() == output_rule,
            input_state.limit() == limit, output_state.limit() == limit,
            input_state.dependency() == input_dependency, output_state.dependency() == output_dependency,
            input_state.template() == input_template, output_state.template() == output_template,
            input_state.index() == output_state.index() <= limit,
            !output_state.peer_closed(),
            !output_state.own_closed(),
            forall|i: nat, chunk: Chunk| #[trigger] input_rule(i, chunk)
                ==> crate::proof::pipeline::input_message(chunk, settings),
            forall|i: nat, chunk: Chunk| i < crate::trusted::concurrency::channel_trace::<Chunk>(input_id).len()
                && crate::proof::pipeline::sorted_message(
                    crate::trusted::concurrency::channel_trace::<Chunk>(input_id)[i as int], chunk, settings)
                ==> #[trigger] output_rule(i, chunk),
            crate::proof::pipeline::forwarded(input_id, output_id, output_state.index(), settings),
        invariant_except_break !input_state.peer_closed(),
        ensures input_state.index() == output_state.index(),
            input_state.index() == crate::trusted::concurrency::channel_trace::<Chunk>(input_id).len(),
            input_state.peer_closed(),
        decreases limit - input_state.index(),
    ))]
    while let Ok(mut payload) = {
        #[cfg(not(verus_keep_ghost))]
        { receiver.recv() }
        #[cfg(verus_keep_ghost)]
        { crate::trusted::concurrency::recv(receiver, verus_exec_expr! { Tracked(&mut *input_state) }) }
    } {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = payload; let ghost position = output_state.index(); }
        sort_payload(&mut payload, settings);
        #[cfg(verus_keep_ghost)]
        proof! { assert(output_rule(position, payload)); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost after = payload; }
        #[cfg(not(verus_keep_ghost))]
        let sent = sender.send(payload);
        #[cfg(verus_keep_ghost)]
        let sent = crate::trusted::concurrency::send(sender, payload, verus_exec_expr! { Tracked(&mut *output_state) });
        if matches!(sent, Err(_)) {
            // The receiver has gone away, likely because the other thread hit an error.
            // We stop silently because the actual error is printed by the other thread.
            return;
        }
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::pipeline::forwarded_step(input_id, output_id, position, before, after, settings); }
    }
}

#[cfg(verus_keep_ghost)]
#[verus_verify]
struct SortContents<'s> { settings: &'s GlobalSettings }

#[cfg(verus_keep_ghost)]
verus! {
    impl<'s> crate::proof::unwind::ContentsMutator for SortContents<'s> {
        type Output = ();

        #[verifier::prophetic]
        closed spec fn valid(&self, _owner: &Vec<u8>, contents: &crate::chunks::ChunkContents) -> bool {
            crate::proof::native_settings_valid(self.settings) && crate::trusted::unwind::rayon_ready()
                && crate::proof::pipeline::valid_contents(contents, self.settings)
        }
        #[verifier::prophetic]
        closed spec fn post(&self, _owner: &Vec<u8>, before: &crate::chunks::ChunkContents,
            after: &crate::chunks::ChunkContents, _result: &()) -> bool
        {
            after.line_data == before.line_data
                && after.lines@.to_multiset() == before.lines@.to_multiset()
                && crate::proof::sorting::sorting_result(
                    crate::proof::sorting::native_owned(before.lines@),
                    crate::proof::sorting::native_owned(after.lines@),
                    self.settings.stable || self.settings.unique,
                    crate::proof::sorting::native_compare(self.settings))
        }
        fn run<'a>(&self, _owner: &'a Vec<u8>, contents: &mut crate::chunks::ChunkContents<'a>) {
            proof! {
                reveal(<SortContents as crate::proof::unwind::ContentsMutator>::valid);
                reveal(<SortContents as crate::proof::unwind::ContentsMutator>::post);
            }
            sort_by(&mut contents.lines, self.settings, &contents.line_data);
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires crate::proof::native_settings_valid(settings), crate::trusted::unwind::rayon_ready(),
        crate::proof::pipeline::input_message(*old(payload), settings),
    ensures crate::proof::pipeline::sorted_message(*old(payload), *final(payload), settings),
    no_unwind
))]
fn sort_payload(payload: &mut Chunk, settings: &GlobalSettings) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = *payload; }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(<SortContents as crate::proof::unwind::ContentsMutator>::valid);
        reveal(<SortContents as crate::proof::unwind::ContentsMutator>::post);
        crate::proof::pipeline::input_facts(before, settings);
    }
    #[cfg(not(verus_keep_ghost))]
    payload.with_dependent_mut(|_, contents| {
        sort_by(&mut contents.lines, settings, &contents.line_data);
    });
    #[cfg(verus_keep_ghost)]
    crate::trusted::unwind::with_dependent_mut(payload, &SortContents { settings });
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::pipeline::establish_sorted(before, *payload, settings); }
}

/// Describes how we read the chunks from the input.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(crate) enum ReadResult<I: WriteableTmpFile> {
    /// The input was empty. Nothing was read.
    EmptyInput,
    /// The input fits into a single Chunk, which was kept in memory.
    SortedSingleChunk(Chunk),
    /// The input fits into two chunks, which were kept in memory.
    SortedTwoChunks([Chunk; 2]),
    /// The input was read into multiple chunks, which were written to auxiliary files.
    WroteChunksToFile { tmp_files: Vec<I::Closed> },
}
/// The function that is executed on the reader/writer thread.
#[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(result =>
    with Ghost(bytes): Ghost<Seq<u8>>,
        Tracked(sending): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>,
        Tracked(receiving): Tracked<&mut crate::trusted::concurrency::RecvState<Chunk>>,
    requires crate::proof::native_settings_valid(settings), I::supported(),
        separator == crate::proof::native_ending(settings),
        crate::proof::producer::ready(&sender, receiver, old(sending), old(receiving), settings, bytes.len()),
        vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(&files),
        vstd::std_specs::iter::IteratorSpec::will_return_none(&files),
        vstd::std_specs::iter::IteratorSpec::decrease(&files) is Some,
        vstd::std_specs::iter::IteratorSpec::remaining(&files).len() > 0,
        crate::proof::input::valid_files(vstd::std_specs::iter::IteratorSpec::remaining(&files)),
        bytes == crate::proof::input::file_bytes(vstd::std_specs::iter::IteratorSpec::remaining(&files), separator),
    ensures result is Ok, crate::proof::producer::valid_result(&result->Ok_0, settings),
        crate::proof::sorting::canonical_lines(
            crate::proof::producer::result_batches(&result->Ok_0, separator).flatten(), crate::proof::sorting::native_compare(settings))
            == crate::proof::sorting::canonical_lines(crate::proof::sorting::rows_of(bytes, separator),
                crate::proof::sorting::native_compare(settings)),
))]
fn read_write_loop<I: WriteableTmpFile>(
    mut files: impl Iterator<Item = UResult<crate::InputReader>>,
    tmp_dir: &mut TmpDirWrapper,
    separator: u8,
    buffer_size: usize,
    settings: &GlobalSettings,
    receiver: &SortReceiver,
    sender: SortSender<'_>,
) -> UResult<ReadResult<I>> {
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let consumer = receiver;
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    let receiver = consumer.receiver();
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof_decl! {
        let ghost input_id = sending.id(); let ghost output_id = receiving.id();
        let ghost limit = bytes.len();
    }
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! {
        crate::proof::native_settings_facts(settings);
        crate::proof::producer::payload_facts(input_id, output_id, settings);
        assert(crate::proof::input::allows_parsed(sending.rule(), separator, settings));
    }
    let mut file = files.next().unwrap()?;

    let mut carry_over = vec![];
    // kick things off with two reads
    #[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(state =>
        invariant crate::proof::native_settings_valid(settings), I::supported(),
            separator == crate::proof::native_ending(settings),
            crate::proof::producer::channels(consumer, sending, receiving, settings, limit),
            crate::trusted::concurrency::receiver_id(receiver) == output_id,
            sending.id() == input_id, receiving.id() == output_id,
            sender.input_id() == input_id, !sending.own_closed(),
            receiving.index() == 0, sending.index() == state.index(),
            crate::trusted_common::io::readable(&file), files.obeys_prophetic_iter_laws(),
            files.will_return_none(), files.decrease() is Some,
            crate::proof::input::valid_files(files.remaining()),
            sending.index() + crate::proof::input::pending(carry_over@, &file, files.remaining(), separator).len() <= limit,
            crate::proof::producer::sent_rows(input_id, sending.index())
                + crate::proof::sorting::rows_of(crate::proof::input::pending(carry_over@, &file, files.remaining(), separator), separator)
                    == crate::proof::sorting::rows_of(bytes, separator),
    ))]
    for _ in 0..2 {
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_decl! {
            let ghost expected = crate::proof::input::pending(carry_over@, &file, files.remaining(), separator);
            let ghost previous = sending.index();
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            crate::proof::native_settings_facts(settings);
            crate::proof::producer::payload_facts(input_id, output_id, settings);
            assert(crate::proof::input::allows_parsed(sending.rule(), separator, settings));
            crate::proof::input::parsed_allows_read(sending.rule(), sending.index(), expected, separator, settings);
        }
        #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
        let raw_sender = &sender;
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        let raw_sender = sender.sender();
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Tracked(&mut *sending) }
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
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            crate::proof::producer::read_progress(expected, carry_over@, &file,
                files.remaining(), separator, settings, input_id, previous, sending.index(), should_continue);
        }

        if !should_continue {
            #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
            drop(sender);
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            verus_exec_expr! { sender.close(Tracked(&mut *sending)) };
            // We have already read the whole input. Since we are in our first two reads,
            // this means that we can fit the whole input into memory. Bypass writing below and
            // handle this case in a more straightforward way.
            #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
            return Ok(if let Ok(first_chunk) = receiver.recv() {
                if let Ok(second_chunk) = receiver.recv() {
                    ReadResult::SortedTwoChunks([first_chunk, second_chunk])
                } else {
                    ReadResult::SortedSingleChunk(first_chunk)
                }
            } else {
                ReadResult::EmptyInput
            });
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            {
                let first = verus_exec_expr! { crate::trusted::concurrency::recv(receiver, Tracked(&mut *receiving)) };
                let result: ReadResult<I> = if let Ok(first_chunk) = first {
                    proof! {
                        crate::proof::producer::sorted_chunk(
                            crate::trusted::concurrency::channel_trace::<Chunk>(input_id)[0], first_chunk, settings);
                    }
                    let second = verus_exec_expr! { crate::trusted::concurrency::recv(receiver, Tracked(&mut *receiving)) };
                    if let Ok(second_chunk) = second {
                        proof! {
                            crate::proof::producer::sorted_chunk(
                                crate::trusted::concurrency::channel_trace::<Chunk>(input_id)[1], second_chunk, settings);
                        }
                        ReadResult::SortedTwoChunks([first_chunk, second_chunk])
                    } else {
                        verus_exec_expr! { pipe_complete(consumer, Tracked(&*receiving)) };
                        ReadResult::SortedSingleChunk(first_chunk)
                    }
                } else {
                    verus_exec_expr! { pipe_complete(consumer, Tracked(&*receiving)) };
                    ReadResult::EmptyInput
                };
                proof! {
                    assert(receiving.index() == sending.index());
                    assert(crate::proof::producer::result_batches(&result, separator)
                        =~= crate::proof::producer::batches(crate::trusted::concurrency::channel_trace::<Chunk>(output_id)
                            .take(receiving.index() as int)));
                    crate::proof::producer::finish_result(&result, bytes, input_id, output_id, receiving.index(), settings);
                }
                return Ok(result);
            }
        }
    }

    let mut sender_option = Some(sender);
    let mut tmp_files = vec![];
    #[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(
        invariant crate::proof::native_settings_valid(settings), I::supported(),
            separator == crate::proof::native_ending(settings), settings.compress_prog is None,
            crate::proof::producer::channels(consumer, sending, receiving, settings, limit),
            crate::trusted::concurrency::receiver_id(receiver) == output_id,
            sending.id() == input_id, receiving.id() == output_id,
            crate::trusted_common::io::readable(&file), files.obeys_prophetic_iter_laws(),
            files.will_return_none(), files.decrease() is Some,
            crate::proof::input::valid_files(files.remaining()),
            tmp_files.len() == receiving.index(),
            tmp_files@.map_values(|file: I::Closed| crate::proof::sorting::rows_of(file.bytes(), separator))
                == crate::proof::producer::batches(crate::trusted::concurrency::channel_trace::<Chunk>(output_id)
                    .take(receiving.index() as int)),
            forall|i: int| 0 <= i < tmp_files.len() ==> tmp_files@[i].valid()
                && vstd::relations::sorted_by(crate::proof::sorting::rows_of(tmp_files@[i].bytes(), separator),
                    |a: Seq<u8>, b: Seq<u8>| crate::proof::sorting::native_compare(settings)(a, b) != Ordering::Greater),
            match &sender_option {
                Some(producer) => producer.input_id() == input_id && producer.output_id() == output_id
                    && !sending.own_closed()
                    && sending.index() + crate::proof::input::pending(carry_over@, &file, files.remaining(), separator).len() <= limit
                    && crate::proof::producer::sent_rows(input_id, sending.index())
                        + crate::proof::sorting::rows_of(crate::proof::input::pending(carry_over@, &file, files.remaining(), separator), separator)
                            == crate::proof::sorting::rows_of(bytes, separator),
                None => sending.own_closed()
                    && crate::trusted::concurrency::channel_trace::<Chunk>(input_id).len() == sending.index()
                    && crate::proof::producer::sent_rows(input_id, sending.index()) == crate::proof::sorting::rows_of(bytes, separator),
            },
        decreases limit - receiving.index(),
    ))]
    loop {
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_decl! { let ghost previous_received = receiving.index(); }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! { crate::proof::producer::payload_facts(input_id, output_id, settings); }
        let message = {
            #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
            { receiver.recv() }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            { verus_exec_expr! { crate::trusted::concurrency::recv(receiver, Tracked(&mut *receiving)) } }
        };
        let Ok(chunk) = message else {
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            if let Some(producer) = &sender_option {
                verus_exec_expr! { producer.reject_eof(Tracked(&*receiving)) };
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            verus_exec_expr! { pipe_complete(consumer, Tracked(&*receiving)) };
            #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
            return Ok(ReadResult::WroteChunksToFile { tmp_files });
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            {
                let result = ReadResult::<I>::WroteChunksToFile { tmp_files };
                proof! {
                    crate::proof::producer::finish_result(&result, bytes, input_id, output_id, receiving.index(), settings);
                }
                return Ok(result);
            }
        };

        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            crate::proof::producer::sorted_chunk(
                crate::trusted::concurrency::channel_trace::<Chunk>(input_id)[previous_received as int], chunk, settings);
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        let (new_file, file_log) = crate::trusted::temporary::new_file(tmp_dir);
        #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
        let new_file = tmp_dir.next_file();
        #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
        let compress_prog = settings.compress_prog.as_deref();
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        let compress_prog = crate::trusted::temporary::optional_str(&settings.compress_prog);
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Tracked(file_log.get()) }
        let tmp_file = write::<I>(
            &chunk,
            new_file?,
            compress_prog,
            separator,
        )?;
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            crate::proof::producer::emit_roundtrip(crate::proof::producer::rows(&chunk), separator);
            assert(crate::proof::sorting::rows_of(tmp_file.bytes(), separator) == crate::proof::producer::rows(&chunk));
            crate::proof::producer::batches_push(
                crate::trusted::concurrency::channel_trace::<Chunk>(output_id).take(previous_received as int), chunk);
            assert(crate::trusted::concurrency::channel_trace::<Chunk>(output_id).take(receiving.index() as int)
                =~= crate::trusted::concurrency::channel_trace::<Chunk>(output_id).take(previous_received as int).push(chunk));
        }
        tmp_files.push(tmp_file);

        let recycled_chunk = chunk.recycle();

        if let Some(sender) = &sender_option {
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            let sender = sender.sender();
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_decl! {
                let ghost expected = crate::proof::input::pending(carry_over@, &file, files.remaining(), separator);
                let ghost previous = sending.index();
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                crate::proof::native_settings_facts(settings);
                assert(crate::proof::input::allows_parsed(sending.rule(), separator, settings));
                crate::proof::input::parsed_allows_read(sending.rule(), sending.index(), expected, separator, settings);
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Tracked(&mut *sending) }
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
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                crate::proof::producer::read_progress(expected, carry_over@, &file,
                    files.remaining(), separator, settings, input_id, previous, sending.index(), should_continue);
            }
            if !should_continue {
                #[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
                { sender_option = None; }
                #[cfg(all(verus_keep_ghost, uutils_sort_full))]
                {
                    let producer = sender_option.take().unwrap();
                    verus_exec_expr! { producer.close(Tracked(&mut *sending)) };
                }
            }
        }
    }
}

/// Write the lines in `chunk` to `file`, separated by `separator`.
/// `compress_prog` is used to optionally compress file contents.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(log): Tracked<crate::proof::OutputLog>,
    requires I::supported(), compress_prog is None,
        crate::trusted::temporary::file_session(&file.0) == log.session(),
        crate::trusted::temporary::path_session(&file.1) == log.session(), log.bytes().len() == 0,
    ensures result is Ok, result->Ok_0.valid(), result->Ok_0.bytes()
        == crate::proof::sorting::emit(crate::proof::sorting::native_owned(
            crate::trusted::ownership::contents(chunk).lines@), separator),
))]
fn write<I: WriteableTmpFile>(
    chunk: &Chunk,
    file: (File, TmpPath),
    compress_prog: Option<&str>,
    separator: u8,
) -> UResult<I::Closed> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let tracked mut log = log; }
    #[cfg(not(verus_keep_ghost))]
    let mut tmp_file = I::create(file, compress_prog)?;
    #[cfg(verus_keep_ghost)]
    let mut tmp_file = verus_exec_expr! { I::create(file, compress_prog, Tracked(&log))? };
    #[cfg(verus_keep_ghost)]
    proof_with! { Tracked(&mut log) }
    write_lines(chunk.lines(), tmp_file.as_write(), separator)?;
    #[cfg(not(verus_keep_ghost))]
    { tmp_file.finished_writing() }
    #[cfg(verus_keep_ghost)]
    { verus_exec_expr! { tmp_file.finished_writing(Tracked(log)) } }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires crate::trusted::writer_session(old(writer)) == old(log).session(),
    ensures result is Ok, final(log).session() == old(log).session(),
        crate::trusted::writer_session(final(writer)) == final(log).session(),
        final(log).bytes() == old(log).bytes() + crate::proof::sorting::emit(
            crate::proof::sorting::native_owned(lines@), separator),
))]
fn write_lines<T: Write>(lines: &[Line], writer: &mut T, separator: u8) -> std::io::Result<()> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = log.bytes(); let ghost session = log.session(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(state =>
        invariant state.seq().unref() == lines@, log.session() == session,
            crate::trusted::writer_session(&*writer) == log.session(),
            log.bytes() == initial + crate::proof::sorting::emit(
                crate::proof::sorting::native_owned(lines@.take(state.index())), separator),
    ))]
    for s in lines {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::sorting::native_line_value(s);
            let prefix = crate::proof::sorting::native_owned(lines@.take(state.index()));
            assert(crate::proof::sorting::native_owned(lines@.take(state.index() + 1))
                =~= prefix.push(s.line@));
            crate::proof::sorting::emit_push(prefix, separator, s.line@);
        }
        #[cfg(not(verus_keep_ghost))]
        writer.write_all(s.line)?;
        #[cfg(verus_keep_ghost)]
        proof_with! { Tracked(&mut *log) }
        #[cfg(verus_keep_ghost)]
        crate::trusted::write_output(writer, s.line)?;
        #[cfg(not(verus_keep_ghost))]
        writer.write_all(&[separator])?;
        #[cfg(verus_keep_ghost)]
        proof_with! { Tracked(&mut *log) }
        #[cfg(verus_keep_ghost)]
        crate::trusted::write_output(writer, &[separator])?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(lines@.take(lines@.len() as int) =~= lines@); }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io;

    use super::*;

    struct FailingWriter(io::ErrorKind);

    impl Write for FailingWriter {
        fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
            Err(io::Error::from(self.0))
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn write_lines_propagates_write_errors() {
        let lines = [Line {
            line: b"line",
            index: 0,
        }];

        let result = write_lines(
            &lines,
            &mut FailingWriter(io::ErrorKind::StorageFull),
            b'\n',
        );

        assert_eq!(result.unwrap_err().kind(), io::ErrorKind::StorageFull);
    }
}
