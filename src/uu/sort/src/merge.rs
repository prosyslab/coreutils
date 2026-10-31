// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

//! Merge already sorted files.
//!
//! We achieve performance by splitting the tasks of sorting and writing, and reading and parsing between two threads.
//! The threads communicate over channels. There's one channel per file in the direction reader -> sorter, but only
//! one channel from the sorter back to the reader. The channels to the sorter are used to send the read chunks.
//! The sorter reads the next chunk from the channel whenever it needs the next chunk after running out of lines
//! from the previous read of the file. The channel back from the sorter to the reader has two purposes: To allow the reader
//! to reuse memory allocations and to tell the reader which file to read from next.

use std::{
    cmp::Ordering,
    collections::BinaryHeap,
    ffi::{OsStr, OsString},
    fs::File,
    io::{self, BufWriter, Read, Write},
    iter,
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    rc::Rc,
    sync::mpsc::{Receiver, Sender, SyncSender, TryRecvError, channel, sync_channel},
    thread::{self, JoinHandle},
};

use uucore::error::FromIo;
use crate::SortResult as UResult;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
#[cfg(verus_keep_ghost)]
use crate::proof::temporary::{WriterModel, ClosedModel, InputModel};
#[cfg(not(verus_keep_ghost))]
pub trait WriterModel {}
#[cfg(not(verus_keep_ghost))]
impl<T> WriterModel for T {}
#[cfg(not(verus_keep_ghost))]
pub trait ClosedModel {}
#[cfg(not(verus_keep_ghost))]
impl<T> ClosedModel for T {}
#[cfg(not(verus_keep_ghost))]
pub trait InputModel {}
#[cfg(not(verus_keep_ghost))]
impl<T> InputModel for T {}

use crate::{
    GlobalSettings, Output, SortError,
    chunks::{self, Chunk, RecycledChunk},
    current_open_fd_count, fd_soft_limit, merge_compare, open,
    tmp_dir::{TmpDirWrapper, TmpPath},
};

/// If the output file occurs in the input files as well, copy the contents of the output file
/// and replace its occurrences in the inputs with that copy, which is returned.
fn replace_output_file_in_input_files(
    files: &mut [OsString],
    output: Option<&OsStr>,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<Option<TmpPath>> {
    let mut copy: Option<TmpPath> = None;
    if let Some(Ok(output_path)) = output.map(|path| Path::new(path).canonicalize()) {
        for file in files {
            if Path::new(file)
                .canonicalize()
                .is_ok_and(|file_path| file_path == output_path)
            {
                if let Some(copy) = &copy {
                    *file = copy.path().into();
                } else {
                    // Write through the descriptor `next_file` just opened rather
                    // than `fs::copy`, which would put the source's permission bits
                    // on the temporary file and undo the 0600 it was created with.
                    let (mut copy_file, copy_path) = tmp_dir.next_file()?;
                    let mut source = File::open(&output_path)
                        .map_err(|error| SortError::OpenTmpFileFailed { error })?;
                    io::copy(&mut source, &mut copy_file)
                        .map_err(|error| SortError::OpenTmpFileFailed { error })?;
                    *file = copy_path.path().into();
                    copy = Some(copy_path);
                }
            }
        }
    }
    Ok(copy)
}

/// Open the merge input `file`. `copy` is the copy of the output file returned by
/// [`replace_output_file_in_input_files`].
fn open_input(file: &OsStr, copy: Option<&TmpPath>) -> UResult<crate::InputReader> {
    match copy {
        Some(copy) if Path::new(file) == copy.path() => Ok(crate::boxed_reader(
            copy.open()
                .map_err(|error| SortError::OpenTmpFileFailed { error })?,
        )),
        _ => open(file).map_err(Into::into),
    }
}

/// Determine the effective merge batch size, enforcing a minimum and respecting the
/// file-descriptor soft limit after reserving stdio/output and a safety margin.
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result >= 2,))]
fn effective_merge_batch_size(settings: &GlobalSettings) -> usize {
    const MIN_BATCH_SIZE: usize = 2;
    const RESERVED_TMP_OUTPUT: usize = 1;
    const RESERVED_CTRL_C: usize = 2;
    const RESERVED_RANDOM_SOURCE: usize = 1;
    const SAFETY_MARGIN: usize = 1;
    let mut batch_size = settings.merge_batch_size.max(MIN_BATCH_SIZE);

    if let Some(limit) = fd_soft_limit() {
        let open_fds = current_open_fd_count().unwrap_or(3);
        let mut reserved = RESERVED_TMP_OUTPUT + RESERVED_CTRL_C + SAFETY_MARGIN;
        if settings.salt.is_some() {
            reserved = reserved.saturating_add(RESERVED_RANDOM_SOURCE);
        }
        let available_inputs = limit.saturating_sub(open_fds.saturating_add(reserved));
        if available_inputs >= MIN_BATCH_SIZE {
            batch_size = batch_size.min(available_inputs);
        } else {
            batch_size = MIN_BATCH_SIZE;
        }
    }

    batch_size
}

/// Merge pre-sorted `Box<dyn Read>`s.
///
/// If `settings.merge_batch_size` is greater than the length of `files`, intermediate files will be used.
/// If `settings.compress_prog` is `Some`, intermediate files will be compressed with it.
pub fn merge(
    files: &mut [OsString],
    settings: &GlobalSettings,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    let copy = replace_output_file_in_input_files(files, output.as_output_name(), tmp_dir)?;
    let files = files
        .iter()
        .map(|file| open_input(file, copy.as_ref()).map(|inner| PlainMergeInput { inner }));
    if settings.compress_prog.is_none() {
        merge_with_file_limit::<_, _, WriteablePlainTmpFile>(files, settings, output, tmp_dir)
    } else {
        merge_with_file_limit::<_, _, WriteableCompressedTmpFile>(files, settings, output, tmp_dir)
    }
}

// Consume one bounded batch before initializing its reader channels.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(files).obeys_prophetic_iter_laws(), old(files).will_return_none(),
    ensures IteratorSpec::obeys_prophetic_iter_laws(&*final(files)), IteratorSpec::will_return_none(&*final(files)),
        IteratorSpec::decrease(&*final(files)) is Some == (old(files).decrease() is Some),
        result@ == old(files).remaining().take(if count < old(files).remaining().len() { count as int }
            else { old(files).remaining().len() as int }),
        IteratorSpec::remaining(&*final(files)) == old(files).remaining().skip(result.len() as int),
))]
fn merge_batch<M, F: ExactSizeIterator<Item = UResult<M>>>(files: &mut F, count: usize) -> Vec<UResult<M>> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = files.remaining(); }
    let count = count.min(files.len());
    let mut batch = Vec::new();
    #[cfg_attr(verus_keep_ghost, verus_spec(state =>
        invariant files.obeys_prophetic_iter_laws(), files.will_return_none(),
            files.decrease() is Some == (old(files).decrease() is Some),
            state.seq().len() == count,
            count <= original.len(), batch@ == original.take(state.index()),
            files.remaining() == original.skip(state.index()),
    ))]
    for _ in 0..count {
        batch.push(files.next().unwrap());
    }
    batch
}

#[cfg(verus_keep_ghost)]
#[verus_spec(result =>
    requires forall|i: int| 0 <= i < files.len() ==> #[trigger] files@[i].valid(),
    ensures result.values().len() == files.len(),
        result.obeys_prophetic_iter_laws(), result.will_return_none(), result.decrease() is Some,
        result.remaining() == result.values(),
        forall|i: int| 0 <= i < files.len() ==> (#[trigger] result.values()[i] is Ok
            && result.values()[i]->Ok_0.valid()
            && result.values()[i]->Ok_0.bytes() == files@[i].bytes()),
)]
pub(crate) fn reopen_files<C: ClosedTmpFile + 'static>(files: Vec<C>)
    -> crate::trusted::exact_iteration::ExactIter<'static, UResult<C::Reopened>>
{
    crate::trusted::exact_iteration::map(crate::trusted::joining::into_vec_iter(files),
        crate::trusted_common::closure_with_spec!(
            (result => requires file.valid(),
                ensures result is Ok, result->Ok_0.valid(), result->Ok_0.bytes() == file.bytes(),
            ),
            |file: C| -> UResult<C::Reopened> { file.reopen() }
        ))
}

// Merge already sorted `MergeInput`s.
#[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_verify)]
#[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(result =>
    with Ghost(context): Ghost<crate::proof::merging::MergeContext>,
        Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires Tmp::supported(), files.obeys_prophetic_iter_laws(), files.will_return_none(), files.decrease() is Some,
        crate::proof::merging::inputs_valid(files.remaining(), settings),
        context.files == crate::proof::merging::input_rows(files.remaining(), settings),
        old(log).session() == crate::trusted::output_session(output),
    ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
        final(log).bytes() == crate::proof::merging::output(context.files, settings),
    decreases context.files.len(),
))]
pub(crate) fn merge_with_file_limit<
    M: MergeInput + 'static,
    F: ExactSizeIterator<Item = UResult<M>>,
    Tmp: WriteableTmpFile + 'static,
>(
    mut files: F,
    settings: &GlobalSettings,
    output: Output,
    tmp_dir: &mut TmpDirWrapper,
) -> UResult<()> {
    let batch_size = effective_merge_batch_size(settings);
    #[cfg(not(verus_keep_ghost))]
    debug_assert!(batch_size >= 2);
    #[cfg(all(verus_keep_ghost, uutils_sort_full))]
    proof! { assert(batch_size >= 2); crate::proof::native_settings_facts(settings); }

    if files.len() <= batch_size {
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Ghost(context) => Tracked(init) }
        let merger = merge_without_limit(files, settings);
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Tracked(&mut *log), Tracked(init) }
        merger?.write_all(settings, output)
    } else {
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_decl! {
            let ghost original = files.remaining();
            let ghost mut processed: nat = 0;
            let ghost mut groups: Seq<Seq<Seq<u8>>> = Seq::empty();
        }
        let mut temporary_files: Vec<Tmp::Closed> = vec![];
        #[cfg_attr(all(verus_keep_ghost, uutils_sort_full), verus_spec(
            invariant Tmp::supported(), crate::proof::merging::inputs_valid(original, settings),
                crate::proof::merging::context_valid(&context, settings),
                context.files == crate::proof::merging::input_rows(original, settings),
                files.obeys_prophetic_iter_laws(), files.will_return_none(), files.decrease() is Some,
                processed <= context.files.len(), files.remaining() == original.skip(processed as int),
                crate::proof::merging::inputs_valid(files.remaining(), settings),
                batch_size >= 2, batch_size < context.files.len(),
                groups.flatten() == context.files.take(processed as int).flatten(),
                groups.len() == temporary_files.len(),
                (groups.len() == 0) == (processed == 0), groups.len() > 0 ==> groups.len() < processed,
                forall|i: int| #![trigger temporary_files@[i]] 0 <= i < temporary_files.len() ==> {
                    let file = &temporary_files@[i];
                    let rows = crate::proof::composition::merged_rows(groups[i], settings.unique,
                        crate::proof::sorting::native_compare(settings));
                    &&& file.valid()
                    &&& file.bytes() == crate::proof::sorting::emit(rows, crate::proof::native_ending(settings))
                    &&& crate::proof::sorting::rows_of(file.bytes(), crate::proof::native_ending(settings)) == rows
                    &&& vstd::relations::sorted_by(rows, |a: Seq<u8>, b: Seq<u8>|
                        crate::proof::sorting::native_compare(settings)(a, b) != std::cmp::Ordering::Greater)
                },
            decreases context.files.len() - processed,
        ))]
        while files.len() > 0 {
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! { crate::proof::native_settings_facts(settings); }
            // Create the output before opening this batch's inputs, so that
            // creating it doesn't compete with them for file descriptors.
            #[cfg(not(verus_keep_ghost))]
            let mut tmp_file = Tmp::create(tmp_dir.next_file()?, settings.compress_prog.as_deref())?;
            #[cfg(verus_keep_ghost)]
            let (new_file, mut file_log) = crate::trusted::temporary::new_file(tmp_dir);
            #[cfg(verus_keep_ghost)]
            let mut tmp_file = verus_exec_expr! {
                Tmp::create(new_file?, crate::trusted::temporary::optional_str(&settings.compress_prog), Tracked(file_log.borrow()))?
            };
            let batch = merge_batch(&mut files, batch_size);
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_decl! {
                let ghost batch_context = crate::proof::merging::MergeContext {
                    files: context.files.subrange(processed as int, processed as int + batch.len()) };
                let ghost batch_rows = crate::proof::merging::source(&batch_context);
                let ghost merged = crate::proof::composition::merged_rows(batch_rows, settings.unique,
                    crate::proof::sorting::native_compare(settings));
                let ghost batch_len = batch.len();
            }
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                crate::proof::native_settings_facts(settings);
                crate::proof::merging::base_lawful(settings);
                crate::proof::merging::input_slice(original, settings, processed as int, processed as int + batch.len());
                crate::proof::merging::input_slice(original, settings, processed as int + batch.len(), original.len() as int);
                assert(batch@ =~= original.subrange(processed as int, processed as int + batch.len()));
                assert(files.remaining() =~= original.skip(processed as int + batch.len()));
                assert(files.remaining() =~= original.subrange(processed as int + batch.len(), original.len() as int));
                assert(crate::proof::merging::inputs_valid(files.remaining(), settings));
                crate::proof::merging::inputs_clean(batch@, settings);
                crate::proof::composition::merged_facts(batch_rows, settings.unique,
                    crate::proof::sorting::native_compare(settings), crate::proof::native_ending(settings));
            }
            #[cfg(not(verus_keep_ghost))]
            let batch = batch.into_iter();
            #[cfg(verus_keep_ghost)]
            let batch = crate::trusted::joining::into_vec_iter(batch);
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Ghost(batch_context) => Tracked(init) }
            let merger = merge_without_limit(batch, settings)?;
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof_with! { Tracked(file_log.borrow_mut()), Tracked(init) }
            merger.write_all_to(settings, tmp_file.as_write(), || "write failed".into())?;
            #[cfg(not(verus_keep_ghost))]
            temporary_files.push(tmp_file.finished_writing()?);
            #[cfg(verus_keep_ghost)]
            temporary_files.push(tmp_file.finished_writing(file_log)?);
            #[cfg(all(verus_keep_ghost, uutils_sort_full))]
            proof! {
                assert(context.files.take(processed as int + batch_len) =~=
                    context.files.take(processed as int) + batch_context.files);
                assert((context.files.take(processed as int) + batch_context.files).flatten()
                    == context.files.take(processed as int).flatten() + batch_rows) by {
                    vstd::seq_lib::lemma_flatten_concat(context.files.take(processed as int), batch_context.files);
                };
                vstd::seq_lib::lemma_flatten_concat(groups, seq![batch_rows]);
                reveal_with_fuel(Seq::flatten, 2);
                assert(groups.push(batch_rows) =~= groups + seq![batch_rows]);
                assert(groups.push(batch_rows).flatten() == groups.flatten() + batch_rows);
                groups = groups.push(batch_rows);
                processed = (processed + batch_len) as nat;
            }
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_decl! {
            let ghost next_context = crate::proof::merging::MergeContext { files: temporary_files@
                .map_values(|file: Tmp::Closed| crate::proof::sorting::rows_of(file.bytes(), crate::proof::native_ending(settings))) };
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            crate::proof::merging::base_lawful(settings);
            assert(processed == context.files.len());
            assert(context.files.take(processed as int) =~= context.files);
            assert(groups.flatten() == context.files.flatten());
            assert(next_context.files =~= crate::proof::composition::merged_chunks(groups, settings.unique,
                crate::proof::sorting::native_compare(settings)));
            crate::proof::composition::merge_pass(groups, settings.unique, crate::proof::sorting::native_compare(settings));
            assert(crate::proof::merging::output(next_context.files, settings) == crate::proof::sorting::emit(
                crate::proof::composition::merged_rows(next_context.files.flatten(), settings.unique,
                    crate::proof::sorting::native_compare(settings)), crate::proof::native_ending(settings)));
            assert(crate::proof::merging::output(next_context.files, settings) == crate::proof::merging::output(context.files, settings));
        }
        #[cfg(verus_keep_ghost)]
        let files = reopen_files(temporary_files);
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof! {
            assert(crate::proof::merging::input_rows(files.remaining(), settings) =~= next_context.files);
            assert(crate::proof::merging::inputs_valid(files.remaining(), settings));
        }
        #[cfg(all(verus_keep_ghost, uutils_sort_full))]
        proof_with! { Ghost(next_context), Tracked(&mut *log) }
        merge_with_file_limit::<_, _, Tmp>(
            #[cfg(not(verus_keep_ghost))]
            temporary_files.into_iter().map(Box::new(|c: Tmp::Closed| c.reopen())
                as Box<dyn FnMut(Tmp::Closed) -> UResult<<Tmp::Closed as ClosedTmpFile>::Reopened>>),
            #[cfg(verus_keep_ghost)]
            files,
            settings,
            output,
            tmp_dir,
        )
    }
}

/// Merge files without limiting how many files are concurrently open.
///
/// It is the responsibility of the caller to ensure that `files` yields only
/// as many files as we are allowed to open concurrently.
#[cfg(not(all(verus_keep_ghost, uutils_sort_full)))]
fn merge_without_limit<M: MergeInput + 'static, F: Iterator<Item = UResult<M>>>(
    files: F,
    settings: &GlobalSettings,
) -> UResult<FileMerger<'_>> {
    let (request_sender, request_receiver) = channel();
    let mut reader_files = Vec::with_capacity(files.size_hint().0);
    let mut loaded_receivers = Vec::with_capacity(files.size_hint().0);
    for (file_number, file) in files.enumerate() {
        let (sender, receiver) = sync_channel(2);
        loaded_receivers.push(receiver);
        reader_files.push(Some(ReaderFile {
            file: file?,
            sender,
            carry_over: vec![],
        }));
        // Send the initial chunk to trigger a read for each file
        request_sender
            .send((file_number, RecycledChunk::new(8 * 1024)))
            .unwrap();
    }

    // Send the second chunk for each file
    for file_number in 0..reader_files.len() {
        request_sender
            .send((file_number, RecycledChunk::new(8 * 1024)))
            .unwrap();
    }

    let reader_join_handle = thread::spawn({
        // The merge comparator (`merge_compare`) compares whole-line locale keys lazily
        // with the ICU collator, so the reader does not need to precompute per-line sort
        // keys. Disabling `fast_locale_collation` here turns `Line::create` into a no-op
        // for that (whole-line, default) mode and avoids the dominant cost of merging
        // already-sorted input. Other modes are unaffected (the flag is already false).
        let mut settings = settings.clone();
        settings.precomputed.fast_locale_collation = false;
        move || {
            reader(
                &request_receiver,
                &mut reader_files,
                &settings,
                settings.line_ending.into(),
            )
        }
    });

    let mut mergeable_files = vec![];

    for (file_number, receiver) in loaded_receivers.into_iter().enumerate() {
        if let Ok(chunk) = receiver.recv() {
            mergeable_files.push(MergeableFile {
                current_chunk: Rc::new(chunk),
                file_number,
                line_idx: 0,
                receiver,
                settings,
            });
        }
    }

    Ok(FileMerger {
        heap: BinaryHeap::from(mergeable_files),
        request_sender,
        prev: None,
        reader_join_handle,
    })
}

#[cfg(all(verus_keep_ghost, uutils_sort_full))]
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
#[verus_spec(result =>
    with Ghost(context): Ghost<crate::proof::merging::MergeContext>
        -> init: Tracked<crate::proof::merging::StreamInit>,
    requires files.obeys_prophetic_iter_laws(), files.will_return_none(), files.decrease() is Some,
        crate::proof::merging::inputs_valid(files.remaining(), settings),
        context.files == crate::proof::merging::input_rows(files.remaining(), settings),
    ensures result is Ok, init@.context == context,
        crate::proof::merging::stream_ready(&result->Ok_0, &init@, settings),
)]
fn merge_without_limit<M: MergeInput + 'static, F: Iterator<Item = UResult<M>>>(
    files: F, settings: &GlobalSettings,
) -> UResult<FileMerger<'_>> {
    let (request_sender, request_receiver, request_sending, request_receiving) = verus_exec_expr! {
        crate::trusted::concurrency::unbounded_channel(Ghost(0),
            Ghost(crate::proof::merging::request_template(context.files.len())),
            Ghost(2 * context.files.len() + crate::proof::merging::source(&context).len()))
    };
    proof_decl! {
        let tracked mut requests = request_sending.get();
        let tracked mut senders: Map<usize, crate::trusted::concurrency::SendState<Chunk>> = Map::tracked_empty();
        let tracked mut receivers: Map<usize, crate::trusted::concurrency::RecvState<Chunk>> = Map::tracked_empty();
        let ghost request_id = requests.id();
    }
    proof! { crate::proof::native_settings_facts(settings); }
    let separator = settings.line_ending.into();
    let mut reader_files = Vec::new();
    let mut loaded_receivers = Vec::new();
    proof! {
        assert(context.files.take(0) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(Seq::new(0, |i: int| i as usize).to_set() =~= Set::<usize>::empty());
        assert(crate::proof::joining::files_progress(reader_files@, &senders, context.files.take(0), settings, separator));
        assert(crate::proof::merging::startup_receivers(loaded_receivers@, &receivers, context.files.take(0), settings));
    }
    #[verus_spec(state =>
        invariant crate::proof::native_settings_valid(settings),
            state.iter.obeys_prophetic_iter_laws(), state.iter.will_return_none(), state.iter.decrease() is Some,
            state.seq().len() == context.files.len(),
            context.files == crate::proof::merging::input_rows(state.seq(), settings),
            crate::proof::merging::inputs_valid(state.seq(), settings),
            reader_files.len() == state.index(), loaded_receivers.len() == state.index(),
            crate::proof::joining::files_progress(reader_files@, &senders, context.files.take(state.index()), settings, separator),
            crate::proof::merging::startup_receivers(loaded_receivers@, &receivers, context.files.take(state.index()), settings),
            forall|i: usize| i < reader_files.len() ==> #[trigger] senders[i].id() == receivers[i].id(),
            separator == crate::proof::native_ending(settings),
            requests.id() == request_id, requests.index() == state.index(),
            crate::trusted::concurrency::sender_id_unbounded(&request_sender) == requests.id(),
            requests.template() == crate::proof::merging::request_template(context.files.len()),
            requests.limit() == 2 * context.files.len() + crate::proof::merging::source(&context).len(),
    )]
    for file in files {
        let file_number = reader_files.len();
        let file = crate::trusted::unwind::unwrap_result(file);
        proof! {
            assert(context.files[file_number as int] == crate::proof::sorting::rows_of(file.bytes(), separator));
            crate::proof::input::terminated_length(file.bytes(), separator);
        }
        let (sender, receiver, sending, receiving) = verus_exec_expr! {
            crate::trusted::joining::chunk_channel(
                Ghost(crate::proof::joining::reader_template(context.files[file_number as int], settings)),
                Ghost(file.bytes().len() + 1))
        };
        proof_decl! {
            let ghost old_files = reader_files@;
            let ghost old_loaded = loaded_receivers@;
            let ghost old_senders = senders;
            let ghost old_receivers = receivers;
            let tracked sending = sending.get();
            let tracked receiving = receiving.get();
        }
        reader_files.push(Some(ReaderFile { file, sender, carry_over: Vec::new() }));
        loaded_receivers.push(receiver);
        proof! {
            broadcast use vstd::seq_lib::group_seq_properties;
            crate::proof::native_settings_facts(settings);
            assert(file_number < context.files.len());
            crate::proof::merging::index_extend(file_number as nat);
            crate::proof::input::rows_terminated(reader_files@[file_number as int]->Some_0.file.bytes(), separator);
            assert(crate::proof::joining::file_progress(reader_files@[file_number as int], &sending,
                context.files[file_number as int], settings, separator));
            senders.tracked_insert(file_number, sending);
            receivers.tracked_insert(file_number, receiving);
            assert(senders.dom() =~= Seq::new((file_number + 1) as nat, |i: int| i as usize).to_set());
            assert(receivers.dom() =~= senders.dom());
            assert forall|i: int| 0 <= i <= file_number implies #[trigger]
                crate::proof::joining::file_progress(reader_files@[i], &senders[i as usize], context.files[i], settings, separator) by {
                if i < file_number { crate::proof::joining::progress_index(old_files, &old_senders,
                    context.files.take(file_number as int), settings, separator, i as usize); }
            };
            assert(crate::proof::merging::startup_receivers(loaded_receivers@, &receivers,
                context.files.take(file_number as int + 1), settings));
        }
        let request = (file_number, RecycledChunk::new(8 * 1024));
        verus_exec_expr! {
            crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send_unbounded(
                &request_sender, request, Tracked(&mut requests)))
        };
    }
    #[verus_spec(state =>
        invariant requests.id() == request_id, requests.index() == context.files.len() + state.index(),
            crate::trusted::concurrency::sender_id_unbounded(&request_sender) == requests.id(),
            requests.template() == crate::proof::merging::request_template(context.files.len()),
            requests.limit() == 2 * context.files.len() + crate::proof::merging::source(&context).len(),
            reader_files.len() == context.files.len(), state.seq().len() == reader_files.len(),
    )]
    for file_number in 0..reader_files.len() {
        let request = (file_number, RecycledChunk::new(8 * 1024));
        verus_exec_expr! {
            crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send_unbounded(
                &request_sender, request, Tracked(&mut requests)))
        };
    }
    proof_decl! { let ghost ids = Seq::new(context.files.len(), |i: int| receivers[i as usize].id()); }
    let (reader_join_handle, completion, reader, lease) = verus_exec_expr! { {
        let mut task_settings = crate::trusted::concurrency::clone_settings(settings);
        proof! { crate::proof::native_settings_facts(settings); }
        task_settings.precomputed.fast_locale_collation = false;
        let task = SourceReaderTask { recycled_receiver: request_receiver, files: reader_files,
            settings: task_settings, separator, states: Tracked(senders), requests: request_receiving,
            source: Ghost(context.files) };
        proof! { assert(<SourceReaderTask<M> as crate::proof::joining::Task>::ready(&task)); }
        let ghost before = task;
        let result = crate::trusted::joining::launch_reader_projected(task);
        proof! {
            assert(Seq::new(context.files.len(), |i: int| before.states@[i as usize].id()) =~= ids);
            reader_completion_facts(&before, &result.2@);
            assert(crate::proof::joining::completion_covers(&result.2@, context.files, ids));
            assert forall|value: UResult<()>| #[trigger] result.1@.post(value) implies value is Ok by {
                let output = choose|output: crate::proof::joining::ReaderOutput|
                    <SourceReaderTask<M> as crate::proof::joining::Task>::post(&before, output) && output.0 == value;
                reader_post_facts(&before, output);
            };
        }
        result
    } };
    proof_decl! {
        let tracked completion = completion.get();
        let tracked reader = reader.get();
        let tracked lease = lease.get();
        let tracked progress = crate::proof::merging::begin_progress(&context, settings,
            crate::proof::merging::source(&context).len());
        let ghost original_receivers = receivers;
    }
    proof! {
        assert(lease.output_ids() =~= ids);
        assert(crate::proof::joining::completion_covers(&reader, context.files, ids));
        assert forall|value: UResult<()>| #[trigger] completion.post(value) implies value is Ok by {};
    }
    let mut mergeable_files: Vec<MergeableFile<'_>> = Vec::new();
    let mut file_number = 0;
    #[verus_spec(state =>
        invariant crate::proof::native_settings_valid(settings),
            crate::proof::merging::context_valid(&context, settings),
            crate::proof::merging::progress_valid(&context, &crate::proof::merging::progress_view(&progress), settings),
            progress.history.len() == 0, progress.remaining == crate::proof::merging::source(&context).len(),
            forall|i: usize| i < context.files.len() ==> #[trigger] progress.consumed[i] == 0,
            file_number == state.index(), state.seq().len() == context.files.len(),
            crate::proof::merging::startup_receivers(state.seq(), &original_receivers, context.files, settings),
            receivers.dom() == original_receivers.dom(),
            forall|i: usize| i < ids.len() ==> #[trigger] receivers[i].id() == ids[i as int],
            forall|i: usize| file_number <= i < ids.len() ==> #[trigger] receivers[i] == original_receivers[i],
            forall|i: int| 0 <= i < mergeable_files.len() ==> {
                let file = #[trigger] mergeable_files@[i];
                &&& file.file_number < file_number
                &&& crate::proof::merging::stream_cursor(&file, &crate::proof::merging::receiver_view(&receivers[file.file_number]),
                    context.files[file.file_number as int], 0, settings)
            },
            mergeable_files@.map_values(|file: MergeableFile| file.file_number).no_duplicates(),
            reader.success() ==> mergeable_files@.map_values(|file: MergeableFile| file.file_number)
                == crate::proof::merging::active_prefix(&context, &crate::proof::merging::progress_view(&progress), file_number as nat),
            crate::proof::joining::completion_covers(&reader, context.files, ids),
            reader.success() ==> reader.post(reader.value()),
            lease.output_ids() == ids, lease.handle_id() == reader.handle_id(), lease.request_id() == requests.id(),
            requests.id() == request_id, crate::trusted::concurrency::sender_id_unbounded(&request_sender) == requests.id(),
    )]
    for receiver in loaded_receivers {
        proof! {
            crate::proof::merging::startup_receiver(state.seq(), &original_receivers, context.files, settings, file_number);
            crate::proof::merging::index_member(context.files.len(), file_number);
            assert(receivers.contains_key(file_number));
            assert(progress.consumed.contains_key(file_number));
            assert(receivers[file_number] == original_receivers[file_number]);
        }
        proof_decl! {
            let ghost before_receivers = receivers;
            let tracked mut receiving = receivers.tracked_remove(file_number);
            let ghost before_files = mergeable_files@;
        }
        let received = verus_exec_expr! { crate::trusted::concurrency::recv(&receiver, Tracked(&mut receiving)) };
        if let Ok(chunk) = received {
            proof! { crate::proof::merging::input_chunk_facts(chunk, settings); }
            let file = MergeableFile { current_chunk: Rc::new(chunk), file_number, line_idx: 0, receiver, settings };
            proof! {
                assert(crate::proof::merging::stream_cursor(&file, &crate::proof::merging::receiver_view(&receiving),
                    context.files[file_number as int], 0, settings));
                crate::proof::merging::stream_cursor_head(&file, &crate::proof::merging::receiver_view(&receiving),
                    context.files[file_number as int], 0, settings);
            }
            mergeable_files.push(file);
        } else {
            verus_exec_expr! {
                crate::trusted::joining::reader_eof(&request_sender, Tracked(&receiving), Tracked(&reader), Tracked(&lease), Ghost(file_number))
            };
            proof! {
                if reader.success() {
                    crate::proof::joining::completed_file(&reader, context.files, ids, file_number);
                    assert(context.files[file_number as int].len() == 0);
                }
            }
        }
        proof! {
            broadcast use vstd::map::group_map_lemmas;
            receivers.tracked_insert(file_number, receiving);
            assert(receivers.dom() =~= before_receivers.dom());
            assert forall|i: usize| i < ids.len() implies #[trigger] receivers[i].id() == ids[i as int] by {
                if i != file_number { assert(receivers[i] == before_receivers[i]); }
            };
            assert forall|i: int| 0 <= i < mergeable_files.len() implies {
                let file = #[trigger] mergeable_files@[i];
                &&& file.file_number < file_number + 1
                &&& crate::proof::merging::stream_cursor(&file, &crate::proof::merging::receiver_view(&receivers[file.file_number]),
                    context.files[file.file_number as int], 0, settings)
            } by {
                if i < before_files.len() {
                    assert(mergeable_files@[i] == before_files[i]);
                    assert(before_files[i].file_number != file_number);
                    assert(receivers[before_files[i].file_number] == before_receivers[before_files[i].file_number]);
                }
            };
            let ids_before = before_files.map_values(|file: MergeableFile| file.file_number);
            let ids_after = mergeable_files@.map_values(|file: MergeableFile| file.file_number);
            assert(!ids_before.contains(file_number)) by {
                assert forall|j: int| 0 <= j < ids_before.len() implies ids_before[j] != file_number by {};
            };
            assert(ids_after == ids_before || ids_after == ids_before.push(file_number));
            assert(ids_after.no_duplicates());
            crate::proof::merging::active_prefix_step(&context, &crate::proof::merging::progress_view(&progress), file_number as nat);
            if reader.success() {
                assert(ids_after == crate::proof::merging::active_prefix(&context,
                    &crate::proof::merging::progress_view(&progress), file_number as nat + 1));
            }
        }
        file_number += 1;
    }
    proof! { crate::proof::merging::file_ord_compatible(settings); }
    proof_decl! { let ghost loaded = mergeable_files@; }
    let heap = verus_exec_expr! { crate::trusted::merging::heap_from(mergeable_files,
        Ghost(crate::proof::merging::file_domain(settings)), Ghost(crate::proof::merging::file_order())) };
    let merger = FileMerger { heap, request_sender, prev: None, reader_join_handle };
    proof! {
        crate::proof::merging::receiver_views_facts(&receivers);
        assert forall|i: int| 0 <= i < loaded.len() implies {
            let file = #[trigger] loaded[i];
            &&& file.file_number < context.files.len()
            &&& crate::proof::merging::stream_cursor(&file,
                &crate::proof::merging::receiver_views(&receivers)[file.file_number], context.files[file.file_number as int],
                progress.consumed[file.file_number], settings)
        } by {
            let file = loaded[i];
            crate::proof::merging::index_member(context.files.len(), file.file_number);
            assert(receivers.contains_key(file.file_number));
            assert(progress.consumed[file.file_number] == 0);
        };
        crate::proof::merging::initial_stream_heap(&merger, loaded, &context,
            &crate::proof::merging::progress_view(&progress), &crate::proof::merging::receiver_views(&receivers), settings);
    }
    proof_decl! { let tracked init = crate::proof::merging::StreamInit {
        context, receivers, requests, progress, completion, reader, lease, ids,
    }; }
    #[verus_spec(with |= Tracked(init))]
    Ok(merger)
}
/// The struct on the reader thread representing an input file
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct ReaderFile<M: MergeInput> {
    pub(crate) file: M,
    pub(crate) sender: SyncSender<Chunk>,
    pub(crate) carry_over: Vec<u8>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Ghost(expected): Ghost<Seq<u8>>,
        Tracked(state): Tracked<&mut crate::trusted::concurrency::SendState<Chunk>>,
    requires old(entry).file.valid(), crate::proof::native_settings_valid(settings),
        expected == crate::proof::joining::pending(old(entry), separator),
        crate::proof::input::recycled_empty(&recycled_chunk),
        crate::trusted::concurrency::sender_id(&old(entry).sender) == old(state).id(),
        !old(state).own_closed(),
        crate::proof::input::allows_read(old(state).rule(), old(state).index(), expected, separator, settings),
        old(state).index() <= crate::trusted::concurrency::channel_trace::<Chunk>(old(state).id()).len(),
        old(state).index() + expected.len() <= old(state).limit(),
    ensures result is Ok, final(entry).file.valid(), final(entry).sender == old(entry).sender,
        final(state).id() == old(state).id(), final(state).rule() == old(state).rule(),
        final(state).template() == old(state).template(), final(state).dependency() == old(state).dependency(),
        final(state).peer_closed() == old(state).peer_closed(), final(state).limit() == old(state).limit(),
        final(state).own_closed() == old(state).own_closed(),
        final(state).index() <= final(state).limit(),
        crate::proof::joining::read_rows(expected, crate::proof::joining::pending(final(entry), separator),
            separator, old(state).id(), old(state).index(), final(state).index(), result->Ok_0),
))]
fn read_reader_file<M: MergeInput>(
    entry: &mut ReaderFile<M>, recycled_chunk: RecycledChunk,
    settings: &GlobalSettings, separator: u8,
) -> UResult<bool> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = state.index(); let ghost id = state.id(); }
    let ReaderFile { file, sender, carry_over } = entry;
    let input = file.as_read();
    #[cfg(not(verus_keep_ghost))]
    let mut next_files = iter::empty();
    #[cfg(verus_keep_ghost)]
    let mut next_files = crate::trusted::joining::empty();
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::proof::input::pending(carry_over@, input, next_files.remaining(), separator) == expected);
    }
    #[cfg(verus_keep_ghost)]
    proof_with! { Tracked(&mut *state) }
    let continued = chunks::read(sender, recycled_chunk, None, carry_over, input, &mut next_files, separator, settings)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(next_files.remaining() =~= Seq::<UResult<M::InnerRead>>::empty());
        crate::proof::joining::read_effect_rows(expected, carry_over@, input, separator, settings,
            id, before, state.index(), continued);
    }
    Ok(continued)
}

/// The function running on the reader thread.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(states): Tracked<&mut Map<usize, crate::trusted::concurrency::SendState<Chunk>>>,
        Tracked(requests): Tracked<&mut crate::trusted::concurrency::RecvState<(usize, RecycledChunk)>>,
        Ghost(source): Ghost<Seq<Seq<Seq<u8>>>>,
    requires crate::proof::native_settings_valid(settings), separator == crate::trusted::ending_byte(settings.line_ending),
        crate::proof::joining::files_progress(old(files)@, old(states), source, settings, separator),
        crate::trusted::concurrency::receiver_id(recycled_receiver) == old(requests).id(),
        !old(requests).peer_closed(),
        old(requests).index() <= old(requests).limit(),
        forall|i: nat, request: (usize, RecycledChunk)| #[trigger] old(requests).rule()(i, request)
            ==> request.0 < old(files).len() && crate::proof::input::recycled_empty(&request.1),
    ensures result is Ok,
        crate::proof::joining::files_progress(final(files)@, final(states), source, settings, separator),
        crate::trusted::concurrency::same_recv_channel(old(requests), final(requests)),
        final(requests).peer_closed(),
        forall|i: usize| old(states).dom().contains(i) ==>
            crate::proof::joining::reader_state_extends(&old(states)[i], &final(states)[i]),
))]
fn reader<M: MergeInput>(
    recycled_receiver: &Receiver<(usize, RecycledChunk)>,
    files: &mut [Option<ReaderFile<M>>],
    settings: &GlobalSettings,
    separator: u8,
) -> UResult<()> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before_states = *states;
        let ghost before_requests = *requests;
        let ghost count = files.len();
        let ghost request_rule = requests.rule();
        let ghost request_id = requests.id();
        let ghost request_limit = requests.limit();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: usize| before_states.dom().contains(i)
            implies crate::proof::joining::reader_state_extends(&before_states[i], &states[i]) by {
            crate::proof::joining::progress_member(files@, states, source, settings, separator, i);
            crate::proof::joining::state_extends_reflexive(&states[i]);
        };
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant crate::proof::native_settings_valid(settings), files.len() == count,
            separator == crate::trusted::ending_byte(settings.line_ending),
            crate::proof::joining::files_progress(files@, states, source, settings, separator),
            crate::trusted::concurrency::same_recv_channel(&before_requests, requests),
            crate::trusted::concurrency::receiver_id(recycled_receiver) == requests.id(),
            requests.rule() == request_rule, requests.id() == request_id, requests.limit() == request_limit,
            forall|i: nat, request: (usize, RecycledChunk)| #[trigger] request_rule(i, request)
                ==> request.0 < count && crate::proof::input::recycled_empty(&request.1),
            forall|i: usize| before_states.dom().contains(i) ==>
                crate::proof::joining::reader_state_extends(&before_states[i], &states[i]),
        invariant_except_break !requests.peer_closed(),
        ensures requests.peer_closed(),
        decreases request_limit - requests.index(),
    ))]
    while let Ok((file_idx, recycled_chunk)) = {
        #[cfg(not(verus_keep_ghost))]
        { recycled_receiver.recv() }
        #[cfg(verus_keep_ghost)]
        { crate::trusted::concurrency::recv(recycled_receiver, verus_exec_expr! { Tracked(&mut *requests) }) }
    } {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::joining::progress_index(files@, states, source, settings, separator, file_idx); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost old_files = files@;
            let ghost old_states = *states;
            let tracked mut state = states.tracked_remove(file_idx);
        }
        if let Some(entry) = &mut files[file_idx] {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(old_files[file_idx as int] == Some(*entry));
                assert(crate::proof::joining::file_progress(Some(*entry), &state,
                    source[file_idx as int], settings, separator));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost expected = crate::proof::joining::pending(entry, separator);
                let ghost previous = state.index();
                let ghost id = state.id();
            }
            #[cfg(verus_keep_ghost)]
            proof! { crate::proof::joining::allow_reader_read(source[file_idx as int], expected, separator, settings, &state); }
            #[cfg(verus_keep_ghost)]
            proof_with! { Ghost(expected), Tracked(&mut state) }
            let should_continue = read_reader_file(entry, recycled_chunk, settings, separator)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::joining::append_read(source[file_idx as int], expected,
                    crate::proof::joining::pending(entry, separator), separator, id, previous, state.index(), should_continue);
            }
            if !should_continue {
                // Remove the file from the list by replacing it with `None`.
                #[cfg(not(verus_keep_ghost))]
                let ReaderFile { file, .. } = files[file_idx].take().unwrap();
                #[cfg(verus_keep_ghost)]
                let ReaderFile { file, sender, .. } = files[file_idx].take().unwrap();
                #[cfg(verus_keep_ghost)]
                verus_exec_expr! { crate::trusted::joining::close_chunk_sender(sender, Tracked(&mut state)) };
                // Depending on the kind of the `MergeInput`, this may delete the file:
                file.finished_reading()?;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::proof::joining::file_progress(files@[file_idx as int], &state,
                source[file_idx as int], settings, separator));
            assert(crate::proof::joining::reader_state_extends(&old_states[file_idx], &state));
            states.tracked_insert(file_idx, state);
            assert(files@ == old_files.update(file_idx as int, files@[file_idx as int]));
            assert(*states == old_states.insert(file_idx, states[file_idx]));
            crate::proof::joining::progress_update(old_files, files@, &old_states, states,
                source, settings, separator, file_idx);
            assert forall|i: usize| before_states.dom().contains(i)
                implies crate::proof::joining::reader_state_extends(&before_states[i], &states[i]) by {
                if i == file_idx {
                    crate::proof::joining::state_extends_transitive(&before_states[i], &old_states[i], &states[i]);
                }
            };
        }
    }
    Ok(())
}

#[cfg(verus_keep_ghost)]
#[verus_verify]
pub(crate) struct SourceReaderTask<M: MergeInput + 'static> {
    pub(crate) recycled_receiver: Receiver<(usize, RecycledChunk)>,
    pub(crate) files: Vec<Option<ReaderFile<M>>>,
    pub(crate) settings: GlobalSettings,
    pub(crate) separator: u8,
    pub(crate) states: Tracked<Map<usize, crate::trusted::concurrency::SendState<Chunk>>>,
    pub(crate) requests: Tracked<crate::trusted::concurrency::RecvState<(usize, RecycledChunk)>>,
    pub(crate) source: Ghost<Seq<Seq<Seq<u8>>>>,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl<M: MergeInput + 'static> crate::proof::joining::Task for SourceReaderTask<M> {
        type Output = crate::proof::joining::ReaderOutput;

        #[verifier::prophetic]
        open(crate) spec fn ready(&self) -> bool {
            &&& crate::proof::native_settings_valid(&self.settings)
            &&& self.separator == crate::trusted::ending_byte(self.settings.line_ending)
            &&& crate::proof::joining::files_progress(self.files@, &self.states@, self.source@, &self.settings, self.separator)
            &&& crate::trusted::concurrency::receiver_id(&self.recycled_receiver) == self.requests@.id()
            &&& !self.requests@.peer_closed() && self.requests@.index() <= self.requests@.limit()
            &&& forall|i: nat, request: (usize, RecycledChunk)| #[trigger] self.requests@.rule()(i, request)
                ==> request.0 < self.files.len() && crate::proof::input::recycled_empty(&request.1)
        }

        #[verifier::prophetic]
        open(crate) spec fn post(&self, result: Self::Output) -> bool {
            &&& result.0 is Ok
            &&& crate::proof::joining::final_progress(&result.1@, self.source@)
            &&& crate::trusted::concurrency::same_recv_channel(&self.requests@, &result.1@.requests)
            &&& result.1@.requests.peer_closed()
            &&& forall|i: usize| self.states@.dom().contains(i) ==>
                crate::proof::joining::reader_state_extends(&self.states@[i], &result.1@.states[i])
        }

        fn run(self) -> Self::Output {
            proof {
                reveal(<SourceReaderTask<_> as crate::proof::joining::Task>::ready);
                reveal(<SourceReaderTask<_> as crate::proof::joining::Task>::post);
            }
            let mut task = self;
            let tracked mut states = task.states.get();
            let tracked mut requests = task.requests.get();
            let result = _VERUS_VERIFIED_reader(&task.recycled_receiver, task.files.as_mut_slice(),
                &task.settings, task.separator, Tracked(&mut states), Tracked(&mut requests), task.source);
            let ghost active = crate::proof::joining::active_files(task.files@);
            let ghost remaining = crate::proof::joining::remaining_rows(task.files@, task.separator);
            let tracked final_state = crate::proof::joining::ReaderFinal { states, requests, active, remaining };
            proof {
                crate::proof::joining::establish_final(task.files@, &final_state, task.source@, &task.settings, task.separator);
            }
            (result, Tracked(final_state))
        }
    }

    pub(crate) proof fn reader_post_facts<M: MergeInput + 'static>(task: &SourceReaderTask<M>,
        result: crate::proof::joining::ReaderOutput)
        requires <SourceReaderTask<M> as crate::proof::joining::Task>::ready(task),
            <SourceReaderTask<M> as crate::proof::joining::Task>::post(task, result),
        ensures result.0 is Ok, crate::proof::joining::final_progress(&result.1@, task.source@),
            forall|i: int| 0 <= i < task.source@.len() ==> #[trigger] result.1@.states.dom().contains(i as usize),
            forall|i: int| 0 <= i < task.source@.len() ==>
                #[trigger] result.1@.states[i as usize].id() == task.states@[i as usize].id(),
    {
        reveal(<SourceReaderTask<_> as crate::proof::joining::Task>::ready);
        reveal(<SourceReaderTask<_> as crate::proof::joining::Task>::post);
        assert forall|i: int| 0 <= i < task.source@.len() implies #[trigger] result.1@.states.dom().contains(i as usize) by {
            let ids = Seq::new(task.source@.len(), |j: int| j as usize);
            assert(ids[i] == i as usize);
            assert(ids.contains(i as usize));
        };
        assert forall|i: int| 0 <= i < task.source@.len() implies
            #[trigger] result.1@.states[i as usize].id() == task.states@[i as usize].id() by {
            crate::proof::joining::progress_index(task.files@, &task.states@, task.source@,
                &task.settings, task.separator, i as usize);
            let ids = Seq::new(task.source@.len(), |j: int| j as usize);
            assert(ids[i] == i as usize);
            assert(ids.contains(i as usize));
            assert(result.1@.states.dom().contains(i as usize));
            assert(crate::proof::joining::reader_state_extends(&task.states@[i as usize], &result.1@.states[i as usize]));
            assert(result.1@.states[i as usize].id() == task.states@[i as usize].id());
        };
    }

    pub(crate) proof fn reader_completion_facts<M: MergeInput + 'static>(task: &SourceReaderTask<M>,
        completion: &crate::trusted::joining::Completion<crate::proof::joining::ReaderOutput>)
        requires <SourceReaderTask<M> as crate::proof::joining::Task>::ready(task),
            forall|output: crate::proof::joining::ReaderOutput| #[trigger] completion.post(output)
                == <SourceReaderTask<M> as crate::proof::joining::Task>::post(task, output),
        ensures crate::proof::joining::completion_covers(completion, task.source@,
            Seq::new(task.source@.len(), |i: int| task.states@[i as usize].id())),
    {
        let ids = Seq::new(task.source@.len(), |i: int| task.states@[i as usize].id());
        reveal(<SourceReaderTask<_> as crate::proof::joining::Task>::ready);
        assert forall|output: crate::proof::joining::ReaderOutput| #[trigger] completion.post(output)
            implies output.0 is Ok && crate::proof::joining::final_progress(&output.1@, task.source@)
                && (forall|i: int| 0 <= i < task.source@.len() ==>
                    #[trigger] output.1@.states[i as usize].id() == ids[i]) by {
            reader_post_facts(task, output);
        };
        assert(ids.len() == task.source@.len());
        assert(crate::proof::joining::completion_covers(completion, task.source@, ids));
    }
}

/// The struct on the main thread representing an input file
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct MergeableFile<'a> {
    pub(crate) current_chunk: Rc<Chunk>,
    pub(crate) line_idx: usize,
    pub(crate) receiver: Receiver<Chunk>,
    pub(crate) file_number: usize,
    pub(crate) settings: &'a GlobalSettings,
}


macro_rules! delegate_ord {
    ($life:lifetime, $ty:ty, $helper:ident, $contract:ident, $facts:ident) => {
        impl<$life> PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool { self.cmp(other) == Ordering::Equal }
        }
        impl<$life> Eq for $ty {}
        impl<$life> PartialOrd for $ty {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
        }
        impl<$life> Ord for $ty {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering { $helper(self, other) }
        }
        #[cfg(verus_keep_ghost)]
        crate::trusted::merging::register_ord_delegate!($life, $ty, $helper, $contract, $facts);
    };
}

delegate_ord!('a, MergeableFile<'a>, compare_files, file_ord_contract, file_ord_facts);

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::proof::merging::file_pair_valid(a, b),
    ensures result == crate::proof::merging::file_cmp(a, b),
))]
pub(crate) fn compare_files(a: &MergeableFile<'_>, b: &MergeableFile<'_>) -> Ordering {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proof::merging::file_pair_facts(a, b);
        crate::proof::merging::file_cmp_model(a, b);
    }
    let mut cmp = merge_compare(
        &a.current_chunk.lines()[a.line_idx],
        &b.current_chunk.lines()[b.line_idx],
        a.settings,
        a.current_chunk.line_data(),
        b.current_chunk.line_data(),
    );
    if cmp == Ordering::Equal {
        // Equal lines from an earlier file come first.
        cmp = a.file_number.cmp(&b.file_number);
    }
    // BinaryHeap uses the reversed order to select the smallest line.
    cmp.reverse()
}

/// A struct to keep track of the previous line we encountered.
///
/// This is required for deduplication purposes.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct PreviousLine {
    pub(crate) chunk: Rc<Chunk>,
    pub(crate) line_idx: usize,
    pub(crate) file_number: usize,
}

/// Merges files together. This is **not** an iterator because of lifetime problems.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FileMerger<'a> {
    pub(crate) heap: BinaryHeap<MergeableFile<'a>>,
    pub(crate) request_sender: Sender<(usize, RecycledChunk)>,
    pub(crate) prev: Option<PreviousLine>,
    pub(crate) reader_join_handle: JoinHandle<UResult<()>>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
    requires crate::proof::merging::file_valid(file, settings),
        *contents == crate::trusted::ownership::contents(&*file.current_chunk),
        match previous { None => true, Some(previous) => crate::proof::merging::previous_valid(previous, settings) },
        crate::trusted::writer_session(old(writer)) == old(log).session(),
    ensures result is Ok, final(log).session() == old(log).session(),
        crate::trusted::writer_session(final(writer)) == final(log).session(),
        final(log).bytes() == old(log).bytes() + crate::proof::merging::output_delta(file, previous, settings),
))]
fn write_merge_line(
    contents: &chunks::ChunkContents<'_>,
    file: &MergeableFile<'_>,
    previous: &Option<PreviousLine>,
    writer: &mut impl Write,
    settings: &GlobalSettings,
) -> io::Result<()> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::native_settings_facts(settings); }
    let current_line = &contents.lines[file.line_idx];
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::sorting::native_line_value(current_line); }
    if settings.unique {
        if let Some(previous) = previous {
            let cmp = merge_compare(
                &previous.chunk.lines()[previous.line_idx],
                current_line,
                settings,
                previous.chunk.line_data(),
                file.current_chunk.line_data(),
            );
            if cmp == Ordering::Equal {
                return Ok(());
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof_with! { Tracked(&mut *log) }
    current_line.write(writer, settings)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires crate::proof::merging::file_valid(old(file), old(file).settings),
        crate::proof::pipeline::input_message(next_chunk, old(file).settings),
    ensures crate::proof::merging::file_valid(final(file), old(file).settings),
        *final(file).current_chunk == next_chunk, final(file).line_idx == 0,
        final(file).receiver == old(file).receiver, final(file).file_number == old(file).file_number,
        final(file).settings == old(file).settings,
))]
fn advance_merge_file(file: &mut MergeableFile<'_>, next_chunk: Chunk) {
    #[cfg(verus_keep_ghost)]
    proof! { crate::proof::merging::input_chunk_facts(next_chunk, file.settings); }
    file.current_chunk = Rc::new(next_chunk);
    file.line_idx = 0;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires crate::proof::merging::file_valid(old(file), old(file).settings),
        old(file).line_idx + 1 < crate::trusted::ownership::contents(&*old(file).current_chunk).lines.len(),
    ensures crate::proof::merging::file_valid(final(file), old(file).settings),
        final(file).current_chunk == old(file).current_chunk, final(file).line_idx == old(file).line_idx + 1,
        final(file).receiver == old(file).receiver, final(file).file_number == old(file).file_number,
        final(file).settings == old(file).settings,
))]
fn advance_merge_cursor(file: &mut MergeableFile<'_>) {
    file.line_idx += 1;
}

impl FileMerger<'_> {
    /// Write the merged contents to the output file.
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
            Tracked(init): Tracked<crate::proof::merging::StreamInit>,
        requires crate::proof::merging::stream_ready(&self, &init, settings),
            old(log).session() == crate::trusted::output_session(output),
        ensures result is Ok, final(log).session() == old(log).session(), final(log).flushed(),
            final(log).bytes() == crate::proof::merging::output(init.context.files, settings),
    ))]
    fn write_all(self, settings: &GlobalSettings, output: Output) -> UResult<()> {
        #[cfg(not(verus_keep_ghost))]
        let ctx = output.write_failed_context();
        #[cfg(verus_keep_ghost)]
        let ctx = || String::new();
        #[cfg(not(verus_keep_ghost))]
        let mut out = output.into_write()?;
        #[cfg(verus_keep_ghost)]
        proof_with! { Tracked(&mut *log) }
        #[cfg(verus_keep_ghost)]
        let mut out = crate::trusted::output_writer(output)?;
        #[cfg(verus_keep_ghost)]
        proof_with! { Tracked(&mut *log), Tracked(init) }
        self.write_all_to(settings, &mut out, &ctx)?;
        #[cfg(not(verus_keep_ghost))]
        { out.flush().map_err_context(ctx).map_err(Into::into) }
        #[cfg(verus_keep_ghost)]
        {
            proof_with! { Tracked(&mut *log) }
            crate::trusted::flush_output(&mut out)?;
            Ok(())
        }
    }

    /// Write the merged contents to `out`, reporting write errors with `ctx`.
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
            Tracked(init): Tracked<crate::proof::merging::StreamInit>,
        requires crate::proof::merging::stream_ready(&self, &init, settings),
            crate::trusted::writer_session(old(out)) == old(log).session(),
        ensures result is Ok, final(log).session() == old(log).session(), crate::trusted::writer_session(final(out)) == final(log).session(),
            final(log).bytes() == old(log).bytes() + crate::proof::merging::output(init.context.files, settings),
    ))]
    fn write_all_to(
        self,
        settings: &GlobalSettings,
        out: &mut impl Write,
        ctx: impl FnOnce() -> String,
    ) -> UResult<()> {
        let mut this = self;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let tracked mut init = init;
            let ghost context_value = init.context;
            let ghost context = &context_value;
            let ghost prefix = log.bytes();
            let ghost session = log.session();
            let ghost sender = this.request_sender;
            let ghost reader_handle = this.reader_join_handle;
            let ghost reader_identity = init.reader;
            let ghost completion_identity = init.completion;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(crate::proof::merging::emitted(context, &crate::proof::merging::progress_view(&init.progress), settings).len() == 0); }
        let mut write_result = Ok(());
          #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant crate::proof::merging::stream_session(&this, &init, settings), init.context == context_value,
                *context == context_value, init.reader == reader_identity, init.completion == completion_identity,
                log.session() == session, crate::trusted::writer_session(out) == session,
                write_result is Ok,
                init.reader.success() ==> log.bytes() == prefix + crate::proof::merging::emitted(context,
                    &crate::proof::merging::progress_view(&init.progress), settings),
                this.request_sender == sender, this.reader_join_handle == reader_handle,
            ensures crate::trusted::merging::heap_values(&this.heap).len() == 0,
            decreases init.progress.remaining,
          ))]
          loop {
            #[cfg(verus_keep_ghost)]
            proof_with! { Tracked(&mut *log), Tracked(&mut init), Ghost(prefix) }
            let next = this.write_next(out, settings);
            match next {
                Ok(true) => (),
                Ok(false) => break,
                Err(error) => {
                    // Don't return yet: we still have to shut the reader thread down in an
                    // orderly fashion below. Returning here would drop our receivers while
                    // the reader is still sending, and `chunks::read` unwraps that send.
                    write_result = Err(error);
                    break;
                }
            }
          }
        #[cfg(verus_keep_ghost)]
        proof! {
            if init.reader.success() {
                assert(crate::proof::merging::merger_valid(&this, context, &crate::proof::merging::progress_view(&init.progress),
                    &crate::proof::merging::receiver_views(&init.receivers), settings));
                crate::proof::merging::exhausted(&this, context, &crate::proof::merging::progress_view(&init.progress),
                    &crate::proof::merging::receiver_views(&init.receivers), settings);
                crate::proof::merging::emitted_complete(context, &crate::proof::merging::progress_view(&init.progress), settings);
            }
        }

        let Self {
            heap,
            request_sender,
            reader_join_handle,
            ..
        } = this;

        // Stop asking for chunks, so the reader runs out of work and returns.
        #[cfg(not(verus_keep_ghost))]
        drop(request_sender);
        #[cfg(verus_keep_ghost)]
        crate::trusted::merging::drop_sender(request_sender);
        // Until it does, keep draining the files it might still be sending to. We have to
        // poll all of them in turn rather than draining one at a time: the reader can be
        // blocked on any one channel, and blocking on a different one would deadlock.
        #[cfg(not(verus_keep_ghost))]
        let mut files = heap.into_vec();
        #[cfg(verus_keep_ghost)]
        let files = crate::trusted::merging::heap_into_vec(heap);
        #[cfg(verus_keep_ghost)]
        proof! { assert(files.len() == 0); }
        #[cfg(not(verus_keep_ghost))]
        while !files.is_empty() {
            files.retain(|file| {
                !matches!(file.receiver.try_recv(), Err(TryRecvError::Disconnected))
            });
            thread::yield_now();
        }

        #[cfg(not(verus_keep_ghost))]
        let reader_result = reader_join_handle.join().unwrap();
        #[cfg(verus_keep_ghost)]
        let reader_result = verus_exec_expr! { crate::trusted::joining::join_or_unwind(reader_join_handle, Tracked(init.completion)) };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(completion_identity.success());
            assert(reader_identity.success());
            assert(log.bytes() == prefix + crate::proof::merging::output(context.files, settings));
        }
        // A write failure is what the user needs to hear about; the reader hitting an error
        // on the way down is secondary.
        #[cfg(not(verus_keep_ghost))]
        { write_result.map_err_context(ctx).map_err(Into::into).and(reader_result) }
        #[cfg(verus_keep_ghost)]
        { reader_result }
    }

    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with Tracked(log): Tracked<&mut crate::proof::OutputLog>,
            Tracked(init): Tracked<&mut crate::proof::merging::StreamInit>,
            Ghost(prefix): Ghost<vstd::seq::Seq<u8>>,
        requires crate::proof::merging::stream_session(old(self), old(init), settings),
            crate::trusted::writer_session(old(writer)) == old(log).session(),
            old(init).reader.success() ==> old(log).bytes() == prefix
                + crate::proof::merging::emitted(&old(init).context, &crate::proof::merging::progress_view(&old(init).progress), settings),
        ensures result is Ok,
            result->Ok_0 == (crate::trusted::merging::heap_values(&final(self).heap).len() > 0),
            result->Ok_0 ==> crate::trusted::merging::heap_values(&old(self).heap).len() > 0,
            crate::proof::merging::stream_session(final(self), final(init), settings),
            final(init).context == old(init).context, final(init).ids == old(init).ids,
            final(init).reader == old(init).reader, final(init).lease == old(init).lease,
            final(init).completion == old(init).completion,
            final(init).progress.remaining == if crate::trusted::merging::heap_values(&old(self).heap).len() > 0 {
                old(init).progress.remaining - 1 } else { old(init).progress.remaining as int },
            final(log).session() == old(log).session(),
            crate::trusted::writer_session(final(writer)) == final(log).session(),
            final(init).reader.success() ==> final(log).bytes() == prefix
                + crate::proof::merging::emitted(&final(init).context, &crate::proof::merging::progress_view(&final(init).progress), settings),
            final(self).request_sender == old(self).request_sender,
            final(self).reader_join_handle == old(self).reader_join_handle,
    ))]
    fn write_next(
        &mut self,
        writer: &mut impl Write,
        settings: &GlobalSettings,
    ) -> io::Result<bool> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost context = &init.context;
            let ghost ids = init.ids;
            let tracked reader = &init.reader;
            let tracked lease = &init.lease;
            let tracked receivers = &mut init.receivers;
            let tracked requests = &mut init.requests;
            let tracked progress = &mut init.progress;
            let ghost before = *self;
            let ghost old_receivers = crate::proof::merging::receiver_views(receivers);
            let ghost old_progress = crate::proof::merging::progress_view(progress);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::merging::file_ord_compatible(settings);
            crate::proof::merging::receiver_views_facts(receivers);
        }
        #[cfg(not(verus_keep_ghost))]
        let selected = self.heap.peek();
        #[cfg(verus_keep_ghost)]
        let selected = verus_exec_expr! { crate::trusted::merging::heap_peek(&self.heap,
            Ghost(crate::proof::merging::file_domain(settings)), Ghost(crate::proof::merging::file_order())) };
        if let Some(file) = selected {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proof::merging::stream_cursor_head(file, &old_receivers[file.file_number],
                    context.files[file.file_number as int], old_progress.consumed[file.file_number], settings);
                if reader.success() {
                    crate::proof::merging::stream_selection(&before, context, &old_progress, &old_receivers, settings);
                    crate::proof::merging::heap_head_minimum(&before, context, &old_progress, &old_receivers, settings, file);
                    crate::proof::merging::selected_canonical(&before, context, &old_progress, &old_receivers, settings, file);
                    crate::proof::merging::output_step(&before, context, &old_progress, &old_receivers, settings, file);
                }
                let ids = Seq::new(context.files.len(), |i: int| i as usize);
                ids.to_set_ensures();
                assert(ids[file.file_number as int] == file.file_number);
                assert(ids.to_set().contains(file.file_number));
                assert(receivers.contains_key(file.file_number));
                assert(crate::proof::merging::receiver_valid(file, &old_receivers[file.file_number], settings));
                crate::proof::merging::budget_step(context, &old_progress, file.file_number);
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost selected_file = *file; let ghost mut replacement = None; }
            #[cfg(not(verus_keep_ghost))]
            let previous_chunk = file.current_chunk.clone();
            #[cfg(verus_keep_ghost)]
            let previous_chunk = crate::trusted::merging::rc_clone(&file.current_chunk);
            let prev = self.prev.replace(PreviousLine {
                chunk: previous_chunk,
                line_idx: file.line_idx,
                file_number: file.file_number,
            });

            #[cfg(not(verus_keep_ghost))]
            file.current_chunk.with_dependent(|_, contents| {
                write_merge_line(contents, file, &prev, writer, settings)
            })?;
            #[cfg(verus_keep_ghost)]
            {
                let contents = file.current_chunk.borrow_dependent();
                proof_with! { Tracked(&mut *log) }
                write_merge_line(contents, file, &prev, writer, settings)?;
            }

            let was_last_line_for_file = file.current_chunk.lines().len() == file.line_idx + 1;

            if was_last_line_for_file {
                #[cfg(not(verus_keep_ghost))]
                let received = file.receiver.recv();
                #[cfg(verus_keep_ghost)]
                let received = verus_exec_expr! { {
                    let tracked state = receivers.tracked_borrow_mut(file.file_number);
                    proof! {
                        assert(crate::proof::merging::receiver_view(state) == old_receivers[file.file_number]);
                    }
                    let result = crate::trusted::concurrency::recv(&file.receiver, Tracked(&mut *state));
                    proof! {
                        assert(crate::proof::merging::receiver_metadata(&old_receivers[file.file_number],
                            &crate::proof::merging::receiver_view(state)));
                        match &result {
                            Ok(chunk) => {
                                crate::proof::merging::receiver_payload(file, &old_receivers[file.file_number], settings,
                                    old_receivers[file.file_number].index, *chunk);
                            },
                            Err(_) => { assert(old_receivers[file.file_number].index
                                == crate::trusted::concurrency::channel_trace::<Chunk>(old_receivers[file.file_number].id).len()); },
                        }
                    }
                    result
                } };
                #[cfg(verus_keep_ghost)]
                proof! { crate::proof::merging::receiver_views_facts(receivers); }
                if let Ok(next_chunk) = received {
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(crate::proof::pipeline::input_message(next_chunk, settings)); }
                    #[cfg(not(verus_keep_ghost))]
                    {
                    let mut file = self.heap.peek_mut().unwrap();
                    advance_merge_file(&mut file, next_chunk);
                    }
                    #[cfg(verus_keep_ghost)]
                    verus_exec_expr! { {
                        let update = |entry: &mut MergeableFile|
                            requires *entry == selected_file,
                                crate::proof::merging::file_valid(entry, settings),
                            ensures crate::proof::merging::file_valid(final(entry), settings),
                                *final(entry).current_chunk == next_chunk, final(entry).line_idx == 0,
                                final(entry).receiver == old(entry).receiver, final(entry).file_number == old(entry).file_number,
                                final(entry).settings == old(entry).settings,
                        { advance_merge_file(entry, next_chunk); };
                        let next_file = crate::trusted::merging::heap_update_top(&mut self.heap, update,
                            Ghost(crate::proof::merging::file_domain(settings)), Ghost(crate::proof::merging::file_order()));
                        proof! {
                            crate::proof::merging::stream_cursor_chunk(&selected_file, &next_file@,
                                &old_receivers[selected_file.file_number],
                                &crate::proof::merging::receiver_views(receivers)[selected_file.file_number],
                                context.files[selected_file.file_number as int], old_progress.consumed[selected_file.file_number], settings);
                            replacement = Some(next_file@);
                        }
                    } }
                } else {
                    #[cfg(verus_keep_ghost)]
                    verus_exec_expr! { crate::trusted::joining::reader_eof(&self.request_sender,
                        Tracked(receivers.tracked_borrow(selected_file.file_number)), Tracked(reader), Tracked(lease), Ghost(selected_file.file_number)) };
                    #[cfg(not(verus_keep_ghost))]
                    self.heap.pop();
                    #[cfg(verus_keep_ghost)]
                    verus_exec_expr! { {
                        proof! {
                            if reader.success() {
                                crate::proof::joining::completed_file(reader, context.files, ids, selected_file.file_number);
                                crate::proof::merging::stream_cursor_eof(&selected_file, &old_receivers[selected_file.file_number],
                                    context.files[selected_file.file_number as int], old_progress.consumed[selected_file.file_number], settings);
                            }
                        }
                        crate::trusted::merging::heap_pop(&mut self.heap,
                        Ghost(crate::proof::merging::file_domain(settings)), Ghost(crate::proof::merging::file_order())); } }
                }
            } else {
                // This will cause the comparison to use a different line and the heap to readjust.
                #[cfg(not(verus_keep_ghost))]
                advance_merge_cursor(&mut self.heap.peek_mut().unwrap());
                #[cfg(verus_keep_ghost)]
                verus_exec_expr! { {
                    let update = |entry: &mut MergeableFile|
                        requires *entry == selected_file,
                            crate::proof::merging::file_valid(entry, settings),
                            entry.line_idx + 1 < crate::trusted::ownership::contents(&*entry.current_chunk).lines.len(),
                        ensures crate::proof::merging::file_valid(final(entry), settings),
                            final(entry).current_chunk == old(entry).current_chunk, final(entry).line_idx == old(entry).line_idx + 1,
                            final(entry).receiver == old(entry).receiver, final(entry).file_number == old(entry).file_number == selected_file.file_number,
                            final(entry).settings == old(entry).settings,
                    { advance_merge_cursor(entry); };
                    let next_file = crate::trusted::merging::heap_update_top(&mut self.heap, update,
                        Ghost(crate::proof::merging::file_domain(settings)), Ghost(crate::proof::merging::file_order()));
                    proof! {
                        crate::proof::merging::stream_cursor_advance(&selected_file, &next_file@,
                            &old_receivers[selected_file.file_number], context.files[selected_file.file_number as int],
                            old_progress.consumed[selected_file.file_number], settings);
                        replacement = Some(next_file@);
                    }
                } }
            }

            if let Some(prev) = prev {
              if let Ok(prev_chunk) = Rc::try_unwrap(prev.chunk) {
                // If nothing is referencing the previous chunk anymore, this means that the previous line
                // was the last line of the chunk. We can recycle the chunk.
                #[cfg(not(verus_keep_ghost))]
                self.request_sender
                    .send((prev.file_number, prev_chunk.recycle()))
                    .ok();
                #[cfg(verus_keep_ghost)]
                verus_exec_expr! { {
                    let request = (prev.file_number, prev_chunk.recycle());
                    crate::trusted::concurrency::send_unbounded(&self.request_sender, request, Tracked(&mut *requests)).ok();
                } }
              }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::map::group_map_lemmas;
                crate::proof::merging::receiver_views_facts(receivers);
                assert(crate::proof::merging::receiver_views(receivers).dom() == old_receivers.dom());
                assert forall|id: usize| old_receivers.contains_key(id) && id != selected_file.file_number implies
                    #[trigger] crate::proof::merging::receiver_views(receivers)[id] == old_receivers[id] by {};
                crate::proof::merging::stream_transition(&before, self, context, &old_progress,
                    &old_receivers, &crate::proof::merging::receiver_views(receivers), settings, &selected_file, replacement);
                crate::proof::merging::consume_budget(context, progress, selected_file.file_number);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if reader.success() {
                assert(crate::proof::merging::stream_complete(self, context, &crate::proof::merging::progress_view(progress),
                    &crate::proof::merging::receiver_views(receivers), settings));
            }
        }
        #[cfg(not(verus_keep_ghost))]
        { Ok(!self.heap.is_empty()) }
        #[cfg(verus_keep_ghost)]
        { Ok(!crate::trusted::merging::heap_empty(&self.heap)) }
    }
}

/// Wait for the child to exit and check its exit code.
fn check_child_success(mut child: Child, program: &str) -> UResult<()> {
    if matches!(child.wait().map(|e| e.code()), Ok(Some(0) | None) | Err(_)) {
        Ok(())
    } else {
        Err(SortError::CompressProgTerminatedAbnormally {
            prog: program.to_owned(),
        }
        .into())
    }
}

/// A temporary file that can be written to.
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub trait WriteableTmpFile: Sized + WriterModel {
    type Closed: ClosedTmpFile;
    type InnerWrite: Write;
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires Self::supported(), compress_prog is None,
            crate::trusted::temporary::file_session(&file.0) == log@.session(),
            crate::trusted::temporary::path_session(&file.1) == log@.session(), log@.bytes().len() == 0,
        ensures result is Ok, result->Ok_0.valid(), result->Ok_0.session() == log@.session(),
    ))]
    fn create(file: (File, TmpPath), compress_prog: Option<&str>,
        #[cfg(verus_keep_ghost)] log: Tracked<&crate::proof::OutputLog>,
    ) -> UResult<Self>;
    /// Closes the temporary file.
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires Self::supported(), self.valid(), self.session() == log@.session(),
        ensures result is Ok, result->Ok_0.valid(), result->Ok_0.bytes() == log@.bytes(),
    ))]
    fn finished_writing(self,
        #[cfg(verus_keep_ghost)] log: Tracked<crate::proof::OutputLog>,
    ) -> UResult<Self::Closed>;
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).valid(),
        ensures crate::trusted::writer_session(&*result) == old(self).session(),
            final(self).session() == crate::trusted::writer_session(&*final(result)),
            crate::trusted::writer_session(&*final(result)) == old(self).session()
                ==> final(self).valid(),
    ))]
    fn as_write(&mut self) -> &mut Self::InnerWrite;
}
/// A temporary file that is (temporarily) closed, but can be reopened.
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub trait ClosedTmpFile: ClosedModel {
    type Reopened: MergeInput;
    /// Reopens the temporary file.
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.valid(),
        ensures result is Ok, result->Ok_0.valid(), result->Ok_0.bytes() == self.bytes(),
    ))]
    fn reopen(self) -> UResult<Self::Reopened>;
}
/// A pre-sorted input for merging.
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub trait MergeInput: Send + InputModel {
    type InnerRead: Read;
    /// Cleans this `MergeInput` up.
    /// Implementations may delete the backing file.
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.valid(), ensures result is Ok,
    ))]
    fn finished_reading(self) -> UResult<()>;
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).valid(),
        ensures crate::trusted_common::io::readable(&*result),
            crate::trusted_common::io::remaining(&*result) == old(self).bytes(),
            final(self).valid() == crate::trusted_common::io::readable(&*final(result)),
            final(self).bytes() == crate::trusted_common::io::remaining(&*final(result)),
    ))]
    fn as_read(&mut self) -> &mut Self::InnerRead;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct WriteablePlainTmpFile {
    pub(crate) path: TmpPath,
    pub(crate) file: BufWriter<File>,
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct ClosedPlainTmpFile {
    pub(crate) path: TmpPath,
    #[cfg(verus_keep_ghost)]
    pub(crate) stored: Tracked<crate::trusted::temporary::StoredFile>,
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct PlainTmpMergeInput {
    pub(crate) path: TmpPath,
    pub(crate) file: File,
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl WriteableTmpFile for WriteablePlainTmpFile {
    type Closed = ClosedPlainTmpFile;
    type InnerWrite = BufWriter<File>;

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn create(file: (File, TmpPath), compress_prog: Option<&str>,
        #[cfg(verus_keep_ghost)] log: Tracked<&crate::proof::OutputLog>,
    ) -> UResult<Self> {
        let (file, path) = file;
        let result = Self {
            #[cfg(not(verus_keep_ghost))]
            file: BufWriter::new(file),
            #[cfg(verus_keep_ghost)]
            file: crate::trusted::temporary::buffered(file, log),
            path,
        };
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::temporary::writer_facts(&result); }
        Ok(result)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn finished_writing(self,
        #[cfg(verus_keep_ghost)] log: Tracked<crate::proof::OutputLog>,
    ) -> UResult<Self::Closed> {
        #[cfg(not(verus_keep_ghost))]
        { Ok(ClosedPlainTmpFile { path: self.path }) }
        #[cfg(verus_keep_ghost)]
        {
            proof! {
                crate::proof::temporary::writer_facts(&self);
            }
            let (path, stored) = crate::trusted::temporary::close(self.file, self.path, log);
            let result = ClosedPlainTmpFile { path, stored };
            proof! { crate::proof::temporary::closed_facts(&result); }
            Ok(result)
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn as_write(&mut self) -> &mut Self::InnerWrite {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::temporary::writer_facts(self); crate::proof::temporary::writer_borrow_facts(); }
        &mut self.file
    }
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl ClosedTmpFile for ClosedPlainTmpFile {
    type Reopened = PlainTmpMergeInput;
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn reopen(self) -> UResult<Self::Reopened> {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::temporary::closed_facts(&self);
        }
        let result = PlainTmpMergeInput {
            #[cfg(not(verus_keep_ghost))]
            file: self
                .path
                .open()
                .map_err(|error| SortError::OpenTmpFileFailed { error })?,
            #[cfg(verus_keep_ghost)]
            file: verus_exec_expr! { crate::trusted::temporary::reopen(&self.path, Tracked(self.stored.borrow()))? },
            path: self.path,
        };
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::temporary::input_facts(&result); }
        Ok(result)
    }
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl MergeInput for PlainTmpMergeInput {
    type InnerRead = File;

    fn finished_reading(self) -> UResult<()> {
        // we ignore failures to delete the temporary file,
        // because there is a race at the end of the execution and the whole
        // temporary directory might already be gone.
        // Close the file first: removing it briefly takes another descriptor.
        #[cfg(not(verus_keep_ghost))]
        { drop(self.file); self.path.remove(); }
        #[cfg(verus_keep_ghost)]
        crate::trusted::temporary::remove(self.file, self.path);
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn as_read(&mut self) -> &mut Self::InnerRead {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proof::temporary::input_facts(self); crate::proof::temporary::input_borrow_facts(); }
        &mut self.file
    }
}

pub struct WriteableCompressedTmpFile {
    path: TmpPath,
    compress_prog: String,
    child: Child,
    child_stdin: BufWriter<ChildStdin>,
}
pub struct ClosedCompressedTmpFile {
    path: TmpPath,
    compress_prog: String,
}
pub struct CompressedTmpMergeInput {
    path: TmpPath,
    compress_prog: String,
    child: Child,
    child_stdout: ChildStdout,
}
impl WriteableTmpFile for WriteableCompressedTmpFile {
    type Closed = ClosedCompressedTmpFile;
    type InnerWrite = BufWriter<ChildStdin>;

    fn create((file, path): (File, TmpPath), compress_prog: Option<&str>,
        #[cfg(verus_keep_ghost)] _log: Tracked<&crate::proof::OutputLog>,
    ) -> UResult<Self> {
        let compress_prog = compress_prog.unwrap();
        let mut command = Command::new(compress_prog);
        command.stdin(Stdio::piped()).stdout(file);
        let mut child = command
            .spawn()
            .map_err(|err| SortError::CompressProgExecutionFailed {
                prog: compress_prog.to_owned(),
                error: err,
            })?;
        let child_stdin = child.stdin.take().unwrap();
        Ok(Self {
            path,
            compress_prog: compress_prog.to_owned(),
            child,
            child_stdin: BufWriter::new(child_stdin),
        })
    }

    fn finished_writing(self,
        #[cfg(verus_keep_ghost)] _log: Tracked<crate::proof::OutputLog>,
    ) -> UResult<Self::Closed> {
        drop(self.child_stdin);
        check_child_success(self.child, &self.compress_prog)?;
        Ok(ClosedCompressedTmpFile {
            path: self.path,
            compress_prog: self.compress_prog,
        })
    }

    fn as_write(&mut self) -> &mut Self::InnerWrite {
        &mut self.child_stdin
    }
}
impl ClosedTmpFile for ClosedCompressedTmpFile {
    type Reopened = CompressedTmpMergeInput;

    fn reopen(self) -> UResult<Self::Reopened> {
        let mut command = Command::new(&self.compress_prog);
        // mirroring what is done for ClosedPlainTmpFile
        let file = self
            .path
            .open()
            .map_err(|error| SortError::OpenTmpFileFailed { error })?;
        command.stdin(file).stdout(Stdio::piped()).arg("-d");
        let mut child = command
            .spawn()
            .map_err(|err| SortError::CompressProgExecutionFailed {
                prog: self.compress_prog.clone(),
                error: err,
            })?;
        let child_stdout = child.stdout.take().unwrap();
        Ok(CompressedTmpMergeInput {
            path: self.path,
            compress_prog: self.compress_prog,
            child,
            child_stdout,
        })
    }
}
impl MergeInput for CompressedTmpMergeInput {
    type InnerRead = ChildStdout;

    fn finished_reading(self) -> UResult<()> {
        // Explicitly close stdout before waiting on the child process.
        #[allow(clippy::drop_non_drop)]
        drop(self.child_stdout);
        check_child_success(self.child, &self.compress_prog)?;
        self.path.remove();
        Ok(())
    }

    fn as_read(&mut self) -> &mut Self::InnerRead {
        &mut self.child_stdout
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct PlainMergeInput<R: Read + Send> {
    pub(crate) inner: R,
}
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<R: Read + Send> MergeInput for PlainMergeInput<R> {
    type InnerRead = R;
    fn finished_reading(self) -> UResult<()> {
        Ok(())
    }
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    fn as_read(&mut self) -> &mut Self::InnerRead {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proof::temporary::plain_input_facts(self);
            crate::proof::temporary::plain_input_borrow_facts::<R>();
        }
        &mut self.inner
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    /// When the output file is also an input it is copied to a temporary file
    /// first. That copy must stay private to the owner: `fs::copy` would carry the
    /// source's 0644 over and undo what `next_file` created the file with.
    #[test]
    fn output_copy_keeps_the_tmp_file_private() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        fs::write(&out, b"a\n").unwrap();
        fs::set_permissions(&out, fs::Permissions::from_mode(0o644)).unwrap();

        let mut tmp_dir = TmpDirWrapper::new(dir.path().to_owned());
        let mut files = vec![out.clone().into_os_string()];
        replace_output_file_in_input_files(&mut files, Some(out.as_os_str()), &mut tmp_dir)
            .unwrap();

        let copy = Path::new(&files[0]);
        assert_ne!(copy, out, "the input was not replaced by a copy");
        assert_eq!(
            fs::metadata(copy).unwrap().permissions().mode() & 0o777,
            0o600
        );
        assert_eq!(fs::read(copy).unwrap(), b"a\n");
    }

    /// The copy of the output file is only read while it is the file sort
    /// created: once the temporary directory's path leads elsewhere, the file
    /// found at its name there is not read.
    #[test]
    #[cfg(not(target_os = "redox"))]
    fn output_copy_is_not_read_through_a_replaced_tmp_dir() {
        let dir = tempfile::tempdir().unwrap();
        let other = tempfile::tempdir().unwrap();
        fs::write(other.path().join("0"), b"other\n").unwrap();
        let out = dir.path().join("out");
        fs::write(&out, b"a\n").unwrap();

        let mut tmp_dir = TmpDirWrapper::new(dir.path().to_owned());
        let mut files = vec![out.clone().into_os_string()];
        let copy =
            replace_output_file_in_input_files(&mut files, Some(out.as_os_str()), &mut tmp_dir)
                .unwrap();
        let tmp = copy.as_ref().unwrap().path().parent().unwrap();
        fs::rename(tmp, dir.path().join("moved")).unwrap();
        std::os::unix::fs::symlink(other.path(), tmp).unwrap();

        assert!(open_input(&files[0], copy.as_ref()).is_err());
    }

    /// A temporary file that is being merged when the directory's path is made
    /// to lead elsewhere: removing it afterwards leaves the file of the same
    /// name there alone.
    #[test]
    #[cfg(not(target_os = "redox"))]
    fn finished_input_is_not_removed_through_a_replaced_tmp_dir() {
        let dir = tempfile::tempdir().unwrap();
        let other = tempfile::tempdir().unwrap();
        fs::write(other.path().join("0"), b"other\n").unwrap();

        let mut tmp_dir = TmpDirWrapper::new(dir.path().to_owned());
        let input = WriteablePlainTmpFile::create(tmp_dir.next_file().unwrap(), None)
            .unwrap()
            .finished_writing()
            .unwrap()
            .reopen()
            .unwrap();
        let tmp = input.path.path().parent().unwrap().to_owned();
        fs::rename(&tmp, dir.path().join("moved")).unwrap();
        std::os::unix::fs::symlink(other.path(), &tmp).unwrap();
        input.finished_reading().unwrap();

        assert_eq!(fs::read(other.path().join("0")).unwrap(), b"other\n");
    }
}
