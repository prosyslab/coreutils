// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::SortResult as UResult;
use crate::{
    GlobalSettings, Output, SortError,
    chunks::{self, Chunk, RecycledChunk},
    current_open_fd_count, fd_soft_limit, merge_compare, open,
    tmp_dir::{TmpDirWrapper, TmpPath},
};
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
fn open_input(file: &OsStr, copy: Option<&TmpPath>) -> UResult<crate::InputReader> {
    match copy {
        Some(copy) if Path::new(file) == copy.path() => Ok(crate::boxed_reader(
            copy.open()
                .map_err(|error| SortError::OpenTmpFileFailed { error })?,
        )),
        _ => open(file).map_err(Into::into),
    }
}
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
fn merge_batch<M, F: ExactSizeIterator<Item = UResult<M>>>(
    files: &mut F,
    count: usize,
) -> Vec<UResult<M>> {
    let count = count.min(files.len());
    let mut batch = Vec::new();
    for _ in 0..count {
        batch.push(files.next().unwrap());
    }
    batch
}
pub(crate) fn reopen_files<C: ClosedTmpFile + 'static>(
    files: Vec<C>,
) -> crate::trusted::exact_iteration::ExactIter<'static, UResult<C::Reopened>> {
    crate::trusted::exact_iteration::map(
        crate::trusted::joining::into_vec_iter(files),
        |file: C| -> UResult<C::Reopened> { file.reopen() },
    )
}
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
    if files.len() <= batch_size {
        let merger = merge_without_limit(files, settings);
        merger?.write_all(settings, output)
    } else {
        let mut temporary_files: Vec<Tmp::Closed> = vec![];
        while files.len() > 0 {
            let (new_file,) = crate::trusted::temporary::new_file(tmp_dir);
            let mut tmp_file = Tmp::create(
                new_file?,
                crate::trusted::temporary::optional_str(&settings.compress_prog),
            )?;
            let batch = merge_batch(&mut files, batch_size);
            let batch = crate::trusted::joining::into_vec_iter(batch);
            let merger = merge_without_limit(batch, settings)?;
            merger.write_all_to(settings, tmp_file.as_write(), || "write failed".into())?;
            temporary_files.push(tmp_file.finished_writing()?);
        }
        let files = reopen_files(temporary_files);
        merge_with_file_limit::<_, _, Tmp>(files, settings, output, tmp_dir)
    }
}
fn merge_without_limit<M: MergeInput + 'static, F: Iterator<Item = UResult<M>>>(
    files: F,
    settings: &GlobalSettings,
) -> UResult<FileMerger<'_>> {
    let (request_sender, request_receiver) = crate::trusted::concurrency::unbounded_channel();
    let separator = settings.line_ending.into();
    let mut reader_files = Vec::new();
    let mut loaded_receivers = Vec::new();
    for file in files {
        let file_number = reader_files.len();
        let file = crate::trusted::unwind::unwrap_result(file);
        let (sender, receiver) = crate::trusted::joining::chunk_channel();
        reader_files.push(Some(ReaderFile {
            file,
            sender,
            carry_over: Vec::new(),
        }));
        loaded_receivers.push(receiver);
        let request = (file_number, RecycledChunk::new(8 * 1024));
        crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send_unbounded(
            &request_sender,
            request,
        ));
    }
    for file_number in 0..reader_files.len() {
        let request = (file_number, RecycledChunk::new(8 * 1024));
        crate::trusted::unwind::unwrap_result(crate::trusted::concurrency::send_unbounded(
            &request_sender,
            request,
        ));
    }
    let (reader_join_handle,) = {
        let mut task_settings = crate::trusted::concurrency::clone_settings(settings);
        task_settings.precomputed.fast_locale_collation = false;
        let task = SourceReaderTask {
            recycled_receiver: request_receiver,
            files: reader_files,
            settings: task_settings,
            separator,
        };
        let result = crate::trusted::joining::launch_reader_projected(task);
        result
    };
    let mut mergeable_files: Vec<MergeableFile<'_>> = Vec::new();
    let mut file_number = 0;
    for receiver in loaded_receivers {
        let received = crate::trusted::concurrency::recv(&receiver);
        if let Ok(chunk) = received {
            let file = MergeableFile {
                current_chunk: Rc::new(chunk),
                file_number,
                line_idx: 0,
                receiver,
                settings,
            };
            mergeable_files.push(file);
        } else {
            crate::trusted::joining::reader_eof(&request_sender);
        }
        file_number += 1;
    }
    let heap = crate::trusted::merging::heap_from(mergeable_files);
    let merger = FileMerger {
        heap,
        request_sender,
        prev: None,
        reader_join_handle,
    };
    Ok(merger)
}
pub(crate) struct ReaderFile<M: MergeInput> {
    pub(crate) file: M,
    pub(crate) sender: SyncSender<Chunk>,
    pub(crate) carry_over: Vec<u8>,
}
fn read_reader_file<M: MergeInput>(
    entry: &mut ReaderFile<M>,
    recycled_chunk: RecycledChunk,
    settings: &GlobalSettings,
    separator: u8,
) -> UResult<bool> {
    let ReaderFile {
        file,
        sender,
        carry_over,
    } = entry;
    let input = file.as_read();
    let mut next_files = crate::trusted::joining::empty();
    let continued = chunks::read(
        sender,
        recycled_chunk,
        None,
        carry_over,
        input,
        &mut next_files,
        separator,
        settings,
    )?;
    Ok(continued)
}
fn reader<M: MergeInput>(
    recycled_receiver: &Receiver<(usize, RecycledChunk)>,
    files: &mut [Option<ReaderFile<M>>],
    settings: &GlobalSettings,
    separator: u8,
) -> UResult<()> {
    while let Ok((file_idx, recycled_chunk)) =
        { { crate::trusted::concurrency::recv(recycled_receiver) } }
    {
        if let Some(entry) = &mut files[file_idx] {
            let should_continue = read_reader_file(entry, recycled_chunk, settings, separator)?;
            if !should_continue {
                let ReaderFile { file, sender, .. } = files[file_idx].take().unwrap();
                crate::trusted::joining::close_chunk_sender(sender);
                file.finished_reading()?;
            }
        }
    }
    Ok(())
}
pub(crate) struct SourceReaderTask<M: MergeInput + 'static> {
    pub(crate) recycled_receiver: Receiver<(usize, RecycledChunk)>,
    pub(crate) files: Vec<Option<ReaderFile<M>>>,
    pub(crate) settings: GlobalSettings,
    pub(crate) separator: u8,
}
impl<M: MergeInput + 'static> crate::proof::joining::Task for SourceReaderTask<M> {
    type Output = crate::proof::joining::ReaderOutput;
    fn run(self) -> Self::Output {
        let mut task = self;
        let result = reader(
            &task.recycled_receiver,
            task.files.as_mut_slice(),
            &task.settings,
            task.separator,
        );
        (result,)
    }
}
pub struct MergeableFile<'a> {
    pub(crate) current_chunk: Rc<Chunk>,
    pub(crate) line_idx: usize,
    pub(crate) receiver: Receiver<Chunk>,
    pub(crate) file_number: usize,
    pub(crate) settings: &'a GlobalSettings,
}
macro_rules! delegate_ord {
    ($ life : lifetime , $ ty : ty , $ helper : ident , $ contract : ident , $ facts : ident) => {
        impl<$life> PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.cmp(other) == Ordering::Equal
            }
        }
        impl<$life> Eq for $ty {}
        impl<$life> PartialOrd for $ty {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl<$life> Ord for $ty {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                $helper(self, other)
            }
        }
    };
}
delegate_ord ! ('a , MergeableFile <'a >, compare_files , file_ord_contract , file_ord_facts);
pub(crate) fn compare_files(a: &MergeableFile<'_>, b: &MergeableFile<'_>) -> Ordering {
    let mut cmp = merge_compare(
        &a.current_chunk.lines()[a.line_idx],
        &b.current_chunk.lines()[b.line_idx],
        a.settings,
        a.current_chunk.line_data(),
        b.current_chunk.line_data(),
    );
    if cmp == Ordering::Equal {
        cmp = a.file_number.cmp(&b.file_number);
    }
    cmp.reverse()
}
pub(crate) struct PreviousLine {
    pub(crate) chunk: Rc<Chunk>,
    pub(crate) line_idx: usize,
    pub(crate) file_number: usize,
}
pub(crate) struct FileMerger<'a> {
    pub(crate) heap: BinaryHeap<MergeableFile<'a>>,
    pub(crate) request_sender: Sender<(usize, RecycledChunk)>,
    pub(crate) prev: Option<PreviousLine>,
    pub(crate) reader_join_handle: JoinHandle<UResult<()>>,
}
fn write_merge_line(
    contents: &chunks::ChunkContents<'_>,
    file: &MergeableFile<'_>,
    previous: &Option<PreviousLine>,
    writer: &mut impl Write,
    settings: &GlobalSettings,
) -> io::Result<()> {
    let current_line = &contents.lines[file.line_idx];
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
    current_line.write(writer, settings)
}
fn advance_merge_file(file: &mut MergeableFile<'_>, next_chunk: Chunk) {
    file.current_chunk = Rc::new(next_chunk);
    file.line_idx = 0;
}
fn advance_merge_cursor(file: &mut MergeableFile<'_>) {
    file.line_idx += 1;
}
impl FileMerger<'_> {
    fn write_all(self, settings: &GlobalSettings, output: Output) -> UResult<()> {
        let ctx = || String::new();
        let mut out = crate::trusted::output_writer(output)?;
        self.write_all_to(settings, &mut out, &ctx)?;
        {
            crate::trusted::flush_output(&mut out)?;
            Ok(())
        }
    }
    fn write_all_to(
        self,
        settings: &GlobalSettings,
        out: &mut impl Write,
        ctx: impl FnOnce() -> String,
    ) -> UResult<()> {
        let mut this = self;
        let mut write_result = Ok(());
        loop {
            let next = this.write_next(out, settings);
            match next {
                Ok(true) => (),
                Ok(false) => break,
                Err(error) => {
                    write_result = Err(error);
                    break;
                }
            }
        }
        let Self {
            heap,
            request_sender,
            reader_join_handle,
            ..
        } = this;
        crate::trusted::merging::drop_sender(request_sender);
        let files = crate::trusted::merging::heap_into_vec(heap);
        let reader_result = crate::trusted::joining::join_or_unwind(reader_join_handle);
        { reader_result }
    }
    fn write_next(
        &mut self,
        writer: &mut impl Write,
        settings: &GlobalSettings,
    ) -> io::Result<bool> {
        let selected = crate::trusted::merging::heap_peek(&self.heap);
        if let Some(file) = selected {
            let previous_chunk = crate::trusted::merging::rc_clone(&file.current_chunk);
            let prev = self.prev.replace(PreviousLine {
                chunk: previous_chunk,
                line_idx: file.line_idx,
                file_number: file.file_number,
            });
            {
                let contents = file.current_chunk.borrow_dependent();
                write_merge_line(contents, file, &prev, writer, settings)?;
            }
            let was_last_line_for_file = file.current_chunk.lines().len() == file.line_idx + 1;
            if was_last_line_for_file {
                let received = {
                    let result = crate::trusted::concurrency::recv(&file.receiver);
                    result
                };
                if let Ok(next_chunk) = received {
                    {
                        let update = |entry: &mut MergeableFile| {
                            advance_merge_file(entry, next_chunk);
                        };
                        let next_file =
                            crate::trusted::merging::heap_update_top(&mut self.heap, update);
                    }
                } else {
                    crate::trusted::joining::reader_eof(&self.request_sender);
                    {
                        crate::trusted::merging::heap_pop(&mut self.heap);
                    }
                }
            } else {
                {
                    let update = |entry: &mut MergeableFile| {
                        advance_merge_cursor(entry);
                    };
                    let next_file =
                        crate::trusted::merging::heap_update_top(&mut self.heap, update);
                }
            }
            if let Some(prev) = prev {
                if let Ok(prev_chunk) = Rc::try_unwrap(prev.chunk) {
                    {
                        let request = (prev.file_number, prev_chunk.recycle());
                        crate::trusted::concurrency::send_unbounded(&self.request_sender, request)
                            .ok();
                    }
                }
            }
        }
        { Ok(!crate::trusted::merging::heap_empty(&self.heap)) }
    }
}
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
pub trait WriteableTmpFile: Sized {
    type Closed: ClosedTmpFile;
    type InnerWrite: Write;
    fn create(file: (File, TmpPath), compress_prog: Option<&str>) -> UResult<Self>;
    fn finished_writing(self) -> UResult<Self::Closed>;
    fn as_write(&mut self) -> &mut Self::InnerWrite;
}
pub trait ClosedTmpFile {
    type Reopened: MergeInput;
    fn reopen(self) -> UResult<Self::Reopened>;
}
pub trait MergeInput: Send {
    type InnerRead: Read;
    fn finished_reading(self) -> UResult<()>;
    fn as_read(&mut self) -> &mut Self::InnerRead;
}
pub struct WriteablePlainTmpFile {
    pub(crate) path: TmpPath,
    pub(crate) file: BufWriter<File>,
}
pub struct ClosedPlainTmpFile {
    pub(crate) path: TmpPath,
}
pub struct PlainTmpMergeInput {
    pub(crate) path: TmpPath,
    pub(crate) file: File,
}
impl WriteableTmpFile for WriteablePlainTmpFile {
    type Closed = ClosedPlainTmpFile;
    type InnerWrite = BufWriter<File>;
    fn create(file: (File, TmpPath), compress_prog: Option<&str>) -> UResult<Self> {
        let (file, path) = file;
        let result = Self {
            file: crate::trusted::temporary::buffered(file),
            path,
        };
        Ok(result)
    }
    fn finished_writing(self) -> UResult<Self::Closed> {
        {
            let (path,) = crate::trusted::temporary::close(self.file, self.path);
            let result = ClosedPlainTmpFile { path };
            Ok(result)
        }
    }
    fn as_write(&mut self) -> &mut Self::InnerWrite {
        &mut self.file
    }
}
impl ClosedTmpFile for ClosedPlainTmpFile {
    type Reopened = PlainTmpMergeInput;
    fn reopen(self) -> UResult<Self::Reopened> {
        let result = PlainTmpMergeInput {
            file: crate::trusted::temporary::reopen(&self.path)?,
            path: self.path,
        };
        Ok(result)
    }
}
impl MergeInput for PlainTmpMergeInput {
    type InnerRead = File;
    fn finished_reading(self) -> UResult<()> {
        crate::trusted::temporary::remove(self.file, self.path);
        Ok(())
    }
    fn as_read(&mut self) -> &mut Self::InnerRead {
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
    fn create((file, path): (File, TmpPath), compress_prog: Option<&str>) -> UResult<Self> {
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
    fn finished_writing(self) -> UResult<Self::Closed> {
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
pub struct PlainMergeInput<R: Read + Send> {
    pub(crate) inner: R,
}
impl<R: Read + Send> MergeInput for PlainMergeInput<R> {
    type InnerRead = R;
    fn finished_reading(self) -> UResult<()> {
        Ok(())
    }
    fn as_read(&mut self) -> &mut Self::InnerRead {
        &mut self.inner
    }
}
