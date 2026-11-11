pub use crate::trusted_common::{split_inclusive, strip_suffix};
use bigdecimal::BigDecimal;
use rayon::prelude::*;
use std::cmp::Ordering;
pub mod comparisons {
    use std::cmp::Ordering;
    pub trait MonthInitializer {
        fn initialize(&self) -> Option<crate::MonthTable>;
    }
    pub fn cached_none_months<I: MonthInitializer>(
        initialize: I,
    ) -> Option<&'static crate::MonthTable> {
        static CACHE: std::sync::OnceLock<Option<crate::MonthTable>> = std::sync::OnceLock::new();
        CACHE.get_or_init(|| initialize.initialize()).as_ref()
    }
    pub fn month_pairs(
        names: &[Vec<u8>; 12],
        months: &[crate::Month; 12],
    ) -> Vec<(Vec<u8>, crate::Month)> {
        names
            .iter()
            .zip(months.iter())
            .map(|(name, &month)| (name.clone(), month))
            .collect()
    }
    pub fn upper_prefix(input: &[u8], len: usize) -> Option<Vec<u8>> {
        input.get(..len).map(<[u8]>::to_ascii_uppercase)
    }
    pub fn equal_bytes(a: &[u8], b: &[u8]) -> bool {
        a == b
    }
    pub fn equal_vec_array<const N: usize>(a: &Vec<u8>, b: &[u8; N]) -> bool {
        a.as_slice() == b
    }
    pub fn cmp_month(a: &crate::Month, b: &crate::Month) -> Ordering {
        a.cmp(b)
    }
    pub fn float_partial_cmp(a: &f64, b: &f64) -> Option<Ordering> {
        a.partial_cmp(b)
    }
    pub fn cmp_u8(a: u8, b: u8) -> Ordering {
        a.cmp(&b)
    }
    pub fn cmp_i64(a: i64, b: i64) -> Ordering {
        a.cmp(&b)
    }
    pub fn cmp_usize(a: usize, b: usize) -> Ordering {
        a.cmp(&b)
    }
    pub trait BytePredicate {
        fn test(&self, byte: u8) -> bool;
    }
    pub fn slice_len<T>(input: &[T]) -> usize {
        input.len()
    }
    pub fn slice_at<T>(input: &[T], index: usize) -> &T {
        &input[index]
    }
    pub fn slice_from<T>(input: &[T], index: usize) -> &[T] {
        &input[index..]
    }
    pub fn vec_at<T>(input: &Vec<T>, index: usize) -> &T {
        &input[index]
    }
    pub fn vec_get<T>(input: &Vec<T>, index: usize) -> Option<&T> {
        input.get(index)
    }
    pub struct SliceRefs<'a, T> {
        inner: std::slice::Iter<'a, T>,
    }
    impl<'a, T> SliceRefs<'a, T> {
        pub fn next(&mut self) -> Option<&'a T> {
            self.inner.next()
        }
    }
    pub fn slice_refs<T>(input: &[T]) -> SliceRefs<'_, T> {
        SliceRefs {
            inner: input.iter(),
        }
    }
    pub fn vec_refs<T>(input: &Vec<T>) -> SliceRefs<'_, T> {
        SliceRefs {
            inner: input.iter(),
        }
    }
    pub fn derived_general_cmp(
        a: &crate::GeneralBigDecimalParseResult,
        b: &crate::GeneralBigDecimalParseResult,
    ) -> Option<Ordering> {
        a.partial_cmp(b)
    }
    pub fn unwrap_order(input: Option<Ordering>) -> Ordering {
        input.unwrap()
    }
    pub fn utf8(input: &[u8]) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(input)
    }
    pub fn replace_decimal(input: &[u8], point: u8) -> Option<Vec<u8>> {
        (point != b'.').then(|| {
            input
                .iter()
                .map(|&byte| if byte == point { b'.' } else { byte })
                .collect()
        })
    }
    pub fn trim_ascii_start(input: &[u8]) -> &[u8] {
        input.trim_ascii_start()
    }
    pub fn equal_folded(a: &[u8], b: &[u8]) -> bool {
        a.eq_ignore_ascii_case(b)
    }
    pub fn starts_folded(input: &[u8], prefix: &[u8]) -> bool {
        input
            .get(..prefix.len())
            .is_some_and(|part| part.eq_ignore_ascii_case(prefix))
    }
    pub struct IndexedPeek<'a> {
        inner: itertools::PeekNth<std::iter::Enumerate<std::slice::Iter<'a, u8>>>,
    }
    impl<'a> IndexedPeek<'a> {
        pub fn next(&mut self) -> Option<(usize, &'a u8)> {
            self.inner.next()
        }
        pub fn peek(&mut self) -> Option<&(usize, &'a u8)> {
            self.inner.peek()
        }
        pub fn peek_nth(&mut self, n: usize) -> Option<&(usize, &'a u8)> {
            self.inner.peek_nth(n)
        }
    }
    pub fn indexed_peek(input: &[u8]) -> IndexedPeek<'_> {
        IndexedPeek {
            inner: itertools::peek_nth(input.iter().enumerate()),
        }
    }
    pub struct DigitBytes<'a> {
        inner: std::iter::Filter<std::iter::Copied<std::slice::Iter<'a, u8>>, fn(&u8) -> bool>,
    }
    impl<'a> DigitBytes<'a> {
        pub fn next(&mut self) -> Option<u8> {
            self.inner.next()
        }
        pub fn all_zero(&mut self) -> bool {
            self.inner.all(|byte| byte == b'0')
        }
    }
    pub fn digit_bytes(input: &[u8]) -> DigitBytes<'_> {
        DigitBytes {
            inner: input.iter().copied().filter(u8::is_ascii_digit),
        }
    }
    pub fn last_byte(input: &[u8]) -> Option<u8> {
        input.iter().next_back().copied()
    }
}
pub struct Reader {
    inner: Box<dyn std::io::Read + Send>,
}
#[derive(Debug)]
pub struct IoFailure {
    inner: Box<dyn uucore::error::UError>,
}
impl From<std::io::Error> for IoFailure {
    fn from(error: std::io::Error) -> Self {
        Self {
            inner: error.into(),
        }
    }
}
impl From<crate::SortError> for IoFailure {
    fn from(error: crate::SortError) -> Self {
        Self {
            inner: error.into(),
        }
    }
}
pub fn memory_readers(inputs: &[Vec<u8>]) -> Vec<crate::SortResult<crate::InputReader>> {
    inputs
        .iter()
        .map(|input| Ok(crate::boxed_reader(std::io::Cursor::new(input.clone()))))
        .collect()
}
pub fn bounded_bytes(input: &[u8]) -> &[u8] {
    input
}
pub fn descriptor_limit() -> Option<usize> {
    crate::fd_soft_limit()
}
pub struct Capture {
    file: std::fs::File,
}
pub struct ZippedBytes<'a> {
    inner: std::iter::Zip<
        std::iter::Copied<std::slice::Iter<'a, u8>>,
        std::iter::Copied<std::slice::Iter<'a, u8>>,
    >,
}
impl<'a> Iterator for ZippedBytes<'a> {
    type Item = (u8, u8);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}
pub fn zip_bytes<'a>(a: &'a [u8], b: &'a [u8]) -> ZippedBytes<'a> {
    ZippedBytes {
        inner: a.iter().copied().zip(b.iter().copied()),
    }
}
pub struct FilteredBytes<'a, P: comparisons::BytePredicate> {
    inner: std::iter::Filter<std::slice::Iter<'a, u8>, Box<dyn FnMut(&&'a u8) -> bool + 'a>>,
    marker: std::marker::PhantomData<P>,
}
impl<'a, P: comparisons::BytePredicate> FilteredBytes<'a, P> {
    pub fn next(&mut self) -> Option<&'a u8> {
        self.inner.next()
    }
}
pub fn filter_bytes<'a, P: comparisons::BytePredicate + 'a>(
    input: &'a [u8],
    predicate: P,
) -> FilteredBytes<'a, P> {
    FilteredBytes {
        inner: input
            .iter()
            .filter(Box::new(move |byte| predicate.test(**byte))),
        marker: std::marker::PhantomData,
    }
}
pub fn compare_byte_slices(a: &[u8], b: &[u8]) -> Ordering {
    a.cmp(b)
}
pub enum ParsedNumber {
    Invalid,
    Nan,
    NegativeInfinity,
    Finite(BigDecimal),
    Infinity,
}
pub fn parse_number(input: &[u8]) -> ParsedNumber {
    use uucore::extendedbigdecimal::ExtendedBigDecimal as Number;
    use uucore::parser::num_parser::{ExtendedParser, ExtendedParserError as Error};
    let Ok(text) = std::str::from_utf8(input) else {
        return ParsedNumber::Invalid;
    };
    let number = match Number::extended_parse(text) {
        Ok(value)
        | Err(Error::PartialMatch(value, _) | Error::Overflow(value) | Error::Underflow(value)) => {
            value
        }
        Err(Error::NotNumeric) => return ParsedNumber::Invalid,
    };
    match number {
        Number::Nan | Number::MinusNan => ParsedNumber::Nan,
        Number::MinusInfinity => ParsedNumber::NegativeInfinity,
        Number::BigDecimal(value) => ParsedNumber::Finite(value),
        Number::MinusZero => ParsedNumber::Finite(0.into()),
        Number::Infinity => ParsedNumber::Infinity,
    }
}
pub fn compare_decimals(a: &BigDecimal, b: &BigDecimal) -> Ordering {
    a.cmp(b)
}
pub fn hash_bytes(input: &[u8], salt: &[u8; 16]) -> u64 {
    use foldhash::{SharedSeed, fast::FoldHasher};
    use std::hash::{Hash, Hasher};
    let mut hasher = FoldHasher::with_seed(0, SharedSeed::global_fixed());
    (input, salt.as_slice()).hash(&mut hasher);
    hasher.finish()
}
pub fn sort_lines<F: Fn(&Vec<u8>, &Vec<u8>) -> Ordering + Sync>(
    lines: &mut Vec<Vec<u8>>,
    stable: bool,
    compare: F,
) {
    if stable {
        lines.par_sort_by(compare);
    } else {
        lines.par_sort_unstable_by(compare);
    }
}
pub fn join(lines: &[Vec<u8>], separator: &[u8]) -> Vec<u8> {
    lines.join(separator)
}
pub fn begin_capture() -> (Capture, crate::Output, crate::tmp_dir::TmpDirWrapper) {
    let file = tempfile::tempfile().unwrap();
    let output = crate::Output {
        file: Some(("sort-capture".into(), file.try_clone().unwrap())),
    };
    let directory = crate::tmp_dir::TmpDirWrapper::new(std::env::temp_dir());
    (Capture { file }, output, directory)
}
pub fn finish_capture(mut capture: Capture) -> Vec<u8> {
    use std::io::{Read, Seek};
    capture.file.rewind().unwrap();
    let mut bytes = Vec::new();
    capture.file.read_to_end(&mut bytes).unwrap();
    bytes
}
pub fn output_writer(
    output: crate::Output,
) -> crate::SortResult<std::io::BufWriter<Box<dyn std::io::Write>>> {
    output.into_write().map_err(Into::into)
}
pub fn write_output<W: std::io::Write>(writer: &mut W, bytes: &[u8]) -> std::io::Result<()> {
    writer.write_all(bytes)
}
pub fn flush_output<W: std::io::Write>(writer: &mut W) -> std::io::Result<()> {
    writer.flush()
}
pub mod input {
    pub fn separator_positions(ending: u8, bytes: &[u8]) -> Vec<usize> {
        memchr::memchr_iter(ending, bytes).collect()
    }
    pub fn copy_prefix(buffer: &mut Vec<u8>, prefix: &[u8]) {
        buffer[..prefix.len()].copy_from_slice(prefix)
    }
    pub fn read_buffer<R: std::io::Read>(
        reader: &mut R,
        buffer: &mut Vec<u8>,
        start: usize,
    ) -> std::io::Result<usize> {
        reader.read(&mut buffer[start..])
    }
}
pub mod temporary {
    use crate::tmp_dir::{TmpDirWrapper, TmpPath};
    use std::fs::File;
    use std::io::BufWriter;
    pub fn optional_str(value: &Option<String>) -> Option<&str> {
        value.as_deref()
    }
    pub fn new_file(directory: &mut TmpDirWrapper) -> (crate::SortResult<(File, TmpPath)>,) {
        (directory.next_file().map_err(Into::into),)
    }
    pub fn buffered(file: File) -> BufWriter<File> {
        BufWriter::new(file)
    }
    pub fn close(writer: BufWriter<File>, path: TmpPath) -> (TmpPath,) {
        drop(writer);
        (path,)
    }
    pub fn reopen(path: &TmpPath) -> crate::SortResult<File> {
        path.open()
            .map_err(|error| crate::SortError::OpenTmpFileFailed { error }.into())
    }
    pub fn remove(file: File, path: TmpPath) {
        drop(file);
        path.remove();
    }
}
pub mod exact_iteration {
    pub struct ExactIter<'a, T: 'a> {
        inner: Box<dyn ExactSizeIterator<Item = T> + 'a>,
    }
    impl<'a, T: 'a> Iterator for ExactIter<'a, T> {
        type Item = T;
        fn next(&mut self) -> Option<T> {
            self.inner.next()
        }
    }
    impl<'a, T: 'a> ExactSizeIterator for ExactIter<'a, T> {
        fn len(&self) -> usize {
            self.inner.len()
        }
    }
    pub fn map<'a, I: ExactSizeIterator + 'a, U: 'a, F: Fn(I::Item) -> U + 'a>(
        input: I,
        function: F,
    ) -> ExactIter<'a, U> {
        ExactIter {
            inner: Box::new(input.map(function)),
        }
    }
}
pub mod joining {
    use crate::proof::joining::Task;
    use std::thread::JoinHandle;
    pub struct Empty<T> {
        inner: std::iter::Empty<T>,
    }
    impl<T> Iterator for Empty<T> {
        type Item = T;
        fn next(&mut self) -> Option<T> {
            self.inner.next()
        }
    }
    pub fn empty<T>() -> Empty<T> {
        Empty {
            inner: std::iter::empty(),
        }
    }
    pub fn into_vec_iter<T>(values: Vec<T>) -> std::vec::IntoIter<T> {
        values.into_iter()
    }
    pub fn spawn<T: Task>(task: T) -> (JoinHandle<T::Output>,) {
        (std::thread::spawn(move || task.run()),)
    }
    pub fn spawn_first<A: Send + 'static, T: Task<Output = (A,)>>(task: T) -> (JoinHandle<A>,) {
        let handle = std::thread::spawn(move || task.run().0);
        (handle,)
    }
    pub fn join_or_unwind<O>(handle: JoinHandle<O>) -> O {
        handle.join().unwrap()
    }
    pub fn close_chunk_sender(sender: std::sync::mpsc::SyncSender<crate::chunks::Chunk>) {
        drop(sender)
    }
    pub(crate) fn chunk_channel() -> (
        std::sync::mpsc::SyncSender<crate::chunks::Chunk>,
        std::sync::mpsc::Receiver<crate::chunks::Chunk>,
    ) {
        let (sender, receiver) = std::sync::mpsc::sync_channel(2);
        (sender, receiver)
    }
    pub(crate) fn launch_reader<M: crate::merge::MergeInput + 'static>(
        task: crate::merge::SourceReaderTask<M>,
    ) -> (JoinHandle<crate::proof::joining::ReaderOutput>,) {
        let (handle,) = spawn(task);
        (handle,)
    }
    pub(crate) fn launch_reader_projected<M: crate::merge::MergeInput + 'static>(
        task: crate::merge::SourceReaderTask<M>,
    ) -> (JoinHandle<crate::SortResult<()>>,) {
        let (handle,) = spawn_first(task);
        (handle,)
    }
    pub(crate) fn reader_eof(
        request_owner: &std::sync::mpsc::Sender<(usize, crate::chunks::RecycledChunk)>,
    ) {
    }
}
pub mod unwind {
    use super::ownership;
    use crate::chunks::Chunk;
    use crate::proof::unwind::{Comparator, ContentsMutator};
    use rayon::prelude::*;
    pub fn unwrap_result<T, E: std::fmt::Debug>(result: Result<T, E>) -> T {
        result.unwrap()
    }
    pub fn initialize_rayon() -> usize {
        rayon::current_num_threads()
    }
    pub fn sort_values<T: Send, C: Comparator<T> + Sync>(
        values: &mut Vec<T>,
        stable: bool,
        compare: &C,
    ) {
        if stable {
            values.par_sort_by(|a, b| compare.compare(a, b));
        } else {
            values.par_sort_unstable_by(|a, b| compare.compare(a, b));
        }
    }
    pub fn with_dependent_mut<M: ContentsMutator>(chunk: &mut Chunk, mutate: &M) -> M::Output {
        chunk.with_dependent_mut(|owner, contents| mutate.run(owner, contents))
    }
}
pub mod iteration {
    use itertools::Itertools;
    pub struct Iter<'a, T: 'a> {
        inner: Box<dyn Iterator<Item = T> + 'a>,
    }
    impl<'a, T: 'a> Iterator for Iter<'a, T> {
        type Item = T;
        fn next(&mut self) -> Option<T> {
            self.inner.next()
        }
    }
    pub fn slice<'a, T: 'a>(input: &'a [T]) -> Iter<'a, &'a T> {
        Iter {
            inner: Box::new(input.iter()),
        }
    }
    pub fn empty<'a, T: 'a>() -> Iter<'a, T> {
        Iter {
            inner: Box::new(std::iter::empty()),
        }
    }
    pub fn map<'a, T: 'a, U: 'a, F: Fn(T) -> U + 'a>(
        input: Iter<'a, T>,
        function: F,
    ) -> Iter<'a, U> {
        Iter {
            inner: Box::new(input.inner.map(function)),
        }
    }
    pub fn dedup_by<'a, T: 'a, F: Fn(&T, &T) -> bool + 'a>(
        input: Iter<'a, T>,
        predicate: F,
    ) -> Iter<'a, T> {
        Iter {
            inner: Box::new(input.inner.dedup_by(predicate)),
        }
    }
    pub fn merge_by<'a, T: 'a, F: Fn(&T, &T) -> bool + 'a>(
        left: Iter<'a, T>,
        right: Iter<'a, T>,
        predicate: F,
    ) -> Iter<'a, T> {
        Iter {
            inner: Box::new(left.inner.merge_by(right.inner, predicate)),
        }
    }
}
pub mod concurrency {
    pub fn channel<T>(
        bound: usize,
    ) -> (std::sync::mpsc::SyncSender<T>, std::sync::mpsc::Receiver<T>) {
        let (sender, receiver) = std::sync::mpsc::sync_channel(bound);
        (sender, receiver)
    }
    pub fn send<T>(
        sender: &std::sync::mpsc::SyncSender<T>,
        value: T,
    ) -> Result<(), std::sync::mpsc::SendError<T>> {
        sender.send(value)
    }
    pub fn unbounded_channel<T>() -> (std::sync::mpsc::Sender<T>, std::sync::mpsc::Receiver<T>) {
        let (sender, receiver) = std::sync::mpsc::channel();
        (sender, receiver)
    }
    pub fn send_unbounded<T>(
        sender: &std::sync::mpsc::Sender<T>,
        value: T,
    ) -> Result<(), std::sync::mpsc::SendError<T>> {
        sender.send(value)
    }
    pub fn recv<T>(
        receiver: &std::sync::mpsc::Receiver<T>,
    ) -> Result<T, std::sync::mpsc::RecvError> {
        receiver.recv()
    }
    pub fn clone_settings(settings: &crate::GlobalSettings) -> crate::GlobalSettings {
        settings.clone()
    }
    pub trait PipeTask<I, O>: Send {
        fn run(
            &self,
            receiver: &std::sync::mpsc::Receiver<I>,
            sender: &std::sync::mpsc::SyncSender<O>,
        );
    }
    pub struct PendingProducer<I, O, P: PipeTask<I, O>> {
        sender: std::sync::mpsc::SyncSender<I>,
        marker: std::marker::PhantomData<(O, P)>,
    }
    pub struct PipeConsumer<I, O, P: PipeTask<I, O>> {
        receiver: std::sync::mpsc::Receiver<O>,
        marker: std::marker::PhantomData<(I, P)>,
    }
    pub struct PipeProducer<'a, I, O, P: PipeTask<I, O>> {
        sender: std::sync::mpsc::SyncSender<I>,
        consumer: &'a PipeConsumer<I, O, P>,
    }
    impl<'a>
        PipeProducer<'a, crate::chunks::Chunk, crate::chunks::Chunk, crate::ext_sort::SortPipeTask>
    {
        pub fn sender(&self) -> &std::sync::mpsc::SyncSender<crate::chunks::Chunk> {
            &self.sender
        }
        pub fn close(self) {
            drop(self);
        }
        pub fn reject_eof(&self) {}
    }
    impl<I, O, P: PipeTask<I, O>> PipeConsumer<I, O, P> {
        pub fn receiver(&self) -> &std::sync::mpsc::Receiver<O> {
            &self.receiver
        }
    }
    impl PipeConsumer<crate::chunks::Chunk, crate::chunks::Chunk, crate::ext_sort::SortPipeTask> {
        pub fn completed(&self) {}
    }
    pub fn bind_producer<'a>(
        pending: PendingProducer<
            crate::chunks::Chunk,
            crate::chunks::Chunk,
            crate::ext_sort::SortPipeTask,
        >,
        consumer: &'a PipeConsumer<
            crate::chunks::Chunk,
            crate::chunks::Chunk,
            crate::ext_sort::SortPipeTask,
        >,
    ) -> PipeProducer<'a, crate::chunks::Chunk, crate::chunks::Chunk, crate::ext_sort::SortPipeTask>
    {
        PipeProducer {
            sender: pending.sender,
            consumer,
        }
    }
    pub fn launch_pipe(
        input_sender: std::sync::mpsc::SyncSender<crate::chunks::Chunk>,
        input_receiver: std::sync::mpsc::Receiver<crate::chunks::Chunk>,
        output_sender: std::sync::mpsc::SyncSender<crate::chunks::Chunk>,
        output_receiver: std::sync::mpsc::Receiver<crate::chunks::Chunk>,
        task: crate::ext_sort::SortPipeTask,
    ) -> (
        PendingProducer<crate::chunks::Chunk, crate::chunks::Chunk, crate::ext_sort::SortPipeTask>,
        PipeConsumer<crate::chunks::Chunk, crate::chunks::Chunk, crate::ext_sort::SortPipeTask>,
    ) {
        std::thread::spawn(move || {
            task.run(&input_receiver, &output_sender);
        });
        (
            PendingProducer {
                sender: input_sender,
                marker: std::marker::PhantomData,
            },
            PipeConsumer {
                receiver: output_receiver,
                marker: std::marker::PhantomData,
            },
        )
    }
}
pub mod keys {
    pub fn enumerate_bytes(input: &[u8]) -> Vec<(usize, &u8)> {
        input.iter().enumerate().collect()
    }
    pub fn filter_indices<F: Fn(u8) -> bool>(input: &[u8], predicate: F) -> Vec<usize> {
        input
            .iter()
            .enumerate()
            .filter_map(|(i, &byte)| if predicate(byte) { Some(i) } else { None })
            .collect()
    }
    pub fn find_index<F: Fn(&u8) -> bool>(input: &[u8], predicate: F) -> usize {
        input
            .iter()
            .enumerate()
            .find(|(_, byte)| predicate(*byte))
            .map_or(input.len(), |(i, _)| i)
    }
    pub fn nth_index(input: &[u8], index: usize) -> usize {
        input
            .iter()
            .enumerate()
            .nth(index)
            .map_or(input.len(), |(i, _)| i)
    }
}
pub mod configuration {
    pub fn count<T, F: Fn(&T) -> bool>(input: &[T], predicate: F) -> usize {
        input.iter().filter(|item| predicate(*item)).count()
    }
    pub fn any<T, F: Fn(&T) -> bool>(input: &[T], predicate: F) -> bool {
        input.iter().any(predicate)
    }
}
pub mod parsing {
    pub struct EnumeratedBytes<'a> {
        inner: std::iter::Enumerate<std::slice::Iter<'a, u8>>,
    }
    pub fn enumerate(input: &[u8]) -> EnumeratedBytes<'_> {
        EnumeratedBytes {
            inner: input.iter().enumerate(),
        }
    }
    impl<'a> EnumeratedBytes<'a> {
        pub fn next(&mut self) -> Option<(usize, &'a u8)> {
            self.inner.next()
        }
    }
}
pub mod ownership {
    use crate::chunks::{Chunk, ChunkContents};
    pub fn cast_empty_lines<'a, 'b>(lines: Vec<crate::Line<'a>>) -> Vec<crate::Line<'b>> {
        unsafe { std::mem::transmute(lines) }
    }
    pub fn cast_empty_selections<'a, 'b>(selections: Vec<&'a [u8]>) -> Vec<&'b [u8]> {
        unsafe { std::mem::transmute(selections) }
    }
}
impl Reader {
    pub fn new<R: std::io::Read + Send + 'static>(reader: R) -> Self {
        Self {
            inner: Box::new(reader),
        }
    }
}
impl std::io::Read for Reader {
    fn read(&mut self, bytes: &mut [u8]) -> std::io::Result<usize> {
        self.inner.read(bytes)
    }
}
impl std::fmt::Display for IoFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.inner, formatter)
    }
}
impl std::error::Error for IoFailure {}
impl uucore::error::UError for IoFailure {
    fn code(&self) -> i32 {
        self.inner.code()
    }
}
impl From<Box<dyn uucore::error::UError>> for IoFailure {
    fn from(inner: Box<dyn uucore::error::UError>) -> Self {
        Self { inner }
    }
}
pub mod sorting {
    use rayon::prelude::*;
    use std::cmp::Ordering;
    pub struct MappedSlice<'a, T: 'a, U, F: Fn(&'a T) -> U> {
        inner: std::iter::Map<std::slice::Iter<'a, T>, F>,
    }
    impl<'a, T: 'a, U, F: Fn(&'a T) -> U> Iterator for MappedSlice<'a, T, U, F> {
        type Item = U;
        fn next(&mut self) -> Option<U> {
            self.inner.next()
        }
    }
    pub fn map_slice<'a, T: 'a, U, F: Fn(&'a T) -> U>(
        input: &'a [T],
        map: F,
    ) -> MappedSlice<'a, T, U, F> {
        MappedSlice {
            inner: input.iter().map(map),
        }
    }
    pub fn locale_decimal_bytes() -> &'static [u8] {
        uucore::i18n::decimal::locale_decimal_separator().as_bytes()
    }
    pub fn any_ascii_alpha(input: &[u8]) -> bool {
        input.iter().any(u8::is_ascii_alphabetic)
    }
    pub fn utf8(input: &[u8]) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(input)
    }
    pub fn trimmed_plus(text: &str) -> bool {
        text.trim_ascii_start().starts_with('+')
    }
    pub fn float_from_str(text: &str) -> Option<f64> {
        text.parse::<f64>().ok()
    }
    pub fn sort_values<T: Send, F: Fn(&T, &T) -> Ordering + Sync>(
        values: &mut Vec<T>,
        stable: bool,
        compare: F,
    ) {
        if stable {
            values.par_sort_by(compare);
        } else {
            values.par_sort_unstable_by(compare);
        }
    }
    pub fn sort_lines<F: Fn(&Vec<u8>, &Vec<u8>) -> Ordering + Sync>(
        lines: &mut Vec<Vec<u8>>,
        stable: bool,
        compare: F,
    ) {
        if stable {
            lines.par_sort_by(compare);
        } else {
            lines.par_sort_unstable_by(compare);
        }
    }
}
pub mod merging {
    use std::{cmp::Ordering, collections::BinaryHeap};
    pub fn heap_from<T: Ord>(values: Vec<T>) -> BinaryHeap<T> {
        BinaryHeap::from(values)
    }
    pub fn heap_empty<T>(heap: &BinaryHeap<T>) -> bool {
        heap.is_empty()
    }
    pub fn heap_peek<T: Ord>(heap: &BinaryHeap<T>) -> Option<&T> {
        heap.peek()
    }
    pub fn heap_pop<T: Ord>(heap: &mut BinaryHeap<T>) -> Option<T> {
        heap.pop()
    }
    pub fn heap_update_top<T: Ord, F: FnOnce(&mut T)>(heap: &mut BinaryHeap<T>, update: F) -> () {
        let mut entry = heap.peek_mut().unwrap();
        update(&mut *entry);
        ()
    }
    pub fn heap_into_vec<T>(heap: BinaryHeap<T>) -> Vec<T> {
        heap.into_vec()
    }
    pub fn rc_clone<T>(value: &std::rc::Rc<T>) -> std::rc::Rc<T> {
        std::rc::Rc::clone(value)
    }
    pub fn drop_sender<T>(sender: std::sync::mpsc::Sender<T>) {
        drop(sender);
    }
}
