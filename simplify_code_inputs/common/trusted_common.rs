//! Trusted contracts for dependencies outside the verification scope.
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::{IteratorSpec, IteratorSpecImpl};

#[cfg(verus_keep_ghost)]
pub mod fd {
    use crate::proof_common::State;
    use vstd::prelude::*;

    verus! {
    // Read-only files, successful I/O, and append-only output records.
    #[verifier::opaque]
    pub open spec fn open(before: State, after: State, path: Seq<u8>, fd: int) -> bool {
        &&& before.valid()
        &&& before.files.dom().contains(path)
        &&& fd >= 3 && !before.fd_table.dom().contains(fd)
        &&& after.files == before.files
        &&& after.fd_table == before.fd_table.insert(fd, (before.files[path], 0nat))
    }

    pub open spec fn read(before: State, after: State, fd: int, requested: nat, bytes: Seq<u8>) -> bool {
        &&& before.valid() && before.fd_table.dom().contains(fd)
        &&& bytes.len() <= requested && bytes.len() <= before.remaining(fd).len()
        &&& (requested > 0 && before.remaining(fd).len() > 0 ==> bytes.len() > 0)
        &&& bytes == before.remaining(fd).take(bytes.len() as int)
        &&& after == before.advance(fd, bytes.len())
    }

    pub open spec fn write(before: State, after: State, fd: int, bytes: Seq<u8>) -> bool {
        &&& before.valid() && before.fd_table.dom().contains(fd)
        &&& after == before.append(fd, bytes)
    }

    pub open spec fn close(before: State, after: State, fd: int) -> bool {
        before.valid() && fd >= 3 && before.fd_table.dom().contains(fd)
            && after == before.close_file(fd)
    }

    // std::fs::read opens, consumes, and closes a scoped input descriptor.
    #[verifier::opaque]
    pub open spec fn file_read(before: State, path: Seq<u8>, fd: int, bytes: Seq<u8>) -> bool {
        let opened = State { files: before.files,
            fd_table: before.fd_table.insert(fd, (bytes, 0nat)) };
        open(before, opened, path, fd)
            && read(opened, opened.advance(fd, bytes.len()), fd, bytes.len(), bytes)
    }

    pub open spec fn frame(before: State, after: State) -> bool {
        &&& after.files == before.files
        &&& after.fd_table.dom() == before.fd_table.dom()
        &&& after.fd_table[0].0 == before.fd_table[0].0
        &&& after.fd_table[1].1 == before.fd_table[1].1
        &&& forall|fd: int| before.fd_table.dom().contains(fd) && fd != 0 && fd != 1 ==>
            #[trigger] after.fd_table[fd] == before.fd_table[fd]
    }
    }
}

#[cfg(verus_keep_ghost)]
pub mod filesystem {
    use crate::proof_common::{Bytes, Path};
    use vstd::prelude::*;

    verus! {
    // Fixed readable files in the actual environment.
    pub uninterp spec fn contents() -> Map<Path, Bytes>;

    pub open spec fn matches(files: Map<Path, Bytes>) -> bool {
        forall|path: Path| #[trigger] files.dom().contains(path) ==>
            contents().dom().contains(path) && files[path] == contents()[path]
    }

    pub open spec fn readable(files: Map<Path, Bytes>, path: Path) -> bool {
        files.dom().contains(path) && files[path].len() <= usize::MAX
    }
    }
}

// Keep one closure body in both builds; erase its contract in ordinary Rust.
#[cfg(verus_keep_ghost)]
#[allow(unused_macros)]
macro_rules! closure_with_spec {
    (($($spec:tt)*), $closure:expr) => {
        #[verus_spec($($spec)*)] $closure
    };
}
#[cfg(not(verus_keep_ghost))]
macro_rules! closure_with_spec {
    (($($spec:tt)*), $closure:expr) => {
        $closure
    };
}
pub(crate) use closure_with_spec;

#[cfg(verus_keep_ghost)]
verus! {
pub type IndexedPredicate<T> = spec_fn(usize, T) -> bool;
pub type Predicate<T> = spec_fn(T) -> bool;

pub open spec fn selected_indices<T>(input: Seq<T>, predicate: IndexedPredicate<T>) -> Seq<usize> {
    Seq::new(input.len(), |i: int| i as usize)
        .filter(|i: usize| predicate(i, input[i as int]))
}
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires forall|i: usize| i < 256 ==> #[trigger] f.requires((i,)),
    ensures forall|i: int| 0 <= i < 256 ==> f.ensures((i as usize,), result@[i]),
))]
pub fn array_from_fn<T, F: Fn(usize) -> T>(f: F) -> [T; 256] {
    std::array::from_fn(f)
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires forall|i: int| 0 <= i < 256 ==> f.requires((input@[i],)),
    ensures forall|i: int| 0 <= i < 256 ==> f.ensures((input@[i],), result@[i]),
))]
pub fn array_map<T, U, F: Fn(T) -> U>(input: [T; 256], f: F) -> [U; 256] {
    input.map(f)
}

// zip(left, chain(right, repeat(fallback))).collect().
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.len() == left.len(),
        forall|i: int| 0 <= i < left.len() ==> result@[i] == (
            left@[i], if i < right.len() { right@[i] } else { fallback }),
))]
pub fn zip_with_repeat<T: Copy, U: Copy>(left: &[T], right: &[U], fallback: U) -> Vec<(T, U)> {
    left.iter().copied().zip(right.iter().copied().chain(std::iter::repeat(fallback))).collect()
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Ghost(predicate): Ghost<IndexedPredicate<T>>,
    requires
        forall|i: int| 0 <= i < input.len() ==> check.requires((i as usize, &input@[i])),
        forall|i: int, value: bool| 0 <= i < input.len()
            && #[trigger] check.ensures((i as usize, &input@[i]), value)
            ==> value == predicate(i as usize, input@[i]),
    ensures {
        let indices = selected_indices(input@, predicate);
        &&& result.len() == if indices.len() < limit { indices.len() } else { limit as nat }
        &&& forall|j: int| 0 <= j < result.len() ==>
            result@[j] == (indices[j], input@[indices[j] as int])
    },
))]
pub fn enumerated_filter_take<T: Copy, F: Fn(usize, &T) -> bool>(
    input: &[T], check: F, limit: usize,
) -> Vec<(usize, T)> {
    input.iter().enumerate().filter_map(|(i, value)| check(i, value).then_some((i, *value)))
        .take(limit).collect()
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Ghost(predicate): Ghost<Predicate<T>>,
    requires
        forall|i: int| 0 <= i < input.len() ==> f.requires((&input@[i],)),
        forall|i: int, value: bool| 0 <= i < input.len()
            && #[trigger] f.ensures((&input@[i],), value) ==> value == predicate(input@[i]),
    ensures result <= input.len(), result == input@.filter(predicate).len(),
))]
pub fn count_filtered<T, F: Fn(&T) -> bool>(input: &[T], f: F) -> usize {
    input.iter().filter(|item| f(*item)).count()
}

// Standard byte splitting and collection, preserving record boundaries.
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(parts =>
    ensures
        crate::proof_common::slice_values(parts@) == crate::proof_common::split_records(input@, delimiter),
        crate::proof_common::flat_records(crate::proof_common::slice_values(parts@)) == input@,
        crate::proof_common::well_formed_records(crate::proof_common::slice_values(parts@), delimiter),
        parts.len() <= input.len(),
))]
pub fn split_inclusive(input: &[u8], delimiter: u8) -> Vec<&[u8]> {
    input.split_inclusive(|&byte| byte == delimiter).collect()
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures if crate::proof_common::has_suffix(input@, suffix@) {
        result is Some && result->Some_0@ == input@.take(input@.len() - suffix@.len())
    } else { result is None },
))]
pub fn strip_suffix<'a>(input: &'a [u8], suffix: &[u8]) -> Option<&'a [u8]> {
    input.strip_suffix(suffix)
}

// Apply a byte callback and append its results in input order.
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires forall|i: int| #![auto] 0 <= i < input.len() ==> f.requires((input@[i],)),
    ensures
        final(output)@.len() == old(output)@.len() + input@.len(),
        final(output)@.take(old(output)@.len() as int) == old(output)@,
        forall|i: int| 0 <= i < input.len() ==>
            f.ensures((input@[i],), final(output)@[old(output)@.len() + i]),
))]
pub fn extend_mapped<F: Fn(u8) -> u8>(output: &mut Vec<u8>, input: &[u8], f: F) {
    output.extend(input.iter().copied().map(f));
}

#[cfg(verus_keep_ghost)]
verus! {

pub assume_specification<T>[bool::then_some](condition: bool, value: T) -> (result: Option<T>)
    ensures result == if condition { Some(value) } else { None },
;

pub assume_specification<'a, T: Copy>[Option::<&'a T>::copied](value: Option<&'a T>)
    -> (result: Option<T>)
    ensures result == match value { Some(reference) => Some(*reference), None => None },
;

impl<'a> Chunks<'a> {
    pub uninterp spec fn values(&self) -> Seq<&'a [u8]>;
}

impl<'a> IteratorSpecImpl for Chunks<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }
    open spec fn remaining(&self) -> Seq<Self::Item> { self.values() }
    open spec fn will_return_none(&self) -> bool { true }
    open spec fn decrease(&self) -> Option<nat> { Some(self.values().len()) }
    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < self.values().len() { Some(self.values()[index]) } else { None }
    }
}

pub open spec fn chunks_match(input: Seq<u8>, parts: Seq<&[u8]>, size: int) -> bool {
    &&& size > 0
    &&& parts.len() == (input.len() + size - 1) / size
    &&& forall|i: int| 0 <= i < parts.len() ==> {
        let end = if (i + 1) * size < input.len() { (i + 1) * size } else { input.len() as int };
        &&& 0 < (#[trigger] parts[i])@.len() <= size
        &&& parts[i]@ == input.subrange(i * size, end)
    }
}

pub assume_specification[<usize as From<bool>>::from](value: bool) -> (result: usize)
    ensures result == if value { 1usize } else { 0usize },
;

// Follow PartialEq's model; arbitrary types need not use mathematical equality.
pub assume_specification<T: PartialEq>[<[T]>::contains](slice: &[T], byte: &T) -> (found: bool)
    ensures
        T::obeys_eq_spec() ==> (found <==> exists|i: int|
            0 <= i < slice@.len() && (#[trigger] slice@[i]).eq_spec(byte)),
;

}

// Byte-slice iterator; next() delegates to the real slice iterator.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub struct Chunks<'a> {
    inner: std::slice::Chunks<'a, u8>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<'a> Iterator for Chunks<'a> {
    type Item = &'a [u8];

    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires size > 0,
    ensures chunks_match(input@, result.values(), size as int),
))]
pub fn chunks<'a>(input: &'a [u8], size: usize) -> Chunks<'a> {
    Chunks {
        inner: input.chunks(size),
    }
}

pub mod io {
    #[cfg(verus_keep_ghost)]
    use std::io::BufRead;
    use std::io::{Read, Write};
    #[cfg(any(verus_keep_ghost, uutils_sort_full))]
    use vstd::prelude::*;

    #[cfg(verus_keep_ghost)]
    verus! {
    #[verifier::external_trait_specification]
    pub trait ExRead { type ExternalTraitSpecificationFor: Read; }
    #[verifier::external_trait_specification]
    pub trait ExBufRead: Read { type ExternalTraitSpecificationFor: BufRead; }
    #[verifier::external_trait_specification]
    pub trait ExWrite { type ExternalTraitSpecificationFor: Write; }
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExError(std::io::Error);

    pub uninterp spec fn remaining<R>(reader: &R) -> Seq<u8>;
    pub uninterp spec fn written<W>(writer: &W) -> Seq<u8>;
    pub uninterp spec fn readable<R>(reader: &R) -> bool;
    pub uninterp spec fn writable<W>(writer: &W) -> bool;

    pub open spec fn observes<R, W>(state: crate::proof_common::State, input: &R, output: &W) -> bool {
        readable(input) && writable(output)
            && remaining(input) == state.remaining(0) && written(output) == state.output()
    }

    }

    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires readable(old(input)), old(buf).len() > 0,
        ensures readable(final(input)), result is Ok,
            result->Ok_0 <= old(buf).len(), result->Ok_0 <= remaining(old(input)).len(),
            (result->Ok_0 == 0) == (remaining(old(input)).len() == 0),
            final(buf)@.take(result->Ok_0 as int) == remaining(old(input)).take(result->Ok_0 as int),
            remaining(final(input)) == remaining(old(input)).skip(result->Ok_0 as int),
    ))]
    pub fn read<R: Read>(input: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
        input.read(buf)
    }

    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires writable(old(output)),
        ensures writable(final(output)), result is Ok,
            written(final(output)) == written(old(output)) + bytes@,
    ))]
    pub fn write_all<W: Write>(output: &mut W, bytes: &[u8]) -> std::io::Result<()> {
        output.write_all(bytes)
    }

    // Rust Read::read_to_end under the same successful-I/O assumption as read().
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires readable(old(input)),
        ensures readable(final(input)), result is Ok,
            result->Ok_0@ == remaining(old(input)), remaining(final(input)).len() == 0,
    ))]
    pub fn read_all<R: Read>(input: &mut R) -> std::io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        input.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with state: &mut Ghost<crate::proof_common::State>,
        requires old(state)@.valid(), readable(old(input)), old(buf).len() > 0,
            remaining(old(input)) == old(state)@.remaining(0),
        ensures result is Ok, readable(final(input)), final(state)@.valid(),
            result->Ok_0 <= old(buf).len(),
            (result->Ok_0 == 0) == (old(state)@.remaining(0).len() == 0),
            final(buf)@.take(result->Ok_0 as int)
                == old(state)@.remaining(0).take(result->Ok_0 as int),
            remaining(final(input)) == final(state)@.remaining(0),
            final(state)@ == old(state)@.advance(0, result->Ok_0 as nat),
            crate::trusted_common::fd::read(old(state)@, final(state)@,
                0, old(buf).len() as nat, final(buf)@.take(result->Ok_0 as int)),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    ))]
    pub fn read_state<R: Read>(input: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
        let result = read(input, buf);
        #[cfg(verus_keep_ghost)]
        {
            proof_decl! {
                let ghost before = state@;
                let ghost after = before.advance(0, result->Ok_0 as nat);
            }
            proof! {
                before.advance_valid(0, result->Ok_0 as nat);
                crate::proof_common::read_frame(before, result->Ok_0 as nat);
                *state = Ghost(after);
            }
        }
        result
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with state: &mut Ghost<crate::proof_common::State>,
        requires old(state)@.valid(), writable(old(output)),
            written(old(output)) == old(state)@.output(),
        ensures result is Ok, writable(final(output)), final(state)@.valid(),
            written(final(output)) == final(state)@.output(),
            final(state)@ == old(state)@.append(1, bytes@),
            crate::trusted_common::fd::write(old(state)@, final(state)@, 1, bytes@),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    ))]
    pub fn write_state<W: Write>(output: &mut W, bytes: &[u8]) -> std::io::Result<()> {
        let result = write_all(output, bytes);
        #[cfg(verus_keep_ghost)]
        {
            proof_decl! {
                let ghost before = state@;
                let ghost after = before.append(1, bytes@);
            }
            proof! {
                before.append_valid(1, bytes@);
                crate::proof_common::write_frame(before, bytes@);
                *state = Ghost(after);
            }
        }
        result
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with state: &mut Ghost<crate::proof_common::State>,
        requires old(state)@.valid(), readable(old(input)),
            remaining(old(input)) == old(state)@.remaining(0),
        ensures result is Ok, readable(final(input)), final(state)@.valid(),
            result->Ok_0@ == old(state)@.remaining(0), final(state)@.remaining(0).len() == 0,
            remaining(final(input)) == final(state)@.remaining(0),
            final(state)@ == old(state)@.advance(0, old(state)@.remaining(0).len()),
            crate::trusted_common::fd::read(old(state)@, final(state)@,
                0, old(state)@.remaining(0).len(), result->Ok_0@),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    ))]
    pub fn read_all_state<R: Read>(input: &mut R) -> std::io::Result<Vec<u8>> {
        let result = read_all(input);
        #[cfg(verus_keep_ghost)]
        {
            proof_decl! { let ghost before = state@; }
            proof! {
                before.advance_valid(0, before.remaining(0).len());
                crate::proof_common::read_frame(before, before.remaining(0).len());
                assert(before.remaining(0).take(before.remaining(0).len() as int) =~= before.remaining(0));
                *state = Ghost(before.advance(0, before.remaining(0).len()));
            }
        }
        result
    }

    #[cfg(any(verus_keep_ghost, uutils_sort_full))]
    verus! {
    pub fn read_stdin(stdin: &[u8], state: &mut Ghost<crate::proof_common::State>)
        -> (result: Vec<u8>)
        requires old(state)@.valid(), stdin@ == old(state)@.remaining(0),
        ensures final(state)@.valid(), result@ == old(state)@.remaining(0),
            final(state)@.remaining(0).len() == 0,
            final(state)@ == old(state)@.advance(0, old(state)@.remaining(0).len()),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    {
        let mut input = reader(stdin);
        #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
        let result = read_all_state(&mut input);
        result.unwrap()
    }

    pub fn write_stdout(stdout: &Vec<u8>, bytes: &[u8], state: &mut Ghost<crate::proof_common::State>)
        -> (result: Vec<u8>)
        requires old(state)@.valid(), stdout@ == old(state)@.output(),
        ensures final(state)@.valid(), result@ == final(state)@.output(),
            final(state)@ == old(state)@.append(1, bytes@),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    {
        let mut output = writer(stdout);
        #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
        let result = write_state(&mut output, bytes);
        assert(result is Ok);
        finish(output)
    }

    #[cfg(verus_keep_ghost)]
    pub fn finish_observed<R>(input: &R, output: Vec<u8>, state: Ghost<crate::proof_common::State>)
        -> (result: Vec<u8>)
        requires state@.valid(), observes(state@, input, &output),
        ensures result@ == state@.output(),
    {
        finish(output)
    }

    #[cfg(verus_keep_ghost)]
    pub fn begin_state<'a>(stdin: &'a [u8], stdout: &Vec<u8>, state: Ghost<crate::proof_common::State>)
        -> (streams: (&'a [u8], Vec<u8>))
        requires stdin@ == state@.remaining(0), stdout@ == state@.output(),
        ensures observes(state@, &streams.0, &streams.1),
    {
        (reader(stdin), writer(stdout))
    }

    #[cfg(verus_keep_ghost)]
    pub fn finish_state<R>(input: &R, output: Vec<u8>, state: &mut Ghost<crate::proof_common::State>)
        -> (result: Vec<u8>)
        requires old(state)@.valid(),
            remaining(input).len() == 0 || remaining(input) == old(state)@.remaining(0)
                || crate::proof_common::has_suffix(old(state)@.remaining(0), remaining(input)),
            old(state)@.output().len() <= written(&output).len(),
            written(&output).take(old(state)@.output().len() as int) == old(state)@.output(),
        ensures final(state)@.files == old(state)@.files,
            final(state)@.remaining(0) == remaining(input),
            final(state)@.output() == written(&output), result@ == final(state)@.output(),
            final(state)@.valid(),
            crate::trusted_common::fd::frame(old(state)@, final(state)@),
    {
        let ghost unread = remaining(input);
        let stdout = finish(output);
        crate::proof_common::finish_io(state, stdout, Ghost(unread))
    }

    #[verifier::external_body]
    pub fn reader(input: &[u8]) -> (result: &[u8])
        ensures readable(&result), remaining(&result) == input@,
    { input }

    #[verifier::external_body]
    pub fn writer(initial: &Vec<u8>) -> (result: Vec<u8>)
        ensures writable(&result), written(&result) == initial@,
    { initial.clone() }

    #[verifier::external_body]
    pub fn finish(output: Vec<u8>) -> (result: Vec<u8>)
        ensures result@ == written(&output),
    { output }
    }
}
