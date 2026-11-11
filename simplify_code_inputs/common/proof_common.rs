//! Shared models and lemmas across utilities.
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;

pub type Bytes = Seq<u8>;
pub type Path = Bytes;

pub ghost struct State {
    pub files: Map<Seq<u8>, Seq<u8>>,
    // 0: stdin, 1: stdout. Values: (bytes, read position).
    pub fd_table: Map<int, (Seq<u8>, nat)>,
}

impl State {
    pub open spec fn valid(&self) -> bool {
        &&& self.fd_table.dom().contains(0)
        &&& self.fd_table.dom().contains(1)
        &&& forall|fd: int| #[trigger] self.fd_table.dom().contains(fd) ==> (
            fd >= 0 && self.fd_table[fd].1 <= self.fd_table[fd].0.len())
    }

    #[verifier::opaque]
    pub open spec fn initial(&self) -> bool {
        self.valid() && self.fd_table.dom() == set![0int, 1int]
    }

    pub open spec fn remaining(&self, fd: int) -> Seq<u8> {
        self.fd_table[fd].0.skip(self.fd_table[fd].1 as int)
    }

    pub open spec fn output(&self) -> Seq<u8> { self.fd_table[1].0 }

    pub open spec fn advance(&self, fd: int, n: nat) -> State {
        State { files: self.files,
            fd_table: self.fd_table.insert(fd, (self.fd_table[fd].0, self.fd_table[fd].1 + n)) }
    }

    pub open spec fn append(&self, fd: int, bytes: Seq<u8>) -> State {
        State { files: self.files,
            fd_table: self.fd_table.insert(fd, (self.fd_table[fd].0 + bytes, self.fd_table[fd].1)) }
    }

    pub open spec fn open_file(&self, path: Seq<u8>, fd: int) -> State {
        State { files: self.files, fd_table: self.fd_table.insert(fd, (self.files[path], 0nat)) }
    }

    pub open spec fn close_file(&self, fd: int) -> State {
        State { files: self.files, fd_table: self.fd_table.remove(fd) }
    }

    pub proof fn open_valid(&self, path: Seq<u8>, fd: int)
        requires self.valid(), self.files.dom().contains(path), fd >= 3,
            !self.fd_table.dom().contains(fd),
        ensures self.open_file(path, fd).valid(),
            crate::trusted_common::fd::open(*self, self.open_file(path, fd), path, fd),
    {
        reveal(crate::trusted_common::fd::open);
        let after = self.open_file(path, fd);
        assert forall|key: int| #[trigger] after.fd_table.dom().contains(key) implies
            key >= 0 && after.fd_table[key].1 <= after.fd_table[key].0.len() by {
            if key != fd { assert(after.fd_table[key] == self.fd_table[key]); }
        }
    }

    pub proof fn close_valid(&self, fd: int)
        requires self.valid(), fd >= 3, self.fd_table.dom().contains(fd),
        ensures self.close_file(fd).valid(),
            crate::trusted_common::fd::close(*self, self.close_file(fd), fd),
    {
        let after = self.close_file(fd);
        assert forall|key: int| #[trigger] after.fd_table.dom().contains(key) implies
            key >= 0 && after.fd_table[key].1 <= after.fd_table[key].0.len() by {
            assert(after.fd_table[key] == self.fd_table[key]);
        }
    }

    pub proof fn advance_valid(&self, fd: int, n: nat)
        requires self.valid(), self.fd_table.dom().contains(fd), n <= self.remaining(fd).len(),
        ensures self.advance(fd, n).valid(),
            self.advance(fd, n).remaining(fd) == self.remaining(fd).skip(n as int),
    {
        let after = self.advance(fd, n);
        assert(after.fd_table.dom() =~= self.fd_table.dom());
        assert forall|key: int| #[trigger] after.fd_table.dom().contains(key) implies
            key >= 0 && after.fd_table[key].1 <= after.fd_table[key].0.len() by {
            if key == fd {
                assert(self.fd_table[fd].1 <= self.fd_table[fd].0.len());
            } else { assert(after.fd_table[key] == self.fd_table[key]); }
        }
        assert(after.remaining(fd) =~= self.remaining(fd).skip(n as int));
        assert(after.fd_table.dom().contains(0));
        assert(after.fd_table.dom().contains(1));
        assert(after.valid());
    }

    pub proof fn append_valid(&self, fd: int, bytes: Seq<u8>)
        requires self.valid(), self.fd_table.dom().contains(fd),
        ensures self.append(fd, bytes).valid(),
    {
        let after = self.append(fd, bytes);
        assert(after.fd_table.dom() =~= self.fd_table.dom());
        assert forall|key: int| #[trigger] after.fd_table.dom().contains(key) implies
            key >= 0 && after.fd_table[key].1 <= after.fd_table[key].0.len() by {
            assert(self.fd_table[key].1 <= self.fd_table[key].0.len());
            if key != fd { assert(after.fd_table[key] == self.fd_table[key]); }
        }
        assert(after.fd_table.dom().contains(0));
        assert(after.fd_table.dom().contains(1));
        assert(after.valid());
    }
}

pub trait Arguments {
    spec fn valid(&self) -> bool;
    open spec fn valid_state(&self, initial: State) -> bool { true }
}

pub open spec fn ready<A: Arguments>(args: &A, stdin: Seq<u8>, stdout: Seq<u8>, state: State) -> bool {
    &&& state.valid()
    &&& state.initial()
    &&& stdin == state.remaining(0)
    &&& stdout == state.output()
    &&& args.valid()
    &&& args.valid_state(state)
}

pub proof fn frame_transitive(before: State, middle: State, after: State)
    requires crate::trusted_common::fd::frame(before, middle),
        crate::trusted_common::fd::frame(middle, after),
    ensures crate::trusted_common::fd::frame(before, after),
{
    assert forall|fd: int| before.fd_table.dom().contains(fd) && fd != 0 && fd != 1
        implies #[trigger] after.fd_table[fd] == before.fd_table[fd] by {}
}

pub proof fn read_frame(before: State, n: nat)
    requires before.valid(), n <= before.remaining(0).len(),
    ensures crate::trusted_common::fd::frame(before, before.advance(0, n)),
{
    let after = before.advance(0, n);
    assert(after.fd_table.dom() =~= before.fd_table.dom());
    assert forall|fd: int| before.fd_table.dom().contains(fd) && fd != 0 && fd != 1
        implies #[trigger] after.fd_table[fd] == before.fd_table[fd] by {}
}

pub proof fn write_frame(before: State, bytes: Seq<u8>)
    requires before.valid(),
    ensures crate::trusted_common::fd::frame(before, before.append(1, bytes)),
{
    let after = before.append(1, bytes);
    assert(after.fd_table.dom() =~= before.fd_table.dom());
    assert forall|fd: int| before.fd_table.dom().contains(fd) && fd != 0 && fd != 1
        implies #[trigger] after.fd_table[fd] == before.fd_table[fd] by {}
}

#[cfg(verus_keep_ghost)]
pub fn finish_io(state: &mut Ghost<State>, stdout: Vec<u8>, unread: Ghost<Seq<u8>>)
    -> (result: Vec<u8>)
    requires old(state)@.valid(),
        unread@.len() == 0 || unread@ == old(state)@.remaining(0)
            || has_suffix(old(state)@.remaining(0), unread@),
        old(state)@.output().len() <= stdout.len(),
        stdout@.take(old(state)@.output().len() as int) == old(state)@.output(),
    ensures final(state)@.valid(), final(state)@.files == old(state)@.files,
        crate::trusted_common::fd::frame(old(state)@, final(state)@),
        final(state)@.remaining(0) == unread@,
        final(state)@.output() == result@, result@ == stdout@,
        crate::trusted_common::fd::read(old(state)@,
            old(state)@.advance(0, (old(state)@.remaining(0).len() - unread@.len()) as nat),
            0, (old(state)@.remaining(0).len() - unread@.len()) as nat,
            old(state)@.remaining(0).take(old(state)@.remaining(0).len() - unread@.len())),
        crate::trusted_common::fd::write(
            old(state)@.advance(0, (old(state)@.remaining(0).len() - unread@.len()) as nat),
            final(state)@, 1, stdout@.skip(old(state)@.output().len() as int)),
{
    let ghost initial = state@;
    proof {
        if unread@.len() == 0 {
            assert(initial.remaining(0).subrange(initial.remaining(0).len() as int,
                initial.remaining(0).len() as int) =~= unread@);
        } else if unread@ == initial.remaining(0) {
            assert(initial.remaining(0).subrange(0, initial.remaining(0).len() as int) =~= unread@);
        }
        assert(has_suffix(initial.remaining(0), unread@));
    }
    let ghost consumed = (initial.remaining(0).len() - unread@.len()) as nat;
    let ghost after_read = initial.advance(0, consumed);
    let ghost after_write = after_read.append(1, stdout@.skip(initial.output().len() as int));
    proof {
        initial.advance_valid(0, consumed);
        after_read.append_valid(1, stdout@.skip(initial.output().len() as int));
    }
    assert(after_read.remaining(0) =~= unread@);
    assert(after_write.output() =~= stdout@);
    assert(after_write.remaining(0) =~= after_read.remaining(0));
    proof {
        assert(after_write.fd_table.dom() =~= initial.fd_table.dom());
        assert forall|fd: int| initial.fd_table.dom().contains(fd) && fd != 0 && fd != 1
            implies #[trigger] after_write.fd_table[fd] == initial.fd_table[fd] by {}
    }
    *state = Ghost(after_write);
    stdout
}

#[cfg(verus_keep_ghost)]
pub fn write_output(stdout: &mut Vec<u8>, bytes: &[u8], state: &mut Ghost<State>)
    requires old(state)@.valid(), old(stdout)@ == old(state)@.output(),
    ensures final(state)@.valid(), final(stdout)@ == final(state)@.output(),
        crate::trusted_common::fd::frame(old(state)@, final(state)@),
        crate::trusted_common::fd::write(old(state)@, final(state)@, 1, bytes@),
        final(state)@.remaining(0) == old(state)@.remaining(0),
        final(state)@.files == old(state)@.files,
{
    let ghost initial = state@;
    proof { initial.append_valid(1, bytes@); }
    stdout.extend_from_slice(bytes);
    *state = Ghost(initial.append(1, bytes@));
    proof {
        assert(state@.fd_table.dom() =~= initial.fd_table.dom());
        assert forall|fd: int| initial.fd_table.dom().contains(fd) && fd != 0 && fd != 1
            implies #[trigger] state@.fd_table[fd] == initial.fd_table[fd] by {}
    }
}

pub open spec fn slice_values(parts: Seq<&[u8]>) -> Seq<Seq<u8>> {
    parts.map(|i: int, part: &[u8]| part@)
}

pub open spec fn flat_records(records: Seq<Seq<u8>>) -> Seq<u8>
    decreases records.len(),
{
    if records.len() == 0 { Seq::empty() }
    else { records[0] + flat_records(records.skip(1)) }
}

pub open spec fn well_formed_records(records: Seq<Seq<u8>>, ending: u8) -> bool {
    forall|i: int| 0 <= i < records.len() ==> {
        let record = #[trigger] records[i];
        &&& record.len() > 0
        &&& forall|j: int| 0 <= j < record.len() - 1 ==> record[j] != ending
        &&& (i + 1 < records.len() ==> record[record.len() - 1] == ending)
    }
}

pub open spec fn split_records(bytes: Seq<u8>, delimiter: u8) -> Seq<Seq<u8>>
    decreases bytes.len(),
{
    if bytes.len() == 0 { Seq::empty() }
    else if bytes[0] == delimiter {
        seq![seq![bytes[0]]] + split_records(bytes.skip(1), delimiter)
    } else {
        let rest = split_records(bytes.skip(1), delimiter);
        if rest.len() == 0 { seq![seq![bytes[0]]] }
        else { rest.update(0, seq![bytes[0]] + rest[0]) }
    }
}

pub open spec fn has_suffix(bytes: Seq<u8>, suffix: Seq<u8>) -> bool {
    suffix.len() <= bytes.len()
        && bytes.subrange(bytes.len() - suffix.len(), bytes.len() as int) == suffix
}

pub proof fn prefix_of_concat(prefix: Seq<u8>, tail: Seq<u8>)
    ensures (prefix + tail).take(prefix.len() as int) == prefix,
{
    assert((prefix + tail).take(prefix.len() as int) =~= prefix);
}

pub proof fn split_records_flat(bytes: Seq<u8>, delimiter: u8)
    ensures flat_records(split_records(bytes, delimiter)) == bytes,
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        split_records_flat(bytes.skip(1), delimiter);
        let rest = split_records(bytes.skip(1), delimiter);
        reveal_with_fuel(flat_records, 2);
        if bytes[0] != delimiter && rest.len() > 0 {
            assert(rest.update(0, seq![bytes[0]] + rest[0]).skip(1) =~= rest.skip(1));
        }
        assert(seq![bytes[0]] + bytes.skip(1) =~= bytes);
    }
}

pub broadcast proof fn slice_values_skip(parts: Seq<&[u8]>, n: int)
    requires 0 <= n <= parts.len(),
    ensures #[trigger] slice_values(parts.skip(n)) == slice_values(parts).skip(n),
{
    assert(slice_values(parts.skip(n)) =~= slice_values(parts).skip(n));
}

pub broadcast proof fn has_byte_suffix(bytes: Seq<u8>, ending: u8)
    ensures #[trigger] has_suffix(bytes, seq![ending])
        <==> bytes.len() > 0 && bytes[bytes.len() - 1] == ending,
{
    if bytes.len() > 0 {
        assert(bytes.subrange(bytes.len() as int - 1, bytes.len() as int) =~= seq![bytes[bytes.len() - 1]]);
    }
}

}
