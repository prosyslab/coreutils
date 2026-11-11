use crate::proof_common::Arguments;
#[cfg(verus_keep_ghost)]
use crate::proof_common::State;
use std::ffi::OsString;
use uucore::line_ending::LineEnding;
use vstd::prelude::*;

verus! {
pub struct Args {
    pub filenames: Vec<OsString>,
    pub delimiters: OsString,
    pub serial: bool,
    pub line_ending: LineEnding,
}

pub open spec fn valid_delimiters(bytes: Seq<u8>, i: int) -> bool
    decreases bytes.len() - i,
{
    if i >= bytes.len() { true }
    else if bytes[i] == 92 { i + 1 < bytes.len() && valid_delimiters(bytes, i + 2) }
    else { valid_delimiters(bytes, i + 1) }
}

impl Arguments for Args {
    open spec fn valid(&self) -> bool {
        valid_delimiters(crate::filesystem::os_bytes(&self.delimiters), 0)
    }
    open spec fn valid_state(&self, initial: State) -> bool {
        crate::filesystem::normal_files(self.filenames@, initial.files)
    }
}
}
