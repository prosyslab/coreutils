use crate::proof_common::Arguments;
#[cfg(verus_keep_ghost)]
use crate::proof_common::State;
use std::ffi::OsString;
use vstd::prelude::*;

verus! {
#[derive(Clone, Copy)]
pub enum Mode { Text, Numeric, HumanNumeric, GeneralNumeric, Month }
pub struct OrderingOptions {
    pub mode: Mode,
    pub ignore_blanks: bool,
    pub ignore_case: bool,
    pub dictionary: bool,
    pub ignore_nonprinting: bool,
    pub reverse: bool,
}
pub struct Position { pub field: usize, pub offset: usize, pub skip_blanks: bool }
pub struct EndPosition { pub field: usize, pub offset: Option<usize>, pub skip_blanks: bool }
pub struct Key { pub start: Position, pub end: Option<EndPosition>, pub ordering: OrderingOptions }
pub struct SortOptions {
    pub keys: Vec<Key>,
    pub ordering: OrderingOptions,
    pub separator: Option<u8>,
    pub stable: bool,
    pub unique: bool,
    pub zero_terminated: bool,
    pub random_salt: [u8; 16],
}
pub struct Args { pub filenames: Vec<OsString>, pub options: SortOptions }
impl Arguments for Args {
    open spec fn valid(&self) -> bool { !self.options.stable }
    open spec fn valid_state(&self, initial: State) -> bool {
        crate::filesystem::normal_files(self.filenames@, initial.files)
    }
}
}
