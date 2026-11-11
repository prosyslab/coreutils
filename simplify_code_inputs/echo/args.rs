use crate::proof_common::Arguments;
use std::ffi::OsString;
use vstd::prelude::*;

verus! {
pub struct Args {
    pub strings: Vec<OsString>,
    pub trailing_newline: bool,
    pub escape: bool,
}

impl Arguments for Args {
    open spec fn valid(&self) -> bool { true }
}
}
