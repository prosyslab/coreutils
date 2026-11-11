use crate::proof_common::Arguments;
use std::ffi::OsString;
use vstd::prelude::*;

verus! {
pub struct Args {
    pub paths: Vec<OsString>,
    pub zero: bool,
}

impl Arguments for Args {
    open spec fn valid(&self) -> bool { self.paths.len() > 0 }
}
}
