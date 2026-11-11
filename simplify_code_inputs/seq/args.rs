use crate::proof_common::Arguments;
use std::ffi::OsString;
use uucore::extendedbigdecimal::ExtendedBigDecimal;
use vstd::prelude::*;

verus! {
pub struct Number {
    pub value: ExtendedBigDecimal,
    pub integral_digits: usize,
    pub fractional_digits: Option<usize>,
}

pub struct Args {
    pub first: Number,
    pub increment: Number,
    pub last: Number,
    pub separator: OsString,
    pub terminator: OsString,
    pub equal_width: bool,
    pub format: Option<String>,
}

pub uninterp spec fn finite(value: ExtendedBigDecimal) -> bool;
pub uninterp spec fn zero(value: ExtendedBigDecimal) -> bool;

impl Arguments for Args {
    open spec fn valid(&self) -> bool {
        finite(self.first.value) && finite(self.increment.value) && finite(self.last.value)
            && !zero(self.increment.value) && !(self.equal_width && self.format is Some)
    }
}
}
