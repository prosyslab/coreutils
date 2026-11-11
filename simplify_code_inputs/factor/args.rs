use crate::proof_common::Arguments;
use vstd::prelude::*;

verus! {
pub struct Args {
    pub numbers: Vec<String>,
    pub print_exponents: bool,
}

impl Arguments for Args {
    open spec fn valid(&self) -> bool { true }
}
}
