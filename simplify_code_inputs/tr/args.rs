use crate::proof_common::Arguments;
use vstd::prelude::*;

verus! {
#[derive(Clone, Copy)]
pub enum Mode { Delete, Squeeze, Translate, DeleteAndSqueeze, TranslateAndSqueeze }

pub struct Args {
    pub mode: Mode,
    pub set1: Vec<u8>,
    pub set2: Vec<u8>,
}

impl Arguments for Args {
    open spec fn valid(&self) -> bool {
        match self.mode {
            Mode::Translate | Mode::TranslateAndSqueeze => self.set1.len() == 0 || self.set2.len() > 0,
            _ => true,
        }
    }
}
}
