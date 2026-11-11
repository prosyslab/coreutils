use crate::args::Args;
use crate::proof_common::State;
#[cfg(verus_keep_ghost)]
use crate::proof_common::ready;
use vstd::prelude::*;

verus! {
pub fn run(args: &Args, stdin: &[u8], stdout: &Vec<u8>, state: &mut Ghost<State>) -> Vec<u8>
    requires ready(args, stdin@, stdout@, old(state)@),
{
    #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(state@)))]
    let capture = crate::trusted::begin(stdin, stdout);
    let names = if args.filenames.is_empty() {
        vec![std::ffi::OsString::from("-")]
    } else { args.filenames.clone() };
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let result = super::paste(names, args.serial, &args.delimiters, args.line_ending);
    result.unwrap();
    #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(state@)))]
    let (bytes, remaining) = crate::trusted::finish(capture);
    #[cfg(verus_keep_ghost)]
    proof {
        assert(state@.valid());
        assert(state@.remaining(0) == remaining@);
        assert(state@.output() == bytes@);
    }
    bytes
}
}
