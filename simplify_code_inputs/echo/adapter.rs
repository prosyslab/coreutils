use crate::args::Args;
use crate::proof_common::State;
#[cfg(verus_keep_ghost)]
use crate::proof_common::ready;
use vstd::prelude::*;

verus! {
pub fn run(args: &Args, stdin: &[u8], stdout: &Vec<u8>, state: &mut Ghost<State>) -> Vec<u8>
    requires ready(args, stdin@, stdout@, old(state)@),
{
    #[cfg(verus_keep_ghost)]
    let mut output = crate::trusted_common::io::writer(stdout);
    #[cfg(not(verus_keep_ghost))]
    let mut output = stdout.clone();
    let options = super::Options { trailing_newline: args.trailing_newline, escape: args.escape };
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let result = super::execute(&mut output, args.strings.clone().into_iter(), options);
    result.unwrap();
    #[cfg(verus_keep_ghost)]
    { crate::trusted_common::io::finish(output) }
    #[cfg(not(verus_keep_ghost))]
    { output }
}
}
