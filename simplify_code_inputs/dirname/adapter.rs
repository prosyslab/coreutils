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
    let ending = if args.zero { 0u8 } else { b'\n' };
    for path in &args.paths {
        #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
        let result = super::write_name(path.as_os_str(), ending, &mut output);
        result.unwrap();
    }
    #[cfg(verus_keep_ghost)]
    { crate::trusted_common::io::finish(output) }
    #[cfg(not(verus_keep_ghost))]
    { output }
}
}
