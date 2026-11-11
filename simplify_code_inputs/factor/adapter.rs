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
    let (input, output) = crate::trusted_common::io::begin_state(stdin, stdout, Ghost(state@));
    #[cfg(not(verus_keep_ghost))]
    let (input, output) = (stdin, stdout.clone());
    let mut input = std::io::BufReader::new(input);
    let mut output = std::io::BufWriter::with_capacity(4 * 1024, output);
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let _status = super::execute(&args.numbers, &mut input, &mut output, args.print_exponents);
    let output = output.into_inner().unwrap();
    #[cfg(verus_keep_ghost)]
    { crate::trusted_common::io::finish(output) }
    #[cfg(not(verus_keep_ghost))]
    { output }
}
}
