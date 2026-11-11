use crate::args::{Args, Number};
use crate::proof_common::State;
#[cfg(verus_keep_ghost)]
use crate::proof_common::ready;
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
fn number(input: &Number) -> super::number::PreciseNumber {
    super::number::PreciseNumber::new(input.value.clone(), input.integral_digits, input.fractional_digits)
}

verus! {
pub fn run(args: &Args, stdin: &[u8], stdout: &Vec<u8>, state: &mut Ghost<State>) -> Vec<u8>
    requires ready(args, stdin@, stdout@, old(state)@),
{
    #[cfg(verus_keep_ghost)]
    let output = crate::trusted_common::io::writer(stdout);
    #[cfg(not(verus_keep_ghost))]
    let output = stdout.clone();
    let mut output = std::io::BufWriter::new(output);
    let options = super::SeqOptions {
        separator: args.separator.clone(), terminator: args.terminator.clone(),
        equal_width: args.equal_width, format: args.format.as_deref(),
    };
    #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
    let _status = super::execute(number(&args.first), number(&args.increment), number(&args.last), &options, &mut output);
    let output = output.into_inner().unwrap();
    #[cfg(verus_keep_ghost)]
    { crate::trusted_common::io::finish(output) }
    #[cfg(not(verus_keep_ghost))]
    { output }
}
}
