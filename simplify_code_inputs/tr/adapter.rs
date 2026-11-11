use crate::args::{Args, Mode};
use crate::proof_common::State;
#[cfg(verus_keep_ghost)]
use crate::proof_common::ready;
use super::operation::{DeleteOperation, SqueezeOperation, SymbolTranslator, TranslateOperation};
use vstd::prelude::*;

fn delete(set: &[u8]) -> DeleteOperation {
    let keep_table = super::tr_trusted::make_keep_table(set);
    let single_delete = super::simd::find_single_change(&keep_table, |_, &keep| !keep)
        .map(|(byte, _)| byte);
    DeleteOperation { keep_table, single_delete }
}

fn squeeze(set: &[u8]) -> SqueezeOperation {
    SqueezeOperation { squeeze_table: super::tr_trusted::set_to_bitmap(set), previous: None }
}

fn translate(set1: &[u8], set2: &[u8]) -> TranslateOperation {
    let translation_table = super::tr_trusted::make_translation_table(set1, set2);
    let single_change = super::simd::find_single_change(&translation_table, |i, &byte| byte != i as u8);
    TranslateOperation { translation_table, single_change }
}

verus! {
pub fn run(args: &Args, stdin: &[u8], stdout: &Vec<u8>, state: &mut Ghost<State>) -> Vec<u8>
    requires ready(args, stdin@, stdout@, old(state)@),
{
    #[cfg(verus_keep_ghost)]
    let (mut reader, mut output) = crate::trusted_common::io::begin_state(stdin, stdout, Ghost(state@));
    #[cfg(not(verus_keep_ghost))]
    let (mut reader, mut output) = (stdin, stdout.clone());
    match args.mode {
        Mode::Delete => {
            let op = delete(&args.set1);
            #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
            let result = super::simd::process_input(&mut reader, &mut output, &op);
            result.unwrap();
        },
        Mode::Squeeze => {
            let op = squeeze(&args.set1);
            #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
            let result = super::operation::translate_input(&mut reader, &mut output, op);
            result.unwrap();
        },
        Mode::Translate => {
            let op = translate(&args.set1, &args.set2);
            #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
            let result = super::simd::process_input(&mut reader, &mut output, &op);
            result.unwrap();
        },
        Mode::DeleteAndSqueeze => {
            let op = delete(&args.set1).chain(squeeze(&args.set2));
            #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
            let result = super::operation::translate_input(&mut reader, &mut output, op);
            result.unwrap();
        },
        Mode::TranslateAndSqueeze => {
            let op = translate(&args.set1, &args.set2).chain(squeeze(&args.set2));
            #[cfg_attr(verus_keep_ghost, verus_spec(with &mut *state))]
            let result = super::operation::translate_input(&mut reader, &mut output, op);
            result.unwrap();
        },
    }
    #[cfg(verus_keep_ghost)]
    { crate::trusted_common::io::finish_observed(&reader, output, Ghost(state@)) }
    #[cfg(not(verus_keep_ghost))]
    { output }
}
}
