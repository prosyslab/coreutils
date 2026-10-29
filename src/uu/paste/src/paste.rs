// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

#[cfg(not(verus_keep_ghost))]
use clap::{Arg, ArgAction, Command};
use std::cell::{OnceCell, RefCell};
use std::ffi::OsString;
use std::fs::File;
use std::io::{stdin, stdout, BufRead, BufReader, Read, Stdin, Write};
use std::iter::Cycle;
use std::rc::Rc;
use std::slice::Iter;
#[cfg(not(verus_keep_ghost))]
use uucore::error::{UResult, USimpleError};
#[cfg(not(verus_keep_ghost))]
use uucore::format_usage;
use uucore::i18n::charmap::mb_char_len;
use uucore::line_ending::LineEnding;
#[cfg(not(verus_keep_ghost))]
use uucore::translate;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
type UResult<T> = std::io::Result<T>;
#[cfg(verus_keep_ghost)]
use crate::paste_trusted;
#[cfg(verus_keep_ghost)]
use paste_trusted::proof::{self as paste_proof, World};
#[cfg(verus_keep_ghost)]
verus! {
    broadcast use {vstd::seq_lib::group_seq_properties, vstd::arithmetic::div_mod::group_mod_basics};
}
#[cfg(not(verus_keep_ghost))]
#[path = "../../../../../paste/trusted_common.rs"]
mod paste_trusted;
#[cfg(not(verus_keep_ghost))]
#[allow(dead_code, unused_imports, unused_macros)]
#[path = "../../../../../trusted_common.rs"]
mod trusted_common;

#[cfg(not(verus_keep_ghost))]
mod options {
    pub const DELIMITER: &str = "delimiters";
    pub const SERIAL: &str = "serial";
    pub const FILE: &str = "file";
    pub const ZERO_TERMINATED: &str = "zero-terminated";
}

#[cfg(not(verus_keep_ghost))]
#[uucore::main]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let matches = uucore::clap_localization::handle_clap_result(uu_app(), args)?;

    let serial = matches.get_flag(options::SERIAL);
    let delimiters = matches.get_one::<OsString>(options::DELIMITER).unwrap();
    let files = matches
        .get_many::<OsString>(options::FILE)
        .unwrap()
        .cloned()
        .collect();
    let line_ending = LineEnding::from_zero_flag(matches.get_flag(options::ZERO_TERMINATED));

    paste(files, serial, delimiters, line_ending)
}

#[cfg(not(verus_keep_ghost))]
pub fn uu_app() -> Command {
    Command::new("paste")
        .version(uucore::crate_version!())
        .help_template(uucore::localized_help_template("paste"))
        .about(translate!("paste-about"))
        .override_usage(format_usage(&translate!("paste-usage")))
        .infer_long_args(true)
        // GNU lets a later -d override an earlier one.
        .args_override_self(true)
        .arg(
            Arg::new(options::SERIAL)
                .long(options::SERIAL)
                .short('s')
                .help(translate!("paste-help-serial"))
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::DELIMITER)
                .long(options::DELIMITER)
                .short('d')
                .help(translate!("paste-help-delimiter"))
                .value_name("LIST")
                .default_value("\t")
                .hide_default_value(true)
                .allow_hyphen_values(true)
                .value_parser(clap::value_parser!(OsString)),
        )
        .arg(
            Arg::new(options::FILE)
                .value_name("FILE")
                .action(ArgAction::Append)
                .default_value("-")
                .value_hint(clap::ValueHint::FilePath)
                .value_parser(clap::value_parser!(OsString)),
        )
        .arg(
            Arg::new(options::ZERO_TERMINATED)
                .long(options::ZERO_TERMINATED)
                .short('z')
                .help(translate!("paste-help-zero-terminated"))
                .action(ArgAction::SetTrue),
        )
}

#[allow(clippy::cognitive_complexity)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(world): Tracked<&mut World>,
    requires old(world).start(filenames@, line_ending),
    ensures final(world).valid(),
        final(world).names() == old(world).names(),
        final(world).ending() == old(world).ending(),
        final(world).session() == old(world).session(),
        final(world).output() == paste_proof::expected(filenames@, *delimiters, line_ending, serial),
))]
pub(crate) fn paste(
    filenames: Vec<OsString>,
    serial: bool,
    delimiters: &OsString,
    line_ending: LineEnding,
) -> UResult<()> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost names = filenames@;
        let ghost session = world.session();
        let ghost target = paste_proof::expected(names, *delimiters, line_ending, serial);
    }
    let unescaped_and_encoded_delimiters = parse_delimiters(delimiters)?;
    #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&*world)))]
    let mut input_source_vec = open_inputs(filenames)?;

    let line_ending_byte = u8::from(line_ending);
    let input_source_vec_len = input_source_vec.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&*world)))]
    let mut stdout = paste_trusted::lock_stdout(&stdout());

    if !serial && input_source_vec_len == 1 {
        #[cfg(verus_keep_ghost)]
        proof! {
            paste_proof::total_component(world.records(), paste_proof::ids(names)[0], world.records().len() as int);
            paste_proof::single_column(world.records(), paste_proof::ids(names), paste_proof::delimiters(unescaped_and_encoded_delimiters@),
                line_ending_byte, paste_proof::total(world.records(), world.records().len() as int) as int + 1);
        }
        // With a single input source (no -s), `paste` output is identical to input,
        // except that a missing final line ending must be added.
        // Stream directly to avoid unbounded line buffering on inputs like /dev/zero.
        return {
            #[cfg(verus_keep_ghost)]
            proof_with! { Tracked(world) }
            write_single_input_source(
                &mut stdout,
                input_source_vec
                    .pop()
                    .expect("input_source_vec_len was checked to be exactly one"),
                line_ending_byte,
            )
        };
    }

    let line_ending_byte_array_ref = &[line_ending_byte];

    let mut delimiter_state = DelimiterState::new(&unescaped_and_encoded_delimiters);

    let mut output = Vec::new();

    if serial {
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                serial, world.valid(), world.names() == names, world.ending() == line_ending_byte,
                world.session() == session, paste_proof::writer_session(&stdout) == session,
                line_ending_byte_array_ref@ == seq![line_ending_byte],
                input_source_vec_len == names.len(), input_source_vec.len() == input_source_vec_len,
                paste_proof::source_ids(input_source_vec@) == paste_proof::ids(names),
                forall|j: int| 0 <= j < input_source_vec.len() ==> paste_proof::source_session(#[trigger] input_source_vec@[j]) == session,
                world.output() + paste_proof::serial_output(world.records(), paste_proof::ids(names),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), line_ending_byte, i as int) == target,
                delimiter_state.matches(paste_proof::delimiters(unescaped_and_encoded_delimiters@), 0),
        ))]
        for i in 0..input_source_vec_len {
            let input_source = &mut input_source_vec[i];
            output.clear();
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost pool = world.records();
                let ghost id = paste_proof::source_id(*input_source);
                let ghost records = pool[id];
                let ghost prefix = world.output();
                let ghost mut position = 0int;
                paste_proof::record_bound(records, line_ending_byte);
                assert(id == paste_proof::ids(names)[i as int]);
                assert(pool.update(id, records.skip(0)) =~= pool);
            }

            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant
                    world.valid(), world.names() == names, world.ending() == line_ending_byte,
                    world.session() == session, paste_proof::writer_session(&stdout) == session,
                    paste_proof::source_session(*input_source) == session,
                    line_ending_byte_array_ref@ == seq![line_ending_byte],
                    world.output() == prefix, paste_proof::source_id(*input_source) == id,
                    0 <= id < pool.len(), records == pool[id], 0 <= position <= records.len(),
                    world.records() == pool.update(id, records.skip(position)),
                    output@ == paste_trusted::proof::buffered_prefix(paste_proof::lines(records, line_ending_byte),
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), position),
                    delimiter_state.matches(paste_proof::delimiters(unescaped_and_encoded_delimiters@), position),
                    position > 0 ==> delimiter_state.trailing_len()
                        == paste_trusted::proof::delimiter_at(paste_proof::delimiters(unescaped_and_encoded_delimiters@), position - 1).len(),
                ensures position == records.len(),
                decreases records.len() - position,
            ))]
            while let read @ 1.. = {
                #[cfg(verus_keep_ghost)]
                proof_with! { Tracked(&mut *world) }
                input_source.read_until(line_ending_byte, &mut output)?
            } {
                #[cfg(verus_keep_ghost)]
                proof! {
                    paste_proof::line_at(records, line_ending_byte, position);
                    paste_proof::advance(pool, id, position);
                    paste_proof::strip_appended(paste_trusted::proof::buffered_prefix(
                        paste_proof::lines(records, line_ending_byte), paste_proof::delimiters(unescaped_and_encoded_delimiters@), position),
                        records[position], line_ending_byte);
                }
                remove_trailing_line_ending_byte(line_ending_byte, read, &mut output);
                #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(paste_proof::delimiters(unescaped_and_encoded_delimiters@)), Ghost(position)))]
                delimiter_state.write_delimiter(&mut output);
                #[cfg(verus_keep_ghost)]
                proof! { position = position + 1; }
            }

            #[cfg(verus_keep_ghost)]
            proof! {
                assert(position == records.len());
                assert(world.records() =~= pool.update(id, Seq::<Seq<u8>>::empty()));
                assert(prefix + paste_proof::serial_output(pool, paste_proof::ids(names),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), line_ending_byte, i as int) == target);
                paste_trusted::proof::serial_buffers_match(paste_proof::lines(records, line_ending_byte),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), position);
                if position > 0 {
                    paste_trusted::proof::buffered_has_trailing_delimiter(paste_proof::lines(records, line_ending_byte),
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), position);
                }
            }

            delimiter_state.remove_trailing_delimiter(&mut output);

            #[cfg(verus_keep_ghost)]
            proof! {
                assert(output@ == paste_trusted::proof::joined_prefix(paste_proof::lines(records, line_ending_byte),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), position));
                assert(world.output() == prefix);
                assert(line_ending_byte_array_ref@ == seq![line_ending_byte]);
            }

            #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
            paste_trusted::write_all(&mut stdout, &output)?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(world.output() == prefix + output@); }
            #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
            paste_trusted::write_all(&mut stdout, line_ending_byte_array_ref)?;

            #[cfg(verus_keep_ghost)]
            proof! {
                assert(world.output() == prefix + paste_trusted::proof::joined_prefix(paste_proof::lines(records, line_ending_byte),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), position).push(line_ending_byte));
                assert(world.output() + paste_proof::serial_output(world.records(), paste_proof::ids(names),
                    paste_proof::delimiters(unescaped_and_encoded_delimiters@), line_ending_byte, i as int + 1) == target);
            }

            // In serial mode each input file is concatenated onto its own
            // output line, so the delimiter list has to restart from its first
            // element for the next file rather than carrying the cycle over.
            #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(paste_proof::delimiters(unescaped_and_encoded_delimiters@)), Ghost(position)))]
            delimiter_state.reset_to_first_delimiter();
        }
    } else {
        let mut eof = vec![false; input_source_vec_len];
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost mut fuel = paste_proof::total(world.records(), world.records().len() as int) as int + 1; }

        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant !serial,
                world.valid(), world.names() == names, world.ending() == line_ending_byte,
                world.session() == session, paste_proof::writer_session(&stdout) == session,
                input_source_vec_len == input_source_vec.len(), input_source_vec_len == names.len(),
                paste_proof::source_ids(input_source_vec@) == paste_proof::ids(names),
                forall|j: int| 0 <= j < input_source_vec.len() ==> paste_proof::source_session(#[trigger] input_source_vec@[j]) == session,
                line_ending_byte_array_ref@ == seq![line_ending_byte],
                eof.len() == input_source_vec_len,
                forall|j: int| 0 <= j < eof.len() && #[trigger] eof@[j] ==>
                    world.records()[paste_proof::ids(names)[j]].len() == 0,
                fuel > paste_proof::total(world.records(), world.records().len() as int),
            invariant_except_break delimiter_state.matches(paste_proof::delimiters(unescaped_and_encoded_delimiters@), 0),
                world.output() + paste_proof::parallel_output(world.records(), paste_proof::ids(names),
                paste_proof::delimiters(unescaped_and_encoded_delimiters@), line_ending_byte, fuel) == target,
            ensures world.output() == target, world.valid(), world.names() == names, world.ending() == line_ending_byte,
                world.session() == session,
            decreases fuel,
        ))]
        loop {
            output.clear();
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost pool = world.records(); let ghost prefix = world.output(); }

            let mut eof_count = 0;

            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant !serial,
                    world.valid(), world.names() == names, world.ending() == line_ending_byte, world.output() == prefix,
                    world.session() == session, paste_proof::writer_session(&stdout) == session,
                    input_source_vec_len == input_source_vec.len(), input_source_vec_len == names.len(),
                    paste_proof::source_ids(input_source_vec@) == paste_proof::ids(names),
                    forall|j: int| 0 <= j < input_source_vec.len() ==> paste_proof::source_session(#[trigger] input_source_vec@[j]) == session,
                    eof.len() == input_source_vec_len,
                    forall|j: int| 0 <= j < eof.len() && #[trigger] eof@[j] ==>
                        world.records()[paste_proof::ids(names)[j]].len() == 0,
                    paste_proof::valid_ids(paste_proof::ids(names), pool),
                    world.records() == paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int).0,
                    paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int).1.len() == i,
                    output@ == paste_trusted::proof::buffered_prefix(paste_trusted::proof::row_records(
                        paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int).1),
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), i as int),
                    eof_count == paste_proof::none_count(paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int).1, i as int),
                    0 <= eof_count <= i,
                    delimiter_state.matches(paste_proof::delimiters(unescaped_and_encoded_delimiters@), i as int),
                    i > 0 ==> delimiter_state.trailing_len() == paste_trusted::proof::delimiter_at(
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), i as int - 1).len(),
                    paste_proof::total(world.records(), world.records().len() as int) <= paste_proof::total(pool, pool.len() as int),
                    paste_proof::any_record(paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int).1) ==>
                        paste_proof::total(world.records(), world.records().len() as int) < paste_proof::total(pool, pool.len() as int),
            ))]
            for i in 0..input_source_vec_len {
                let input_source = &mut input_source_vec[i];
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost prior = world.records();
                    let ghost prior_eof = eof@;
                    let ghost id = paste_proof::source_id(*input_source);
                    let ghost before = paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, i as int);
                    paste_proof::row_next(pool, paste_proof::ids(names), line_ending_byte, i as int);
                    paste_proof::row_length(pool, paste_proof::ids(names), line_ending_byte, i as int);
                    assert(id == paste_proof::ids(names)[i as int]);
                }
                if eof[i] {
                    eof_count += 1;
                } else {
                    match {
                        #[cfg(verus_keep_ghost)]
                        proof_with! { Tracked(&mut *world) }
                        input_source.read_until(line_ending_byte, &mut output)?
                    } {
                        0 => {
                            eof[i] = true;
                            eof_count += 1;
                        }
                        read => {
                            #[cfg(verus_keep_ghost)]
                            proof! { paste_proof::strip_appended(paste_trusted::proof::buffered_prefix(
                            paste_trusted::proof::row_records(before.1), paste_proof::delimiters(unescaped_and_encoded_delimiters@), i as int),
                            prior[id][0], line_ending_byte); }
                            remove_trailing_line_ending_byte(line_ending_byte, read, &mut output);
                        }
                    }
                }

                #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(paste_proof::delimiters(unescaped_and_encoded_delimiters@)), Ghost(i as int)))]
                delimiter_state.write_delimiter(&mut output);
                #[cfg(verus_keep_ghost)]
                proof! {
                    paste_proof::record_progress(prior, id, line_ending_byte);
                    let next = if prior[id].len() == 0 { None } else { Some(paste_trusted::proof::strip_record(
                        prior[id][0], line_ending_byte, prior[id][0].len() as int, cfg!(windows))) };
                    paste_trusted::proof::row_push(before.1, next);
                    paste_trusted::proof::append_models(paste_trusted::proof::row_records(before.1),
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), match next { Some(bytes) => bytes, None => Seq::empty() });
                    assert forall|j: int| 0 <= j < eof.len() && #[trigger] eof@[j] implies
                        world.records()[paste_proof::ids(names)[j]].len() == 0 by {
                        if j != i as int { assert(prior_eof[j]); }
                    }
                }
            }

            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost row = paste_proof::row_step(pool, paste_proof::ids(names), line_ending_byte, input_source_vec_len as int).1;
                paste_proof::all_none(row);
            }

            if eof_count == input_source_vec_len {
                #[cfg(verus_keep_ghost)]
                proof! { assert(world.output() == target); }
                break;
            }

            #[cfg(verus_keep_ghost)]
            proof! {
                paste_trusted::proof::parallel_row_matches(row, paste_proof::delimiters(unescaped_and_encoded_delimiters@));
                if input_source_vec_len > 0 {
                    paste_trusted::proof::buffered_has_trailing_delimiter(paste_trusted::proof::row_records(row),
                        paste_proof::delimiters(unescaped_and_encoded_delimiters@), input_source_vec_len as int);
                }
            }

            delimiter_state.remove_trailing_delimiter(&mut output);

            #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
            paste_trusted::write_all(&mut stdout, &output)?;
            #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
            paste_trusted::write_all(&mut stdout, line_ending_byte_array_ref)?;

            // Quote:
            //     When the -s option is not specified:
            //     [...]
            //     The delimiter shall be reset to the first element of list after each file operand is processed.
            // https://pubs.opengroup.org/onlinepubs/9799919799/utilities/paste.html
            #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(paste_proof::delimiters(unescaped_and_encoded_delimiters@)), Ghost(input_source_vec_len as int)))]
            delimiter_state.reset_to_first_delimiter();
            #[cfg(verus_keep_ghost)]
            proof! { fuel = fuel - 1; }
        }
    }

    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(world): Tracked<&World>,
    requires world.valid(), world.names() == filenames@,
    ensures (result is Ok) == paste_proof::opened(filenames@),
        result is Ok ==> result->Ok_0.len() == filenames.len()
            && paste_proof::source_ids(result->Ok_0@) == paste_proof::ids(filenames@)
            && forall|j: int| 0 <= j < result->Ok_0.len() ==>
                paste_proof::source_session(#[trigger] result->Ok_0@[j]) == world.session(),
))]
pub(crate) fn open_inputs(filenames: Vec<OsString>) -> UResult<Vec<InputSource>> {
    let stdin_once_cell = OnceCell::<Rc<RefCell<Stdin>>>::new();
    let mut input_source_vec = Vec::with_capacity(filenames.len());

    for filename in filenames {
        let input_source = if paste_trusted::filename_is_stdin(&filename) {
            InputSource::StandardInput(
                stdin_once_cell
                    .get_or_init(|| Rc::new(RefCell::new(stdin())))
                    .clone(),
            )
        } else {
            let file = paste_trusted::open_file(&filename)?;
            InputSource::File(BufReader::new(file))
        };
        input_source_vec.push(input_source);
    }

    Ok(input_source_vec)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    with Tracked(world): Tracked<&mut World>,
    requires old(world).valid(), old(world).ending() == line_ending_byte,
        paste_proof::writer_session(old(writer)) == old(world).session(),
        paste_proof::source_session(input_source) == old(world).session(),
        0 <= paste_proof::source_id(input_source) < old(world).records().len(),
    ensures final(world).valid(),
        final(world).names() == old(world).names(), final(world).ending() == old(world).ending(),
        final(world).session() == old(world).session(),
        paste_proof::writer_session(final(writer)) == paste_proof::writer_session(old(writer)),
        final(world).output() == old(world).output() + paste_proof::normalized(
            paste_proof::flat(old(world).records()[paste_proof::source_id(input_source)]), line_ending_byte),
))]
fn write_single_input_source(
    writer: &mut impl Write,
    mut input_source: InputSource,
    line_ending_byte: u8,
) -> UResult<()> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost names = world.names();
        let ghost session = world.session();
        let ghost id = paste_proof::source_id(input_source);
        let ghost bytes = paste_proof::flat(world.records()[id]);
        let ghost prefix = world.output();
        let ghost mut consumed = 0int;
        let ghost mut records = world.records()[id];
    }
    let mut buffer = [0_u8; 8 * 1024];
    let mut has_data = false;
    let mut last_byte = line_ending_byte;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant world.valid(), world.names() == names, world.ending() == line_ending_byte,
            world.session() == session, paste_proof::writer_session(writer) == session,
            paste_proof::source_session(input_source) == session,
            0 <= id < world.records().len(), paste_proof::source_id(input_source) == id,
            0 <= consumed <= bytes.len(),
            paste_proof::flat(world.records()[id]) == bytes.skip(consumed),
            world.output() == prefix + bytes.take(consumed),
            has_data == (consumed > 0),
            last_byte == if consumed > 0 { bytes[consumed - 1] } else { line_ending_byte },
        ensures consumed == bytes.len(),
        decreases bytes.len() - consumed,
    ))]
    while let bytes_read @ 1.. = {
        #[cfg(verus_keep_ghost)]
        proof! { records = world.records()[id]; }
        #[cfg(verus_keep_ghost)]
        proof_with! { Tracked(&mut *world) }
        input_source.read(&mut buffer)?
    } {
        #[cfg(verus_keep_ghost)]
        proof! {
            paste_proof::drop_flat(records, bytes_read as int);
            paste_proof::byte_step(bytes, consumed, bytes_read as int);
        }
        has_data = true;
        last_byte = buffer[bytes_read - 1];

        #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
        paste_trusted::write_all(writer, &buffer[..bytes_read])?;
        #[cfg(verus_keep_ghost)]
        proof! { consumed = consumed + bytes_read; }
    }

    if has_data && last_byte != line_ending_byte {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(&mut *world)))]
        paste_trusted::write_all(writer, &[line_ending_byte])?;
    }

    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result is Ok) == (paste_proof::parsed(*delimiters) is Some),
        result is Ok ==> result->Ok_0@ == paste_proof::parsed(*delimiters)->Some_0,
))]
pub(crate) fn parse_delimiters(delimiters: &OsString) -> UResult<Box<[Box<[u8]>]>> {
    #[cfg(not(verus_keep_ghost))]
    let bytes = uucore::os_str_as_bytes(delimiters)?;
    #[cfg(verus_keep_ghost)]
    let bytes = uucore::os_str_as_bytes(delimiters).map_err(std::io::Error::other)?;
    let mut vec = Vec::<Box<[u8]>>::with_capacity(bytes.len());
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i += 1;
            if i >= bytes.len() {
                #[cfg(not(verus_keep_ghost))]
                return Err(USimpleError::new(
                    1,
                    translate!("paste-error-delimiter-unescaped-backslash", "delimiters" => delimiters.to_string_lossy()),
                ));
                #[cfg(verus_keep_ghost)]
                return Err(std::io::Error::other(
                    "delimiter list ends with an unescaped backslash",
                ));
            }
            match bytes[i] {
                b'0' => vec.push(Box::new([])),
                b'\\' => vec.push(Box::new(*b"\\")),
                b'n' => vec.push(Box::new(*b"\n")),
                b't' => vec.push(Box::new(*b"\t")),
                b'b' => vec.push(Box::new(*b"\x08")),
                b'f' => vec.push(Box::new(*b"\x0C")),
                b'r' => vec.push(Box::new(*b"\r")),
                b'v' => vec.push(Box::new(*b"\x0B")),
                _ => {
                    // Unknown escape: strip backslash, use the following character(s)
                    let remaining = &bytes[i..];
                    let len = mb_char_len(remaining);
                    vec.push(Box::from(&bytes[i..i + len]));
                    i += len;
                    continue;
                }
            }
            i += 1;
        } else {
            let remaining = &bytes[i..];
            let len = mb_char_len(remaining);
            vec.push(Box::from(&bytes[i..i + len]));
            i += len;
        }
    }

    Ok(vec.into_boxed_slice())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == paste_trusted::proof::strip_record(
        old(output)@, line_ending_byte, read as int, cfg!(windows)),
))]
fn remove_trailing_line_ending_byte(line_ending_byte: u8, read: usize, output: &mut Vec<u8>) {
    if paste_trusted::pop_if_eq(output, line_ending_byte).is_none() {
        return;
    }

    if cfg!(windows) && line_ending_byte == b'\n' && read > 1 {
        let _ = paste_trusted::pop_if_eq(output, b'\r');
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
enum DelimiterState<'a> {
    NoDelimiters,
    OneDelimiter(&'a [u8]),
    MultipleDelimiters {
        current_delimiter: &'a [u8],
        delimiters: &'a [Box<[u8]>],
        delimiters_iterator: Cycle<Iter<'a, Box<[u8]>>>,
    },
}

#[cfg(verus_keep_ghost)]
verus! {
impl<'a> DelimiterState<'a> {
    spec fn valid(&self) -> bool {
        match self {
            Self::MultipleDelimiters { delimiters, delimiters_iterator, .. } =>
                delimiters@.len() > 1
                    && paste_trusted::cycle_values(delimiters_iterator).len() == delimiters@.len(),
            _ => true,
        }
    }

    spec fn next_bytes(&self) -> Seq<u8> {
        match self {
            Self::NoDelimiters => Seq::empty(),
            Self::OneDelimiter(delimiter) => delimiter@,
            Self::MultipleDelimiters { delimiters_iterator, .. } =>
                paste_trusted::cycle_values(delimiters_iterator)[0]@,
        }
    }

    spec fn trailing_len(&self) -> nat {
        match self {
            Self::NoDelimiters => 0,
            Self::OneDelimiter(delimiter) => delimiter@.len(),
            Self::MultipleDelimiters { current_delimiter, .. } => current_delimiter@.len(),
        }
    }

    spec fn matches(&self, ds: Seq<Seq<u8>>, n: int) -> bool {
        &&& self.valid()
        &&& n >= 0
        &&& self.next_bytes() == paste_trusted::proof::delimiter_at(ds, n)
        &&& match self {
            Self::NoDelimiters => forall|i: int| 0 <= i < ds.len() ==> #[trigger] ds[i] == Seq::<u8>::empty(),
            Self::OneDelimiter(delimiter) => ds == seq![delimiter@],
            Self::MultipleDelimiters { delimiters, delimiters_iterator, .. } =>
                ds == paste_proof::delimiters(delimiters@)
                && forall|k: int| 0 <= k < ds.len() ==>
                    #[trigger] paste_trusted::cycle_values(delimiters_iterator)[k]@
                        == paste_trusted::proof::delimiter_at(ds, n + k),
        }
    }
}
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl<'a> DelimiterState<'a> {
    #[cfg_attr(verus_keep_ghost, allow(unused, verus_impl_method_marker))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.valid(),
            result.matches(paste_proof::delimiters(unescaped_and_encoded_delimiters@), 0),
            result.next_bytes() == if unescaped_and_encoded_delimiters.len() > 0 {
                unescaped_and_encoded_delimiters@[0]@
            } else { Seq::<u8>::empty() },
    ))]
    fn new(unescaped_and_encoded_delimiters: &'a [Box<[u8]>]) -> Self {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost ds = paste_proof::delimiters(unescaped_and_encoded_delimiters@);
            assert forall|k: int| 0 <= k < ds.len() implies
                unescaped_and_encoded_delimiters@[k]@ == #[trigger] paste_trusted::proof::delimiter_at(ds, k) by {
                vstd::arithmetic::div_mod::lemma_small_mod(k as nat, ds.len());
            }
        }
        if unescaped_and_encoded_delimiters.is_empty() {
            DelimiterState::NoDelimiters
        } else if unescaped_and_encoded_delimiters.len() == 1 {
            let only_delimiter = &unescaped_and_encoded_delimiters[0];
            // -d '\0' is equivalent to -d ''
            if only_delimiter.is_empty() {
                DelimiterState::NoDelimiters
            } else {
                #[cfg(verus_keep_ghost)]
                proof! { assert(paste_proof::delimiters(unescaped_and_encoded_delimiters@) =~= seq![only_delimiter@]); }
                DelimiterState::OneDelimiter(only_delimiter)
            }
        } else {
            DelimiterState::MultipleDelimiters {
                current_delimiter: &unescaped_and_encoded_delimiters[0],
                delimiters: unescaped_and_encoded_delimiters,
                delimiters_iterator: paste_trusted::delimiter_cycle(
                    unescaped_and_encoded_delimiters,
                ),
            }
        }
    }

    /// This should only be used to return to the start of the delimiter list after a file has been processed.
    /// This is a no-op unless there are multiple delimiters.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        with Ghost(ds): Ghost<Seq<Seq<u8>>>, Ghost(n): Ghost<int>,
        requires old(self).matches(ds, n),
        ensures final(self).matches(ds, 0),
    ))]
    fn reset_to_first_delimiter(&mut self) {
        if let DelimiterState::MultipleDelimiters {
            delimiters_iterator,
            delimiters,
            ..
        } = self
        {
            *delimiters_iterator = paste_trusted::delimiter_cycle(delimiters);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|k: int| 0 <= k < ds.len() implies
                    #[trigger] paste_trusted::cycle_values(delimiters_iterator)[k]@
                        == paste_trusted::proof::delimiter_at(ds, k) by {
                    vstd::arithmetic::div_mod::lemma_small_mod(k as nat, ds.len());
                }
            }
        }
    }

    /// Remove the trailing delimiter.
    /// If there are no delimiters, this is a no-op.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(output).len() == 0 || old(self).trailing_len() <= old(output).len(),
        ensures final(output)@ == paste_trusted::proof::drop_suffix(
            old(output)@, old(self).trailing_len() as int),
            final(self).trailing_len() == old(self).trailing_len(),
            *final(self) == *old(self),
    ))]
    fn remove_trailing_delimiter(&mut self, output: &mut Vec<u8>) {
        let delimiter_length = match self {
            DelimiterState::OneDelimiter(only_delimiter) => only_delimiter.len(),
            DelimiterState::MultipleDelimiters {
                current_delimiter, ..
            } => current_delimiter.len(),
            DelimiterState::NoDelimiters => {
                return;
            }
        };

        // `delimiter_length` will be zero if the current delimiter is a "\0" delimiter
        if delimiter_length > 0 {
            let output_len = output.len();

            if let Some(output_without_delimiter_length) = output_len.checked_sub(delimiter_length)
            {
                output.truncate(output_without_delimiter_length);
            } else {
                // This branch is NOT unreachable, must be skipped
                // `output` should be empty in this case
                #[cfg(not(verus_keep_ghost))]
                assert_eq!(output_len, 0);
                #[cfg(verus_keep_ghost)]
                proof! { assert(output_len == 0); }
            }
        }
    }

    /// Append the current delimiter to `output`.
    /// If there are no delimiters, this is a no-op.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        with Ghost(ds): Ghost<Seq<Seq<u8>>>, Ghost(n): Ghost<int>,
        requires old(self).matches(ds, n),
        ensures final(self).matches(ds, n + 1),
            final(output)@ == old(output)@ + old(self).next_bytes(),
            final(self).trailing_len() == old(self).next_bytes().len(),
    ))]
    fn write_delimiter(&mut self, output: &mut Vec<u8>) {
        match self {
            DelimiterState::OneDelimiter(only_delimiter) => {
                output.extend_from_slice(only_delimiter);
            }
            DelimiterState::MultipleDelimiters {
                current_delimiter,
                delimiters_iterator,
                ..
            } => {
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost previous = paste_trusted::cycle_values(delimiters_iterator); }
                // Unwrap because `delimiters_iterator` is a cycle iter and was created from a non-empty slice
                let bo = paste_trusted::delimiter_next(delimiters_iterator).unwrap();

                output.extend_from_slice(bo);

                *current_delimiter = bo;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|k: int| 0 <= k < ds.len() implies
                        #[trigger] paste_trusted::cycle_values(delimiters_iterator)[k]@
                            == paste_trusted::proof::delimiter_at(ds, n + 1 + k) by {
                        if k + 1 < ds.len() {
                            assert(previous[k + 1]@ == paste_trusted::proof::delimiter_at(ds, n + k + 1));
                        } else {
                            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(n, ds.len() as int);
                            assert(previous[0]@ == paste_trusted::proof::delimiter_at(ds, n));
                        }
                    }
                }
            }
            DelimiterState::NoDelimiters => {}
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum InputSource {
    File(BufReader<File>),
    StandardInput(Rc<RefCell<Stdin>>),
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
impl InputSource {
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with Tracked(world): Tracked<&mut World>,
        requires old(world).valid(), old(buf).len() > 0,
            paste_proof::source_session(*old(self)) == old(world).session(),
            0 <= paste_proof::source_id(*old(self)) < old(world).records().len(),
        ensures result is Ok, final(world).valid(),
            paste_proof::source_id(*final(self)) == paste_proof::source_id(*old(self)),
            paste_proof::source_session(*final(self)) == paste_proof::source_session(*old(self)),
            final(world).session() == old(world).session(),
            final(world).names() == old(world).names(),
            final(world).ending() == old(world).ending(),
            final(world).output() == old(world).output(),
            result->Ok_0 <= old(buf).len(),
            result->Ok_0 <= paste_proof::flat(old(world).records()[paste_proof::source_id(*old(self))]).len(),
            (result->Ok_0 == 0) == (paste_proof::flat(old(world).records()[paste_proof::source_id(*old(self))]).len() == 0),
            final(buf)@.take(result->Ok_0 as int) == paste_proof::flat(old(world).records()[paste_proof::source_id(*old(self))]).take(result->Ok_0 as int),
            final(world).records() == old(world).records().update(paste_proof::source_id(*old(self)),
                paste_proof::drop_bytes(old(world).records()[paste_proof::source_id(*old(self))], result->Ok_0 as int)),
    ))]
    fn read(&mut self, buf: &mut [u8]) -> UResult<usize> {
        let us = match self {
            Self::File(bu) => bu.read(buf)?,
            Self::StandardInput(rc) => rc
                .try_borrow()
                .map_err(|bo| {
                    #[cfg(not(verus_keep_ghost))]
                    {
                        USimpleError::new(1, translate!("paste-error-stdin-borrow", "error" => bo))
                    }
                    #[cfg(verus_keep_ghost)]
                    {
                        std::io::Error::other(bo.to_string())
                    }
                })?
                .lock()
                .read(buf)?,
        };

        Ok(us)
    }

    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        with Tracked(world): Tracked<&mut World>,
        requires old(world).valid(), byte == old(world).ending(),
            paste_proof::source_session(*old(self)) == old(world).session(),
            0 <= paste_proof::source_id(*old(self)) < old(world).records().len(),
        ensures result is Ok, final(world).valid(),
            paste_proof::source_id(*final(self)) == paste_proof::source_id(*old(self)),
            paste_proof::source_session(*final(self)) == paste_proof::source_session(*old(self)),
            final(world).session() == old(world).session(),
            final(world).names() == old(world).names(),
            final(world).ending() == old(world).ending(),
            final(world).output() == old(world).output(),
            final(world).records() == paste_proof::after_record(*old(world), paste_proof::source_id(*old(self))),
            if old(world).records()[paste_proof::source_id(*old(self))].len() == 0 {
                result->Ok_0 == 0 && final(buf)@ == old(buf)@
            } else {
                result->Ok_0 == old(world).records()[paste_proof::source_id(*old(self))][0].len()
                    && final(buf)@ == old(buf)@ + old(world).records()[paste_proof::source_id(*old(self))][0]
            },
    ))]
    pub(crate) fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> UResult<usize> {
        let us = match self {
            Self::File(bu) => bu.read_until(byte, buf)?,
            Self::StandardInput(rc) => rc
                .try_borrow()
                .map_err(|bo| {
                    #[cfg(not(verus_keep_ghost))]
                    {
                        USimpleError::new(1, translate!("paste-error-stdin-borrow", "error" => bo))
                    }
                    #[cfg(verus_keep_ghost)]
                    {
                        std::io::Error::other(bo.to_string())
                    }
                })?
                .lock()
                .read_until(byte, buf)?,
        };

        Ok(us)
    }
}
