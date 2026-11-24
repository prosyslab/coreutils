pub use crate::trusted_common::io::{read, write_all};
pub use crate::trusted_common::strip_suffix;
use vstd::prelude::*;
# [cfg_attr (verus_keep_ghost , verus_spec (with state : & mut vstd :: prelude :: Ghost < crate :: proof_common :: State > ,))]
pub fn next_line<I: Iterator<Item = std::io::Result<Vec<u8>>>>(
    lines: &mut I,
) -> Option<std::io::Result<Vec<u8>>> {
    let io_result = { lines.next() };
    #[cfg(verus_keep_ghost)]
    vstd::prelude::proof! { if let Some (Ok (line)) = & io_result { let ghost before = state @ ; let ghost unread = before . remaining (0) ; let ghost n = line @ . len () ; assert (n <= unread . len ()) ; assert (line @ == unread . take (n as int)) ; let ghost consumed = if n < unread . len () && unread [n as int] == 10u8 { n + 1 } else { n } ; before . advance_valid (0 , consumed) ; * state = Ghost (before . advance (0 , consumed)) ; } }
    io_result
}
