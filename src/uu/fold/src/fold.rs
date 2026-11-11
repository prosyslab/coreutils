// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::io::{BufReader, Read, Write};
type UResult<T> = std::io::Result<T>;
use crate::{fold_trusted, trusted_common::io as io_trusted};
const NL: u8 = b'\n';
pub(crate) fn fold_file_bytewise<T: Read, W: Write>(
    mut file: BufReader<T>,
    spaces: bool,
    width: usize,
    output: &mut W,
) -> UResult<()> {
    let mut line = Vec::new();
    loop {
        while line.len() <= width {
            let buf = fold_trusted::fill_buf(&mut file)?;
            if buf.is_empty() {
                break;
            }
            let len = buf.len();
            line.extend_from_slice(buf);
            fold_trusted::consume(&mut file, len);
        }
        if line.len() <= width {
            if line.is_empty() {
                break;
            }
            io_trusted::write_all(output, &line)?;
            break;
        }
        let chunk = &line[..width];
        if let Some(position) = fold_trusted::position_eq(&line[..=width], NL) {
            let end = position + 1;
            io_trusted::write_all(output, &line[..end])?;
            fold_trusted::drain_prefix(&mut line, end);
            continue;
        }
        let end = if spaces {
            match fold_trusted::last_whitespace(chunk) {
                Some(i) => i + 1,
                None => width,
            }
        } else {
            width
        };
        io_trusted::write_all(output, &line[..end])?;
        io_trusted::write_all(output, &[NL])?;
        fold_trusted::drain_prefix(&mut line, end);
    }
    Ok(())
}
