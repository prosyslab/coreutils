pub use crate::trusted_common::io::{read, write_all};
pub use crate::trusted_common::strip_suffix;

pub fn next_line<I: Iterator<Item = std::io::Result<Vec<u8>>>>(lines: &mut I)
    -> Option<std::io::Result<Vec<u8>>>
{
    lines.next()
}
