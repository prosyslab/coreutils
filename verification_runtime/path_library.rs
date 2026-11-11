#[cfg_attr(verus_keep_ghost, verus_spec(
    requires forall|byte: u8| predicate.requires((byte,)),
))]
pub fn all<F: Fn(u8) -> bool>(bytes: &[u8], predicate: F) -> bool {
    ::std::iter::Iterator::all(&mut bytes.iter().copied(), predicate)
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires forall|byte: u8| predicate.requires((byte,)),
))]
pub fn rposition<F: Fn(u8) -> bool>(bytes: &[u8], predicate: F) -> Option<usize> {
    ::std::iter::Iterator::rposition(&mut bytes.iter().copied(), predicate)
}
