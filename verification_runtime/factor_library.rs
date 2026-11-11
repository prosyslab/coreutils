use std::fmt::Display;

pub fn one<T: Display>(prefix: &str, value: &T, suffix: &str) -> String {
    ::std::fmt::format(format_args!("{prefix}{value}{suffix}"))
}

pub fn two<T: Display, U: Display>(prefix: &str, first: &T, separator: &str, second: &U) -> String {
    ::std::fmt::format(format_args!("{prefix}{first}{separator}{second}"))
}

pub fn invalid(text: &str) -> std::io::Error {
    ::std::io::Error::new(std::io::ErrorKind::InvalidInput, text.to_owned())
}
pub fn split<R: std::io::BufRead>(input: R, byte: u8) -> std::io::Split<R> {
    ::std::io::BufRead::split(input, byte)
}

pub fn big_factors(value: num_bigint::BigUint) -> (std::collections::BTreeMap<num_bigint::BigUint, usize>, Option<Vec<num_bigint::BigUint>>) {
    ::num_prime::nt_funcs::factors(value, None)
}

pub fn positive_overflow(error: &std::num::ParseIntError) -> bool {
    *::std::num::ParseIntError::kind(error) == std::num::IntErrorKind::PosOverflow
}

pub fn entries<T>(map: std::collections::BTreeMap<T, usize>) -> Vec<(T, usize)> {
    ::std::iter::IntoIterator::into_iter(map).collect()
}

pub fn delimiter_positions(a: u8, b: u8, c: u8, bytes: &[u8], end: usize) -> Vec<usize> {
    ::memchr::memchr3_iter(a, b, c, bytes).chain(std::iter::once(end)).collect()
}

