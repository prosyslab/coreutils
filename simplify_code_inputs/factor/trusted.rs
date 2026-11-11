#[cfg(verus_keep_ghost)]
use std::io::{BufRead, Write};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOsString(::std::ffi::OsString);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUtf8Error(::std::str::Utf8Error);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExParseInt(::std::num::ParseIntError);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExParseBigInt(::num_bigint::ParseBigIntError);
#[verifier::external_trait_specification]
pub trait ExFromStr: Sized {
    type ExternalTraitSpecificationFor: ::std::str::FromStr;
    type Err;
}
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBigUint(::num_bigint::BigUint);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
pub struct ExWriter<W: ?Sized + std::io::Write>(::std::io::BufWriter<W>);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExReader<R: ?Sized>(::std::io::BufReader<R>);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExSplit<R>(::std::io::Split<R>);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
pub struct ExIntoError<W>(::std::io::IntoInnerError<W>);

pub assume_specification<R: std::io::Read> [::std::io::BufReader::<R>::new](input: R) -> std::io::BufReader<R>;
pub assume_specification<W: std::io::Write> [::std::io::BufWriter::<W>::with_capacity](capacity: usize, output: W) -> std::io::BufWriter<W>;
pub assume_specification<W: std::io::Write> [::std::io::BufWriter::<W>::into_inner](writer: std::io::BufWriter<W>) -> Result<W, std::io::IntoInnerError<std::io::BufWriter<W>>>;
pub assume_specification<W: ?Sized + std::io::Write> [::std::io::BufWriter::<W>::flush](output: &mut std::io::BufWriter<W>) -> std::io::Result<()>;
pub assume_specification [::num_prime::nt_funcs::factorize64](value: u64) -> std::collections::BTreeMap<u64, usize>;
pub assume_specification [::num_prime::nt_funcs::factorize128](value: u128) -> std::collections::BTreeMap<u128, usize>;
pub assume_specification [::std::primitive::str::from_utf8](bytes: &[u8]) -> Result<&str, std::str::Utf8Error>;
pub assume_specification<F: std::str::FromStr> [::std::primitive::str::parse](text: &str) -> Result<F, F::Err>;
pub assume_specification [::std::primitive::str::trim](text: &str) -> &str;
pub assume_specification [::std::primitive::str::repeat](text: &str, n: usize) -> String;
pub assume_specification [::std::string::String::as_bytes](text: &String) -> &[u8];
}
