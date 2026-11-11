#[cfg(verus_keep_ghost)]
use std::io::Write;
#[cfg(verus_keep_ghost)]
use std::ops::{Add, Deref};
#[cfg(verus_keep_ghost)]
use num_traits::{ToPrimitive, Zero};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOsString(::std::ffi::OsString);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOsStr(::std::ffi::OsStr);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDecimal(::uucore::extendedbigdecimal::ExtendedBigDecimal);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBigUint(::num_bigint::BigUint);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFloat(::uucore::format::num_format::Float);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(F)]
#[verifier::reject_recursive_types(T)]
pub struct ExFormat<F: uucore::format::num_format::Formatter<T>, T>(::uucore::format::Format<F, T>);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
pub struct ExWriter<W: ?Sized + std::io::Write>(::std::io::BufWriter<W>);
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
pub struct ExIntoError<W>(::std::io::IntoInnerError<W>);

#[verifier::external_trait_specification]
pub trait ExZero: Sized + std::ops::Add<Self, Output = Self> {
    type ExternalTraitSpecificationFor: ::num_traits::Zero;
    fn zero() -> Self;
    fn is_zero(&self) -> bool;
}
#[verifier::external_trait_specification]
pub trait ExToPrimitive { type ExternalTraitSpecificationFor: ::num_traits::ToPrimitive; }
#[verifier::external_trait_specification]
pub trait ExFormatter<T> { type ExternalTraitSpecificationFor: ::uucore::format::num_format::Formatter<T>; }

pub assume_specification [::std::ffi::OsString::as_os_str](value: &std::ffi::OsString) -> &std::ffi::OsStr;
pub assume_specification [::std::ffi::OsString::deref](value: &std::ffi::OsString) -> &std::ffi::OsStr;
pub assume_specification [::std::ffi::OsString::clone](value: &std::ffi::OsString) -> std::ffi::OsString;
pub assume_specification [::std::ffi::OsStr::as_encoded_bytes](value: &std::ffi::OsStr) -> &[u8];
pub assume_specification [::std::ffi::OsStr::len](value: &std::ffi::OsStr) -> usize;
pub assume_specification<T: std::ops::Deref> [::std::option::Option::<T>::as_deref](value: &Option<T>) -> Option<&T::Target>;
pub assume_specification [::std::string::String::len](value: &String) -> usize;
pub assume_specification [::std::string::String::as_bytes](value: &String) -> &[u8];
pub assume_specification<W: std::io::Write> [::std::io::BufWriter::<W>::new](writer: W) -> std::io::BufWriter<W>;
pub assume_specification<W: std::io::Write> [::std::io::BufWriter::<W>::into_inner](writer: std::io::BufWriter<W>)
    -> Result<W, std::io::IntoInnerError<std::io::BufWriter<W>>>;
pub assume_specification<W: ?Sized + std::io::Write> [::std::io::BufWriter::<W>::flush](writer: &mut std::io::BufWriter<W>) -> std::io::Result<()>;
pub assume_specification [::uucore::extendedbigdecimal::ExtendedBigDecimal::one]() -> uucore::extendedbigdecimal::ExtendedBigDecimal;
pub assume_specification [::uucore::extendedbigdecimal::ExtendedBigDecimal::zero]() -> uucore::extendedbigdecimal::ExtendedBigDecimal;
pub assume_specification [::uucore::extendedbigdecimal::ExtendedBigDecimal::to_biguint](value: &uucore::extendedbigdecimal::ExtendedBigDecimal) -> Option<num_bigint::BigUint>;
pub assume_specification [::uucore::extendedbigdecimal::ExtendedBigDecimal::clone](value: &uucore::extendedbigdecimal::ExtendedBigDecimal) -> uucore::extendedbigdecimal::ExtendedBigDecimal;
pub assume_specification [::uucore::extendedbigdecimal::ExtendedBigDecimal::add](a: uucore::extendedbigdecimal::ExtendedBigDecimal, b: uucore::extendedbigdecimal::ExtendedBigDecimal) -> uucore::extendedbigdecimal::ExtendedBigDecimal;
pub assume_specification [::num_bigint::BigUint::to_u64](value: &num_bigint::BigUint) -> Option<u64>;
pub assume_specification [::uucore::fast_inc::fast_inc](bytes: &mut [u8], start: &mut usize, end: usize, increment: &[u8]);
pub assume_specification<F: uucore::format::num_format::Formatter<T>, T> [::uucore::format::Format::<F, T>::from_formatter](formatter: F) -> uucore::format::Format<F, T>;
}
