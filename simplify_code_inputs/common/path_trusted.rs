#[cfg(verus_keep_ghost)]
use std::ops::Deref;
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
pub struct ExNonUtf8(::uucore::NonUtf8OsStrError);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPathBuf(::std::path::PathBuf);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPath(::std::path::Path);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExComponents<'a>(::std::path::Components<'a>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExComponent<'a>(::std::path::Component<'a>);

pub assume_specification [::std::ffi::OsString::as_os_str](value: &std::ffi::OsString)
    -> &std::ffi::OsStr;
pub assume_specification [::std::ffi::OsString::deref](value: &std::ffi::OsString)
    -> &std::ffi::OsStr;
pub assume_specification [::uucore::os_str_as_bytes](value: &std::ffi::OsStr)
    -> Result<&[u8], uucore::NonUtf8OsStrError>;
pub assume_specification [::std::path::is_separator](value: char) -> bool;
pub assume_specification<T, E> [::core::result::Result::<T, E>::unwrap_or](value: Result<T, E>, fallback: T) -> T;
pub assume_specification [::std::path::PathBuf::deref](value: &std::path::PathBuf) -> &std::path::Path;
pub assume_specification [::std::path::Path::components](value: &std::path::Path) -> std::path::Components<'_>;
pub assume_specification<'a> [::std::path::Components::<'a>::next_back](value: &mut std::path::Components<'a>) -> Option<std::path::Component<'a>>;
pub assume_specification<'a> [::std::path::Component::<'a>::as_os_str](value: std::path::Component<'a>) -> &'a std::ffi::OsStr;
pub assume_specification [::std::ffi::OsStr::eq](left: &std::ffi::OsStr, right: &std::ffi::OsString) -> bool;
pub assume_specification<T, F: FnOnce(T) -> bool> [::core::option::Option::<T>::is_some_and](value: Option<T>, predicate: F) -> (result: bool)
    requires value is Some ==> predicate.requires((value->Some_0,)),
    ensures match value { Some(item) => predicate.ensures((item,), result), None => !result },
;
pub assume_specification<T, U, F: FnOnce(T) -> U> [::core::option::Option::<T>::map_or](value: Option<T>, fallback: U, mapper: F) -> (result: U)
    requires value is Some ==> mapper.requires((value->Some_0,)),
    ensures match value { Some(item) => mapper.ensures((item,), result), None => result == fallback },
;
}
