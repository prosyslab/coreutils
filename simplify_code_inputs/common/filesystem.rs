use std::ffi::OsString;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
pub use crate::trusted_common::filesystem::contents;

verus! {
pub uninterp spec fn os_bytes(name: &OsString) -> Seq<u8>;
pub uninterp spec fn descriptor<R>(reader: &R) -> int;

pub open spec fn normal_files(names: Seq<OsString>, files: Map<Seq<u8>, Seq<u8>>) -> bool {
    &&& forall|path: Seq<u8>| #[trigger] files.dom().contains(path) ==>
        contents().dom().contains(path) && files[path] == contents()[path]
    &&& forall|i: int| 0 <= i < names.len() && os_bytes(&names[i]) != seq![45u8] ==>
        files.dom().contains(os_bytes(&names[i])) && files[os_bytes(&names[i])].len() <= usize::MAX
}
}
