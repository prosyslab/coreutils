#[path = "sort.rs"]
mod trusted;
#[path = "sort_callbacks.rs"]
mod proof;
#[path = "common.rs"]
mod trusted_common;
include!("../src/uu/sort/src/sort.rs");
