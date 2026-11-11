#[path = "../src/uu/tr/src/operation.rs"]
mod operation;
#[path = "../src/uu/tr/src/simd.rs"]
mod simd;
#[path = "common.rs"]
mod trusted_common;
#[path = "tr_delete.rs"]
mod trusted;
#[path = "tr_tables.rs"]
mod tr_trusted;
pub use trusted_common::io as io_trusted;
