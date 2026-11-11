// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

#[cfg(not(target_os = "wasi"))]
mod threaded;
#[cfg(all(all(), not(target_os = "wasi")))]
pub(crate) use threaded::ReadResult;
pub(crate) use threaded::SortPipeTask;
#[cfg(not(target_os = "wasi"))]
pub use threaded::ext_sort;
#[cfg(target_os = "wasi")]
mod wasi;
#[cfg(target_os = "wasi")]
pub use self::wasi::ext_sort;
