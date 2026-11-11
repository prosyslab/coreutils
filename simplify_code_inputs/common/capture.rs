use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};

pub struct Capture {
    input: File,
    output: File,
    saved_input: File,
    saved_output: File,
}

fn memory_file() -> File {
    let fd = unsafe { ::libc::memfd_create(c"simplify-code".as_ptr(), ::libc::MFD_CLOEXEC) };
    assert!(fd >= 0);
    unsafe { File::from_raw_fd(fd) }
}

#[cfg_attr(verus_keep_ghost, vstd::prelude::verus_spec(with state: vstd::prelude::Ghost<crate::proof_common::State>,))]
pub fn begin(bytes: &[u8], initial_output: &Vec<u8>) -> Capture {
    let mut input = memory_file();
    ::std::io::Write::write_all(&mut input, bytes).unwrap();
    ::std::io::Seek::rewind(&mut input).unwrap();
    ::std::io::Write::flush(&mut ::std::io::stdout()).unwrap();
    let input_fd = unsafe { ::libc::dup(0) };
    let output_fd = unsafe { ::libc::dup(1) };
    assert!(input_fd >= 0 && output_fd >= 0);
    let mut output = memory_file();
    ::std::io::Write::write_all(&mut output, initial_output).unwrap();
    assert!(unsafe { ::libc::dup2(input.as_raw_fd(), 0) } >= 0);
    assert!(unsafe { ::libc::dup2(output.as_raw_fd(), 1) } >= 0);
    Capture {
        input, output,
        saved_input: unsafe { File::from_raw_fd(input_fd) },
        saved_output: unsafe { File::from_raw_fd(output_fd) },
    }
}

#[cfg_attr(verus_keep_ghost, vstd::prelude::verus_spec(with state: vstd::prelude::Ghost<crate::proof_common::State>,))]
pub fn finish(mut capture: Capture) -> (Vec<u8>, Vec<u8>) {
    ::std::io::Write::flush(&mut ::std::io::stdout()).unwrap();
    let mut remaining = Vec::new();
    ::std::io::Read::read_to_end(&mut ::std::io::stdin(), &mut remaining).unwrap();
    assert!(unsafe { ::libc::dup2(capture.saved_input.as_raw_fd(), 0) } >= 0);
    assert!(unsafe { ::libc::dup2(capture.saved_output.as_raw_fd(), 1) } >= 0);
    ::std::io::Seek::rewind(&mut capture.output).unwrap();
    let mut bytes = Vec::new();
    ::std::io::Read::read_to_end(&mut capture.output, &mut bytes).unwrap();
    (bytes, remaining)
}
