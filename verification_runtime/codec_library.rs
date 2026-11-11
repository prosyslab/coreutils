pub fn os_bytes(value: &std::ffi::OsStr) -> std::io::Result<&[u8]> {
    ::uucore::os_str_as_bytes(value).map_err(std::io::Error::other)
}

pub fn path_buf(value: &std::ffi::OsString) -> std::path::PathBuf {
    ::std::path::PathBuf::from(value)
}
