use uucore::format::{EscapeSet, EscapedChar, OctalParsing};

pub fn three_digits() -> OctalParsing {
    ::uucore::format::OctalParsing::ThreeDigits
}

pub fn escape_set() -> EscapeSet {
    ::uucore::format::EscapeSet::WithoutUnicodeAndQuote
}

pub fn escapes(bytes: &[u8], octal: OctalParsing, set: EscapeSet) -> Vec<EscapedChar> {
    ::uucore::format::parse_escape_only(bytes, octal, set).collect()
}

pub fn render_escape(item: &EscapedChar) -> std::io::Result<(Vec<u8>, bool)> {
    let mut bytes = Vec::new();
    let stop = ::uucore::format::FormatChar::write(item, &mut bytes)?.is_break();
    Ok((bytes, stop))
}
pub fn enumerate<I: Iterator>(iter: I) -> std::iter::Enumerate<I> {
    ::std::iter::Iterator::enumerate(iter)
}

