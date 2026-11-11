use uucore::extendedbigdecimal::ExtendedBigDecimal;
use uucore::format::{Format, num_format};

pub fn parse<'a>(text: &str) -> std::io::Result<Format<num_format::Float, &'a ExtendedBigDecimal>> {
    ::uucore::format::Format::parse(text).map_err(std::io::Error::other)
}

pub fn render(format: &Format<num_format::Float, &ExtendedBigDecimal>, value: &ExtendedBigDecimal)
    -> std::io::Result<Vec<u8>>
{
    let mut bytes = Vec::new();
    ::uucore::format::Format::fmt(format, &mut bytes, value)?;
    Ok(bytes)
}

pub fn decimal_formatter(width: usize, precision: usize) -> num_format::Float {
    ::uucore::format::num_format::Float {
        variant: num_format::FloatVariant::Decimal,
        width,
        alignment: num_format::NumberAlignment::RightZero,
        precision: Some(precision),
        ..Default::default()
    }
}

pub fn shortest_formatter() -> num_format::Float {
    ::uucore::format::num_format::Float {
        variant: num_format::FloatVariant::Shortest,
        ..Default::default()
    }
}
pub fn flush<W: std::io::Write>(writer: &mut W) -> std::io::Result<()> {
    ::std::io::Write::flush(writer)
}

