// This file is part of the uutils coreutils package.
//
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::io::{BufRead, Write};
type UResult<T> = std::io::Result<T>;
use crate::io_trusted;
pub trait ChunkProcessor {
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8];
}
pub trait SymbolTranslator: Sized {
    fn translate(&mut self, current: u8) -> Option<u8>;
    fn chain<T>(self, other: T) -> ChainedSymbolTranslator<Self, T>
    where
        Self: Sized,
    {
        ChainedSymbolTranslator::<Self, T> {
            stage_a: self,
            stage_b: other,
        }
    }
}
pub struct ChainedSymbolTranslator<A, B> {
    pub stage_a: A,
    pub stage_b: B,
}
impl<A: SymbolTranslator, B: SymbolTranslator> SymbolTranslator for ChainedSymbolTranslator<A, B> {
    fn translate(&mut self, current: u8) -> Option<u8> {
        match self.stage_a.translate(current) {
            Some(c) => self.stage_b.translate(c),
            None => None,
        }
    }
}
#[derive(Debug)]
pub struct DeleteOperation {
    pub keep_table: [bool; 256],
    pub single_delete: Option<u8>,
}
impl SymbolTranslator for DeleteOperation {
    fn translate(&mut self, current: u8) -> Option<u8> {
        self.keep_table[current as usize].then_some(current)
    }
}
impl ChunkProcessor for DeleteOperation {
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8] {
        use crate::simd::{process_delete, process_single_delete};
        if let Some(delete_char) = self.single_delete {
            process_single_delete(input, output, delete_char, &self.keep_table)
        } else {
            process_delete(input, output, &self.keep_table);
            output
        }
    }
}
#[derive(Debug)]
pub struct TranslateOperation {
    pub translation_table: [u8; 256],
    pub single_change: Option<(u8, u8)>,
}
impl SymbolTranslator for TranslateOperation {
    fn translate(&mut self, current: u8) -> Option<u8> {
        Some(self.translation_table[current as usize])
    }
}
impl ChunkProcessor for TranslateOperation {
    fn process_chunk<'a>(&self, input: &'a [u8], output: &'a mut Vec<u8>) -> &'a [u8] {
        use crate::simd::process_single_char_replace;
        if let Some((source, target)) = self.single_change {
            process_single_char_replace(input, output, source, target)
        } else {
            let mapper = |b: u8| self.translation_table[b as usize];
            crate::simd::extend_mapped(output, input, mapper);
            output
        }
    }
}
#[derive(Debug)]
pub struct SqueezeOperation {
    pub squeeze_table: [bool; 256],
    pub previous: Option<u8>,
}
impl SymbolTranslator for SqueezeOperation {
    fn translate(&mut self, current: u8) -> Option<u8> {
        let next = if self.squeeze_table[current as usize] {
            match self.previous {
                Some(v) if v == current => None,
                _ => Some(current),
            }
        } else {
            Some(current)
        };
        self.previous = Some(current);
        next
    }
}
pub fn translate_input<T, R, W>(input: &mut R, output: &mut W, mut translator: T) -> UResult<()>
where
    T: SymbolTranslator,
    R: BufRead,
    W: Write,
{
    const BUFFER_SIZE: usize = 32768;
    let mut buf = [0; BUFFER_SIZE];
    let mut output_buf = Vec::with_capacity(BUFFER_SIZE);
    loop {
        let length = match io_trusted::read(input, &mut buf[..]) {
            Ok(0) => {
                break;
            }
            Ok(len) => len,
            Err(e) => return Err(e),
        };
        output_buf.clear();
        for current in &buf[..length] {
            let byte = *current;
            if let Some(translated) = translator.translate(byte) {
                output_buf.push(translated);
            }
        }
        if !output_buf.is_empty() {
            crate::simd::write_output(output, &output_buf)?;
        }
    }
    Ok(())
}
