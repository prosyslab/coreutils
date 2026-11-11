use std::cmp::Ordering;
pub mod joining {
    use crate::chunks::Chunk;
    use crate::merge::{MergeInput, ReaderFile};
    use crate::trusted::concurrency::{self};
    pub trait Task: Sized + Send + 'static {
        type Output: Send + 'static;
        fn run(self) -> Self::Output;
    }
    pub type ReaderOutput = (crate::SortResult<()>,);
}
pub mod unwind {
    use crate::chunks::ChunkContents;
    use std::cmp::Ordering;
    pub trait Comparator<T> {
        fn compare(&self, a: &T, b: &T) -> Ordering;
    }
    pub trait ContentsMutator {
        type Output;
        fn run<'a>(&self, owner: &'a Vec<u8>, contents: &mut ChunkContents<'a>) -> Self::Output;
    }
}
