/// A clone that allows you to hold reference to the original value,
/// for when you want to create new, owned values, while using
/// something else as a base to build off of.
pub trait PartialClone {
    /// Item should be Self, but currently this can't be done in Rust
    type Item<'a>
    where
        Self: 'a;
    fn partial_clone<'b>(&'b self) -> Self::Item<'b>;
}

impl<T> PartialClone for T
where
    T: Clone,
{
    type Item<'a>
        = T
    where
        Self: 'a;

    fn partial_clone<'b>(&'b self) -> Self::Item<'b> {
        self.clone()
    }
}
