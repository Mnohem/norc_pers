/// A clone that allows you to hold reference to the original value,
/// for when you want to create new, owned values, while using
/// something else as a base to build off of.
pub trait PartialClone {
    /// Cloned should be Self, but currently this can't be done in Rust
    type Cloned<'a>
    where
        Self: 'a;
    fn partial_clone<'b>(&'b self) -> Self::Cloned<'b>;
}

impl<T> PartialClone for T
where
    T: Clone,
{
    type Cloned<'a>
        = T
    where
        Self: 'a;

    fn partial_clone<'b>(&'b self) -> Self::Cloned<'b> {
        self.clone()
    }
}
