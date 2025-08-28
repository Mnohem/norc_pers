/// A clone that allows you to hold reference to the original value, for when you want to create
/// new, owned values, while using something else as a base to build off of.
pub trait PartialClone {
    /// Cloned must be Self, but with a smaller inner lifetime
    type Cloned<'a>
    where
        Self: 'a;
    fn partial_clone<'c>(&'c self) -> Self::Cloned<'c>;
    /// Extend the inner lifetime of a clone
    /// # Safety
    /// It is up to the caller to ensure that `clone` is valid for the resultant lifetime. Usually
    /// this function will be called after a succession.
    unsafe fn extend_inner_lifetime<'c>(clone: Self::Cloned<'c>) -> Self
    where
        Self: 'c;
}
/// This trait exists to facilitate more efficient memory usage with partial clones. When you have
/// partially cloned a value, and then wish to replace the original with that possibly modified
/// clone, there will be lifetime constraints that prevent that pattern, since the clone is still
/// borrowing from the original. A call to succeed is meant to effectively invert the dependence of
/// `clone` on `self`, to a dependence of `self` on `clone`, thus `self` can be safely dropped
/// while `clone` is still live. `PartialClone::extend_inner_lifetime` can then be used to extend
/// the lifetime of the clone.
pub trait Succeed: PartialClone {
    /// Gives ownership of shared values from `self` to `clone`
    /// # Safety
    /// Concurrent calls to `succeed` over `clone` or `self` are undefined behavior. All other
    /// use of concurrent, shared reference are allowed, such as `PersVec::get` and
    /// `PartialClone::partial_clone`. After this call, dropping `clone` before `self` is undefined
    /// behavior. It is up to the caller to manage lifetimes so that this does not happen, and
    /// consider other references to `self` that may still be live. Calling `succeed` when `clone`
    /// does not originate as a clone of `self` preserves all stated behavior.
    unsafe fn succeed<'c>(&'c self, clone: &Self::Cloned<'c>);
}

impl<T> PartialClone for T
where
    T: Copy,
{
    type Cloned<'a>
        = T
    where
        Self: 'a;

    fn partial_clone<'c>(&'c self) -> Self::Cloned<'c> {
        *self
    }
    unsafe fn extend_inner_lifetime<'c>(clone: Self::Cloned<'c>) -> Self
    where
        Self: 'c,
    {
        clone
    }
}
impl<T> Succeed for T
where
    T: Clone + PartialClone,
{
    unsafe fn succeed<'c>(&'c self, _: &Self::Cloned<'c>) {}
}

#[macro_export]
macro_rules! pers_vec_in {
    ($alloc:expr,) => {
        $crate::PersVec::new_in($alloc)
    };
    ($alloc:expr $(,[])?) => {
        $crate::PersVec::new_in($alloc)
    };
    ($alloc:expr, [$elem:expr; $n:expr]) => {{
        let mut pv = $crate::PersVec::new_in($alloc);
        for _ in 0usize..$n {
            pv = pv.append($elem.clone());
        }
        pv
    }};
    ($alloc:expr, [$($x:expr),+ $(,)?]) => {{
        $crate::PersVec::new_in($alloc)
            $(
                .append($x)
            )+
    }};
}
cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        #[macro_export]
        macro_rules! pers_vec {
            ($($args:expr),*) => {
                $crate::pers_vec_in!(allocator_api2::alloc::Global, [$($args,)*])
            };
            ($elem:expr; $n:expr) => {
                pers_vec_in!(allocator_api2::alloc::Global, [$elem; $n])
            };
        }
    } else if #[cfg(feature = "std")] {
        #[macro_export]
        macro_rules! pers_vec {
            ($($args:expr),*) => {
                pers_vec_in!(std::alloc::Global, [$($args,)*])
            };
            ($elem:expr; $n:expr) => {
                pers_vec_in!(std::alloc::Global, [$elem; $n])
            };
        }
    } else {
        #[macro_export]
        macro_rules! pers_vec {
            ($($args:expr),*) => {
                pers_vec_in!(alloc::Global, [$($args,)*])
            };
            ($elem:expr; $n:expr) => {
                pers_vec_in!(alloc::Global, [$elem; $n])
            };
        }
    }
}
