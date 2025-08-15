/// A clone that allows you to hold reference to the original value,
/// for when you want to create new, owned values, while using
/// something else as a base to build off of.
pub trait PartialClone {
    /// Cloned should be Self, but currently this can't be done in Rust
    type Cloned<'a>
    where
        Self: 'a;
    fn partial_clone<'c>(&'c self) -> Self::Cloned<'c>;
}
/// A clone can "succeed" the original value when there are no references to the original besides
/// those borrowed by the given clone. This process entails freeing only that in the original
/// which isn't borrowed by the clone, and giving ownership to the clone over everything that they
/// borrow from the original.
/// This method can not be fallible as it takes ownership over the original value. It is up to the
/// implementor to ensure the clone is actually a clone of the original.
pub trait Succeed: PartialClone {
    unsafe fn succeed<'c>(self: &mut &'c Self, clone: &mut &Self::Cloned<'c>);
}

impl<T> PartialClone for T
where
    T: Clone,
{
    type Cloned<'a>
        = T
    where
        Self: 'a;

    fn partial_clone<'c>(&'c self) -> Self::Cloned<'c> {
        self.clone()
    }
}
impl<T> Succeed for T
where
    T: Clone + PartialClone,
{
    unsafe fn succeed<'c>(self: &mut &'c Self, _: &mut &Self::Cloned<'c>) {}
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
