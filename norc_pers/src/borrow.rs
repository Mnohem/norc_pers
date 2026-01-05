use core::num::{NonZeroIsize, NonZeroUsize};
use core::pin::Pin;

use crate::boxed::Box;
use crate::{Allocator, NonNull};

/// A clone that allows you to hold reference to the original value, for when you want to create
/// new values while using something else as a base to build off of.
/// # Safety
/// `Self` and `Self::Lended<'a>` must be the same type, except the exposed lifetime `'a` may differ
/// # Purpose
/// The purpose of this trait is to allow for a cheap clone on persistent data structures.
/// # Notes
/// `Lend` is automatically implemented for `T: Copy`, which includes `&_`, and so it may be
/// necessary to disambiguate calls to `lend`.
pub unsafe trait Lend {
    /// `Self::Lended` must be `Self` but with a generic inner lifetime
    type Lended<'a>
    where
        Self: 'a;
    #[must_use]
    fn lend<'c>(&'c self) -> Self::Lended<'c>;
}
/// This trait exists to facilitate memory reclamation with lended values. When you have
/// lended a value, and then wish to replace the original with that possibly modified
/// value, lifetime constraints will prevent this, since the value is still
/// borrowing from the original that will be dropped upon replacement.
/// A call to `consign` effectively inverts the lifetime dependence of
/// `lended` on `self`, to a dependence of `self` on `lended`, thus `self` can be safely dropped
/// while `lended` is still live. `Consign::extend_inner_lifetime` can then be used to extend
/// the lifetime of the clone.
pub trait Consign: Lend {
    /// Transfers ownership of shared values from `self` to `lended`.
    /// If `self` and `lended` share nothing, this is a noop.
    /// # Safety
    /// Concurrent calls to `consign` over `lended` or `self` are undefined behavior. All other
    /// use of concurrent, shared reference are allowed, such as `PersVec::get` and
    /// `Lend::lend`. After this call, dropping `lended` before `self` is undefined
    /// behavior. It is up to the caller to manage lifetimes so that this does not happen, and
    /// consider other references to `self` that may still be live. It is undefined
    /// behavior to call this method when `self` and `lended` come from the same "lineage" of
    /// values but are not immediate lender(`self`) and lendee(`lended`).
    /// It is up to the implementor to deal with cases where `self` and `lended` are unrelated
    /// or are the same reference.
    unsafe fn consign<'c>(&'c self, lended: &Self::Lended<'c>);
    /// Extend the inner lifetime of a lended value.
    /// # Safety
    /// It is up to the caller to ensure that `lended` is valid for the resultant lifetime. Usually
    /// this function will be called after a consignment, where `Self` was the type of the lender.
    #[must_use]
    unsafe fn extend_inner_lifetime<'c>(lended: Self::Lended<'c>) -> Self
    where
        Self: 'c;
}
unsafe impl<T: Copy> Lend for T {
    type Lended<'a>
        = T
    where
        Self: 'a;
    fn lend(&self) -> Self {
        *self
    }
}

impl<T: Copy> Consign for T {
    unsafe fn consign(&self, _: &Self) {}
    unsafe fn extend_inner_lifetime<'c>(clone: Self) -> Self
    where
        Self: 'c,
    {
        clone
    }
}
/// # Safety
/// `Self` can be directly cast as a word sized pointer, and a word size pointer originating
/// as `Self` can be cast as `Self`. Implementing this for fat pointers such as `&[u8]` is
/// invalid and undefined.
pub unsafe trait WordAddress: Sized {
    type Pointee: Sized;
    fn addr(&self) -> &*const Self::Pointee {
        unsafe {
            (core::ptr::from_ref(self) as *const *const Self::Pointee)
                .as_ref()
                .unwrap_unchecked()
        }
    }
    fn into_addr(self) -> *const Self::Pointee {
        let result = *self.addr();
        core::mem::forget(self);
        result
    }
    fn reform(ptr: &*const Self::Pointee) -> &Self {
        unsafe {
            (core::ptr::from_ref(ptr) as *const Self)
                .as_ref()
                .unwrap_unchecked()
        }
    }
    fn reform_mut(ptr: &mut *const Self::Pointee) -> &mut Self {
        unsafe {
            (core::ptr::from_ref(ptr) as *const Self as *mut Self)
                .as_mut()
                .unwrap_unchecked()
        }
    }
}
// TODO swap constant for lower address platforms
/// Wrapper to create a `T` that pads the type to the word size, in order to inline elements
/// in persistent structures that support inlining.
#[repr(align(8))]
#[derive(Clone, Copy)]
pub struct FillWord<T: Copy>(T);
impl<T: Copy> FillWord<T> {
    pub const fn new(t: T) -> Self {
        // TODO swap constant for lower address platforms
        debug_assert!(size_of::<T>() < 8);
        Self(t)
    }
}
unsafe impl<T: Copy> WordAddress for FillWord<T> {
    type Pointee = ();
}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [bool; 8] {
    type Pointee = ();
}
unsafe impl WordAddress for [Option<bool>; 8] {
    type Pointee = ();
}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [u8; 8] {
    type Pointee = ();
}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [i8; 8] {
    type Pointee = ();
}
// TODO swap constant for lower address platform
unsafe impl WordAddress for [u16; 4] {
    type Pointee = ();
}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [i16; 4] {
    type Pointee = ();
}
// TODO conditional compile for higher address platforms
// unsafe impl AddressAddress for u32 {}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [u32; 2] {
    type Pointee = ();
}
// TODO conditional compile for higher address platforms
// unsafe impl AddressAddress for i32 {}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [i32; 2] {
    type Pointee = ();
}
// TODO conditional compile for higher address platforms
// unsafe impl AddressAddress for char {}
// TODO conditional compile for higher address platforms
// unsafe impl AddressAddress for Option<char> {}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [char; 2] {
    type Pointee = ();
}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [Option<char>; 2] {
    type Pointee = ();
}
// TODO conditional compile for higher address platforms
// unsafe impl AddressAddress for f32 {}
// TODO swap constant for lower address platforms
unsafe impl WordAddress for [f32; 2] {
    type Pointee = ();
}
// TODO conditional compile for lower address platforms
unsafe impl WordAddress for f64 {
    type Pointee = ();
}
// TODO conditional compile for lower address platforms
unsafe impl WordAddress for u64 {
    type Pointee = ();
}
// TODO conditional compile for lower address platforms
unsafe impl WordAddress for i64 {
    type Pointee = ();
}
unsafe impl WordAddress for usize {
    type Pointee = ();
}
unsafe impl WordAddress for isize {
    type Pointee = ();
}
unsafe impl WordAddress for NonZeroUsize {
    type Pointee = ();
}
unsafe impl WordAddress for NonZeroIsize {
    type Pointee = ();
}
unsafe impl WordAddress for Option<NonZeroUsize> {
    type Pointee = ();
}
unsafe impl WordAddress for Option<NonZeroIsize> {
    type Pointee = ();
}

unsafe impl<T: Sized, A: Allocator> WordAddress for Box<T, A> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for &T {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for &mut T {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for NonNull<T> {
    type Pointee = T;
}
unsafe impl<T: Sized, A: Allocator> WordAddress for Option<Box<T, A>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<&T> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<&mut T> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<NonNull<T>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for *const T {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for *mut T {
    type Pointee = T;
}
unsafe impl<T: Sized, A: Allocator> WordAddress for Pin<Box<T, A>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Pin<&T> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Pin<&mut T> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Pin<NonNull<T>> {
    type Pointee = T;
}
unsafe impl<T: Sized, A: Allocator> WordAddress for Option<Pin<Box<T, A>>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<Pin<&T>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<Pin<&mut T>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Option<Pin<NonNull<T>>> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Pin<*const T> {
    type Pointee = T;
}
unsafe impl<T: Sized> WordAddress for Pin<*mut T> {
    type Pointee = T;
}

pub trait CreateAddress: WordAddress {
    fn create(value: Self::Pointee) -> Self;
}
impl<T: Sized, A: Allocator + Default> CreateAddress for Box<T, A> {
    fn create(value: Self::Pointee) -> Self {
        Box::new_in(value, A::default())
    }
}
impl<T: Sized, A: Allocator + Default + 'static> CreateAddress for Pin<Box<T, A>> {
    fn create(value: Self::Pointee) -> Self {
        Box::pin_in(value, A::default())
    }
}
impl<T: Sized, A: Allocator + Default> CreateAddress for Option<Box<T, A>> {
    fn create(value: Self::Pointee) -> Self {
        Some(Box::new_in(value, A::default()))
    }
}
impl<T: Sized, A: Allocator + Default + 'static> CreateAddress for Option<Pin<Box<T, A>>> {
    fn create(value: Self::Pointee) -> Self {
        Some(Box::pin_in(value, A::default()))
    }
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
