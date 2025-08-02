#![expect(incomplete_features)]
#![feature(set_ptr_value)]
#![feature(layout_for_ptr)]
#![feature(unsize)]
#![feature(maybe_uninit_slice)]
#![feature(generic_const_exprs)]
#![feature(box_into_inner)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
// #![no_std]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]

mod list;
mod vector;

pub use list::List;
pub use vector::PersVector;

cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        pub(crate) use allocator_api2::alloc;
        pub(crate) use allocator_api2::boxed;
        use allocator_api2::alloc::Allocator;
        use allocator_api2::boxed::Box;
    } else if #[cfg(feature = "std")] {
        pub(crate) use std::alloc;
        pub(crate) use std::boxed;
        use std::alloc::Allocator;
        use std::boxed::Box;
    } else {
        extern crate alloc as mem;
        pub(crate) use mem::alloc;
        pub(crate) use mem::boxed;
        use mem::alloc::Allocator;
        use mem::boxed::Box;
    }
}
use core::{ops::Deref, ptr::NonNull};
#[derive(Debug, Clone)]
enum Ref<'a, T: ?Sized> {
    Boxed(Box<T>),
    Borrowed(&'a T),
}
impl<'a, T: ?Sized> Ref<'a, T> {
    // For when we know we are holding a reference to a value that isnt owned
    fn ref_unchecked(self) -> &'a T {
        match self {
            Self::Boxed(_) => unreachable!(),
            Self::Borrowed(t) => t,
        }
    }
    // For when we know we are owning a value we want to mutate
    fn mut_unchecked(&mut self) -> &mut T {
        match self {
            Self::Boxed(t) => t.as_mut(),
            Self::Borrowed(_) => unreachable!(),
        }
    }
}
impl<'a, T: ?Sized> Deref for Ref<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Boxed(bt) => bt.deref(),
            Self::Borrowed(t) => t,
        }
    }
}
impl<'a, T> AsRef<T> for Ref<'a, T>
where
    T: ?Sized,
    <Ref<'a, T> as Deref>::Target: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.deref()
    }
}
union UnsafeRef<'a, T: ?Sized> {
    boxed: NonNull<T>,
    borrowed: &'a T,
}
impl<'a, T: ?Sized> UnsafeRef<'a, T> {
    cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        pub fn from_box<A: Allocator>(val: Box<T, A>) -> Self {
            UnsafeRef {
                boxed: Box::<T, A>::into_non_null(val).0
            }
        }
    } else {
        pub fn from_box<A: Allocator>(val: Box<T, A>) -> Self {
            UnsafeRef {
                boxed: Box::<T, A>::into_non_null_with_allocator(val).0
            }
        }
    }
    }
}
pub const fn bytes(n: usize) -> usize {
    n.div_ceil(8)
}
pub struct BitArray<const N: usize>([u8; bytes(N)])
where
    [(); bytes(N)]:;
impl<const N: usize> BitArray<N>
where
    [(); bytes(N)]:,
{
    pub const fn new() -> Self {
        Self([0; _])
    }
    pub fn get(&self, idx: usize) -> bool {
        assert!(idx < N);
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        let mask = 1 << bit_idx;
        mask & self.0[byte_idx] != 0
    }
    pub fn set(&mut self, idx: usize) {
        assert!(idx < N);
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        let mask = 1 << bit_idx;
        self.0[byte_idx] |= mask;
    }
    pub fn unset(&mut self, idx: usize) {
        assert!(idx < N);
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        let mask = 1 << bit_idx;
        self.0[byte_idx] &= !mask;
    }
    pub fn toggle(&mut self, idx: usize) {
        assert!(idx < N);
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        let mask = 1 << bit_idx;
        self.0[byte_idx] ^= mask;
    }
}
