#![feature(set_ptr_value)]
#![feature(layout_for_ptr)]
#![feature(unsize)]
#![feature(maybe_uninit_slice)]
#![feature(box_into_inner)]
#![feature(ptr_as_uninit)]
#![feature(breakpoint)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]

pub mod borrow;
mod list;
pub(crate) mod node;
mod vector;

pub use list::List;
pub use vector::PersVec;

use core::{ops::Deref, ptr::NonNull};

cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        pub(crate) use allocator_api2::alloc;
        pub(crate) use allocator_api2::boxed;
        use allocator_api2::alloc::Allocator;
        use allocator_api2::boxed::Box;
        pub(crate) unsafe fn into_non_null<T: ?Sized, A: Allocator>(boxed: Box<T, A>) -> NonNull<T> {
            Box::into_non_null(boxed).0
        }
    } else if #[cfg(feature = "std")] {
        pub(crate) use std::alloc;
        pub(crate) use std::boxed;
        use std::alloc::Allocator;
        use std::boxed::Box;
        pub(crate) unsafe fn into_non_null<T: ?Sized, A: Allocator>(boxed: Box<T, A>) -> NonNull<T> {
            Box::into_non_null_with_allocator(boxed).0
        }
    } else {
        extern crate alloc as mem;
        pub(crate) use mem::alloc;
        pub(crate) use mem::boxed;
        use mem::alloc::Allocator;
        use mem::boxed::Box;
        pub(crate) unsafe fn into_non_null<T: ?Sized, A: Allocator>(boxed: Box<T, A>) -> NonNull<T> {
            Box::into_non_null_with_allocator(boxed).0
        }
    }
}

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
const fn bytes(n: usize) -> usize {
    n.div_ceil(8)
}

pub const BRANCH_FACTOR: usize = 16;
#[derive(Clone, Copy)]
pub struct BitArray([u8; bytes(BRANCH_FACTOR)]);
impl BitArray {
    pub const fn new() -> Self {
        Self([0; _])
    }
    pub fn get(&self, idx: usize) -> bool {
        assert!(idx < BRANCH_FACTOR);
        let byte_idx = idx / 8;
        let bit_idx = 7 - (idx % 8);
        let mask = 1 << bit_idx;
        mask & self.0[byte_idx] != 0
    }
    pub fn set(&mut self, idx: usize) {
        assert!(idx < BRANCH_FACTOR);
        let byte_idx = idx / 8;
        let bit_idx = 7 - (idx % 8);
        let mask = 1 << bit_idx;
        self.0[byte_idx] |= mask;
    }
    pub fn unset(&mut self, idx: usize) {
        assert!(idx < BRANCH_FACTOR);
        let byte_idx = idx / 8;
        let bit_idx = 7 - (idx % 8);
        let mask = 1 << bit_idx;
        self.0[byte_idx] &= !mask;
    }
    pub fn toggle(&mut self, idx: usize) {
        assert!(idx < BRANCH_FACTOR);
        let byte_idx = idx / 8;
        let bit_idx = 7 - (idx % 8);
        let mask = 1 << bit_idx;
        self.0[byte_idx] ^= mask;
    }
    pub fn update(&mut self, idx: usize, bit: bool) {
        if bit {
            self.set(idx);
        } else {
            self.unset(idx);
        }
    }
    pub fn or(self, other: Self) -> Self {
        let mut result = Self::new();
        for i in 0..bytes(BRANCH_FACTOR) {
            result.0[i] = self.0[i] | other.0[i];
        }
        result
    }
    pub fn and(self, other: Self) -> Self {
        let mut result = Self::new();
        for i in 0..bytes(BRANCH_FACTOR) {
            result.0[i] = self.0[i] & other.0[i];
        }
        result
    }
}
