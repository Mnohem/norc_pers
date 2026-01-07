#![feature(box_into_inner)]
#![feature(ptr_as_uninit)]
#![feature(iter_array_chunks)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]

pub mod borrow;
mod champ;
pub(crate) mod node;
mod vector;

pub use vector::PersVec;

use core::num::NonZeroUsize;
pub use core::{ops::Deref, ptr::NonNull};

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

const fn bytes(n: usize) -> usize {
    n.div_ceil(8)
}

pub const BRANCH_FACTOR: usize = 32;
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BitArray([u8; bytes(BRANCH_FACTOR)]);
impl BitArray {
    pub const fn zeroes() -> Self {
        Self([0; _])
    }
    pub fn set_bits_up_to(idx: usize) -> Self {
        let mut result = Self::zeroes();
        for i in 0..idx {
            result.set(i);
        }
        result
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
        let mut result = Self::zeroes();
        for i in 0..bytes(BRANCH_FACTOR) {
            result.0[i] = self.0[i] | other.0[i];
        }
        result
    }
    pub fn and(self, other: Self) -> Self {
        let mut result = Self::zeroes();
        for i in 0..bytes(BRANCH_FACTOR) {
            result.0[i] = self.0[i] & other.0[i];
        }
        result
    }
    pub fn count_bits(self) -> u32 {
        let mut result = 0;
        for i in 0..bytes(BRANCH_FACTOR) {
            result += self.0[i].count_ones();
        }
        result
    }
    pub fn count_bits_up_to(self, num: usize) -> u32 {
        let mut result = 0;
        let full_bytes_covered = num / 8;
        for i in 0..full_bytes_covered {
            result += self.0[i].count_ones();
        }
        let leftover_bits = (num % 8) as u8;
        result
            + self
                .0
                .get(full_bytes_covered)
                .map(|x| (x >> (8 - leftover_bits)).count_ones())
                .unwrap_or(0)
    }
}
impl Default for BitArray {
    fn default() -> Self {
        Self::zeroes()
    }
}

/// `align_of::<T>() >= 2`
/// lsb is tag, set for owned, unset for unowned
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct RentPtr<T>(NonNull<T>);
impl<T> RentPtr<T> {
    /// ```
    /// let own = RentPtr::new_owned(NonNull::new(Box::new(1usize).as_ptr())?);
    /// let unown = RentPtr::new_unowned(&own);
    /// assert!(own.is_owned());
    /// assert!(!unown.is_owned());
    /// ```
    pub fn is_owned(&self) -> bool {
        (self.0.addr().get() & 1) == 1
    }
    fn ptr(&self) -> NonNull<T> {
        self.0
            .map_addr(|x| unsafe { NonZeroUsize::new(x.get() & !1).unwrap_unchecked() })
    }
    pub fn as_ptr(&self) -> Option<NonNull<T>> {
        if !self.is_owned() {
            return None;
        }
        Some(self.ptr())
    }
    pub fn new_owned(ptr: NonNull<T>) -> Self {
        RentPtr(ptr.map_addr(|x| x.saturating_add(1)))
    }
    pub fn new_unowned(ptr: &T) -> Self {
        RentPtr(NonNull::from(ptr))
    }
    pub fn as_unowned(&self) -> Self {
        RentPtr::new_unowned(unsafe { self.ptr().as_ref() })
    }
}
impl<T> AsRef<T> for RentPtr<T> {
    fn as_ref(&self) -> &T {
        unsafe { self.ptr().as_ref() }
    }
}

#[cfg(test)]
mod tests {
    use crate::BitArray;

    #[test]
    fn count_bits_up_to() {
        let mut bits = BitArray::set_bits_up_to(3);
        assert_eq!(3, bits.count_bits_up_to(3));
        bits.unset(1);
        assert_eq!(2, bits.count_bits_up_to(3));
        bits.set(3);
        assert_eq!(2, bits.count_bits_up_to(3));
    }
}
