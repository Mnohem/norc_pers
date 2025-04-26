use crate::{Box, UnsafeRef};
use core::mem::{ManuallyDrop, MaybeUninit};

struct Branches<const BRANCH_FACTOR: usize, T> {
    array: [MaybeUninit<T>; BRANCH_FACTOR],
}
impl<const B: usize, T> Branches<B, T> {
    const fn uninit() -> Self {
        Branches {
            array: [const { MaybeUninit::uninit() }; B],
        }
    }
}

union AmbiguousBranches<'a, const B: usize, T> {
    values: ManuallyDrop<UnsafeRef<'a, Branches<B, T>>>,
    nodes: ManuallyDrop<UnsafeRef<'a, Branches<B, Node<'a, B, T>>>>,
}

struct Node<'a, const B: usize, T> {
    leaf: bool,
    owned: bool,
    start: u8,
    length: u8,
    branches: AmbiguousBranches<'a, B, T>,
}
impl<'a, const B: usize, T> Drop for Node<'a, B, T> {
    fn drop(&mut self) {
        if self.owned {
            if self.leaf {
                let branches = unsafe { &mut *(*self.branches.values).boxed };
                for x in
                    &mut branches.array[(self.start as usize)..(self.start + self.length) as usize]
                {
                    unsafe { x.assume_init_drop() };
                }
                unsafe {
                    ManuallyDrop::drop(&mut (*self.branches.values).boxed);
                    ManuallyDrop::drop(&mut self.branches.values);
                }
            } else {
                let branches = unsafe { &mut *(*self.branches.nodes).boxed };
                for x in
                    &mut branches.array[(self.start as usize)..(self.start + self.length) as usize]
                {
                    unsafe { x.assume_init_drop() };
                }
                unsafe {
                    ManuallyDrop::drop(&mut (*self.branches.nodes).boxed);
                }
            }
        }
    }
}

impl<'a, const B: usize, T> Node<'a, B, T> {
    fn new() -> Self {
        Self {
            leaf: true,
            owned: true,
            start: 0,
            length: 0,
            branches: AmbiguousBranches {
                values: ManuallyDrop::new(UnsafeRef::from_box(Box::new(Branches::uninit()))),
            },
        }
    }
}

/// BRANCH_FACTOR must be < 256.
pub struct Vector<'a, const BRANCH_FACTOR: usize, T> {
    length: usize,
    head: Node<'a, BRANCH_FACTOR, T>,
}
