use crate::alloc::{Allocator, Global};
use crate::borrow::PartialClone;
use crate::boxed::Box;
use crate::{BitArray, bytes, into_non_null};
use core::ops::Index;
use core::ptr::NonNull;
use core::{
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ops::Range,
};

struct Branches<const BRANCH_FACTOR: usize, T> {
    array: [MaybeUninit<T>; BRANCH_FACTOR],
}
impl<const B: usize, T> Branches<B, T> {
    const fn uninit() -> ManuallyDrop<Self> {
        ManuallyDrop::new(Branches {
            array: [const { MaybeUninit::uninit() }; B],
        })
    }
    const fn first(value: T) -> ManuallyDrop<Self> {
        let mut array = [const { MaybeUninit::<T>::uninit() }; B];
        unsafe { array[0].as_mut_ptr().write(value) };
        ManuallyDrop::new(Branches { array })
    }
    unsafe fn append(&mut self, start: u8, len: u8, value: T) -> bool {
        unsafe {
            self.array
                .get_mut((start + len) as usize)
                .map(|x| x.as_mut_ptr().write(value))
                .is_some()
        }
    }
    unsafe fn _prepend(&mut self, start: u8, value: T) -> bool {
        unsafe {
            if start == 0 {
                return false;
            }
            self.array
                .get_mut(start as usize - 1)
                .map(|x| x.as_mut_ptr().write(value))
                .is_some()
        }
    }
    unsafe fn get(&self, idx: u8) -> &T {
        unsafe { self.array[idx as usize].assume_init_ref() }
    }
    unsafe fn range_mut(&mut self, r: Range<u8>) -> &mut [T] {
        unsafe {
            self.array[Range {
                start: r.start as usize,
                end: r.end as usize,
            }]
            .assume_init_mut()
        }
    }
}
union AmbiguousBranches<const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    values: ManuallyDrop<Branches<B, NonNull<T>>>,
    nodes: ManuallyDrop<Branches<B, NonNull<Node<B, T, A>>>>,
    _phantom: PhantomData<A>,
}

struct Node<const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    owned_branches: BitArray<B>,
    branches: AmbiguousBranches<B, T, A>,
}

impl<const B: usize, T, A: Allocator + Clone> Node<B, T, A>
where
    [(); bytes(B)]:,
{
    const fn empty() -> Self {
        Self {
            owned_branches: BitArray::new(),
            branches: AmbiguousBranches::<B, T, A> {
                values: Branches::uninit(),
            },
        }
    }
    fn new_leaf(initial_value: T, allocator: A) -> Self {
        let values = Branches::first(unsafe {
            into_non_null(Box::<T, A>::new_in(initial_value, allocator))
        });
        let mut owned_branches = BitArray::new();
        owned_branches.set(0);
        Self {
            owned_branches,
            branches: AmbiguousBranches::<B, T, A> { values },
        }
    }
    fn _new_leaf_ref(initial_ref: &T) -> Self {
        let values = Branches::first(NonNull::from_ref(initial_ref));
        Self {
            owned_branches: BitArray::new(),
            branches: AmbiguousBranches::<B, T, A> { values },
        }
    }
    fn new_internal(child_node: Self, allocator: A) -> Self {
        let nodes = Branches::first(unsafe {
            into_non_null(Box::<Self, A>::new_in(child_node, allocator))
        });
        let mut owned_branches = BitArray::new();
        owned_branches.set(0);
        Self {
            owned_branches,
            branches: AmbiguousBranches::<B, T, A> { nodes },
        }
    }
    fn partial_borrow(&self) -> Self {
        Self {
            owned_branches: BitArray::new(),
            branches: unsafe { core::mem::transmute_copy(&self.branches) },
        }
    }
    fn branches_append_value(mut self, value: T, length: usize, allocator: A) -> Self {
        if length as usize >= B {
            unreachable!()
        }
        unsafe {
            debug_assert!((*self.branches.values).append(
                0,
                length as u8,
                into_non_null(Box::<T, A>::new_in(value, allocator)),
            ))
        }
        self.owned_branches.set(length);
        self
    }
    fn drop_node(&mut self, length: usize, depth: u32, allocator: A) {
        let branches_amount = length.div_ceil(B.pow(depth)) as u8;
        if depth == 0 {
            for (i, value) in unsafe { (*self.branches.values).range_mut(0..branches_amount) }
                .iter_mut()
                .enumerate()
            {
                if self.owned_branches.get(i) {
                    unsafe { drop(Box::<T, A>::from_raw_in(value.as_ptr(), allocator.clone())) };
                }
            }
        } else {
            let next_length = B.pow(depth);
            for (i, node) in unsafe { (*self.branches.nodes).range_mut(0..branches_amount) }
                .iter_mut()
                .enumerate()
            {
                if i == branches_amount as usize - 1 && length % next_length != 0 {
                    if self.owned_branches.get(branches_amount as usize - 1) {
                        let last_length = length % next_length;
                        let boxed_node = node.as_ptr();
                        Self::drop_node(
                            &mut Box::<Self, A>::into_inner(unsafe {
                                Box::<Self, A>::from_raw_in(boxed_node, allocator.clone())
                            }),
                            last_length,
                            depth - 1,
                            allocator.clone(),
                        )
                    }
                } else if self.owned_branches.get(i) {
                    let boxed_node = node.as_ptr();
                    Self::drop_node(
                        &mut Box::<Self, A>::into_inner(unsafe {
                            Box::<Self, A>::from_raw_in(boxed_node, allocator.clone())
                        }),
                        next_length,
                        depth - 1,
                        allocator.clone(),
                    )
                }
            }
        }
    }
    fn vector_append(mut self, value: T, length: usize, depth: u32, allocator: A) -> Self {
        let next_length = length % B.pow(depth);
        if depth == 0 {
            self.branches_append_value(value, length, allocator)
        } else if next_length == 0 {
            // add a new node with the correct depth
            let mut node = Node::new_leaf(value, allocator.clone());
            for _ in 0..(depth - 1) {
                node = Node::new_internal(node, allocator.clone());
            }
            let branches_amount = (length / B.pow(depth)) as u8;
            unsafe {
                debug_assert!((*self.branches.nodes).append(
                    0,
                    branches_amount,
                    into_non_null(Box::<Self, A>::new_in(node, allocator.clone())),
                ))
            }
            self.owned_branches.set(branches_amount as usize);
            self
        } else {
            // recurse down the last node
            let branches_amount = length.div_ceil(B.pow(depth)) as u8;
            let node = unsafe { (*self.branches.nodes).range_mut(0..branches_amount) }
                .last_mut()
                .unwrap();
            if self.owned_branches.get(branches_amount as usize - 1) {
                unsafe {
                    node.write(node.read().vector_append(
                        value,
                        next_length,
                        depth - 1,
                        allocator.clone(),
                    ))
                };
            } else {
                *node = unsafe {
                    into_non_null(Box::<Self, A>::new_in(
                        node.as_ref().partial_borrow().vector_append(
                            value,
                            next_length,
                            depth - 1,
                            allocator.clone(),
                        ),
                        allocator.clone(),
                    ))
                };
            }
            self.owned_branches.set(branches_amount as usize - 1);
            self
        }
    }
}

/// BRANCH_FACTOR must be a power of 2 and 2 <= BRANCH_FACTOR <= 256.
pub struct PersVector<'a, const BRANCH_FACTOR: usize, T: 'a, A: Allocator + Clone = Global>
where
    [(); bytes(BRANCH_FACTOR)]:,
{
    allocator: A,
    total_length: usize,
    head: Node<BRANCH_FACTOR, T, A>,
    _lifetime: PhantomData<&'a T>,
}

unsafe impl<const B: usize, T: Sync, A: Allocator + Clone> Send for PersVector<'_, B, T, A> where
    [(); bytes(B)]:
{
}
unsafe impl<const B: usize, T: Sync, A: Allocator + Clone> Sync for PersVector<'_, B, T, A> where
    [(); bytes(B)]:
{
}
impl<'a, const B: usize, T: 'a, A: Allocator + Clone> Drop for PersVector<'a, B, T, A>
where
    [(); bytes(B)]:,
{
    fn drop(&mut self) {
        self.head.drop_node(
            self.total_length,
            Self::depth(self.total_length),
            self.allocator.clone(),
        );
    }
}
impl<'a, const B: usize, T> PersVector<'a, B, T, Global>
where
    [(); bytes(B)]:,
{
    pub const fn new() -> PersVector<'a, B, T, Global> {
        PersVector::new_in(Global)
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> PersVector<'a, B, T, A>
where
    [(); bytes(B)]:,
{
    pub const fn new_in(allocator: A) -> Self {
        assert!(2usize.pow(B.ilog2()) == B);
        Self {
            allocator,
            total_length: 0,
            head: Node::<B, T, A>::empty(),
            _lifetime: PhantomData,
        }
    }
    pub fn iter<'b>(&'b self) -> IterPersVec<'b, B, T, A> {
        self.partial_clone().into_iter()
    }
    fn depth(length: usize) -> u32 {
        if length == 0 { 0 } else { length.ilog(B) }
    }
    pub fn len(&self) -> usize {
        self.total_length
    }
    ///```compile_fail
    /// #![feature(generic_const_exprs)]
    /// use norc_pers::PersVector;
    /// let new: PersVector<8, char> = PersVector::new().append('c');
    /// let first = new.get(0);
    /// let new = new.append('h');
    /// println!("{}", first.unwrap());
    ///```
    pub fn get(&self, idx: usize) -> Option<&T> {
        if idx >= self.total_length {
            return None;
        }
        let depth = Self::depth(self.total_length);
        let bits_needed = B.ilog2();
        let mask = B - 1;
        let mut node = &self.head;
        for i in (1..(depth + 1)).map(|x| x * bits_needed).rev() {
            let idx = idx >> i;
            let branch_idx = (idx & mask) as u8;
            // println!("i: {i}");
            node = unsafe { &*node.branches.nodes.get(branch_idx).as_ptr() };
        }
        let branch_idx = (idx & mask) as u8;
        Some(unsafe { &*node.branches.values.get(branch_idx).as_ptr() })
    }
    fn append_mut(&mut self, value: T) {
        let head = core::mem::replace(&mut self.head, Node::<B, T, A>::empty());
        let depth = Self::depth(self.total_length);
        let head = if self.total_length > 1 && B.pow(depth) == self.total_length {
            let mut result_node = Node::new_internal(head, self.allocator.clone());
            let mut node = Node::new_leaf(value, self.allocator.clone());
            for _ in 0..(depth - 1) {
                node = Node::new_internal(node, self.allocator.clone());
            }
            unsafe {
                debug_assert!((*result_node.branches.nodes).append(
                    0,
                    1,
                    into_non_null(Box::<Node<B, T, A>, A>::new_in(
                        node,
                        self.allocator.clone()
                    )),
                ))
            }
            result_node.owned_branches.set(1);
            result_node
        } else {
            head.vector_append(value, self.total_length, depth, self.allocator.clone())
        };
        self.total_length += 1;
        self.head = head;
    }
    #[must_use]
    pub fn append(mut self, value: T) -> Self {
        self.append_mut(value);
        self
    }
}
impl<const B: usize, T, A: Allocator + Clone> PartialClone for PersVector<'_, B, T, A>
where
    [(); bytes(B)]:,
{
    type Cloned<'a>
        = PersVector<'a, B, T, A>
    where
        Self: 'a;
    fn partial_clone<'b>(&'b self) -> Self::Cloned<'b> {
        Self {
            head: Node::<B, T, A>::partial_borrow(&self.head),
            allocator: self.allocator.clone(),
            ..*self
        }
    }
}
impl<const B: usize, T, A: Allocator + Clone> Index<usize> for PersVector<'_, B, T, A>
where
    [(); bytes(B)]:,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}
// TODO FromIterator for ref and box
// can this be impl for non global?
impl<'a, const B: usize, T> FromIterator<T> for PersVector<'a, B, T, Global>
where
    [(); bytes(B)]:,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut pv = Self::new();
        for t in iter.into_iter() {
            pv = pv.append(t);
        }
        pv
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> IntoIterator for PersVector<'a, B, T, A>
where
    [(); bytes(B)]:,
{
    type Item = &'a T;
    type IntoIter = IterPersVec<'a, B, T, A>;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            front: 0,
            back: self.len(),
            vector: self,
        }
    }
}
pub struct IterPersVec<'a, const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    front: usize,
    back: usize,
    vector: PersVector<'a, B, T, A>,
}

impl<'a, const B: usize, T, A: Allocator + Clone> Iterator for IterPersVec<'a, B, T, A>
where
    [(); bytes(B)]:,
{
    // TODO could pop items
    type Item = &'a T;
    // these unsafes are fine since vector cant be mutated or taken once it enters the iterator
    fn next(&mut self) -> Option<Self::Item> {
        self.front += 1;
        if self.front > self.back {
            return None;
        };
        unsafe { core::mem::transmute(self.vector.get(self.front - 1)) }
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.front += n + 1;
        if self.front > self.back {
            return None;
        };
        unsafe { core::mem::transmute(self.vector.get(self.front - 1)) }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.back - self.front;
        (size, Some(size))
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> DoubleEndedIterator for IterPersVec<'a, B, T, A>
where
    [(); bytes(B)]:,
{
    // these unsafes are fine since vector cant be mutated or taken once it enters the iterator
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back = self.back.checked_sub(1)?;
        if self.front > self.back {
            return None;
        };
        unsafe { core::mem::transmute(self.vector.get(self.back)) }
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.back = self.back.checked_sub(n)?;
        self.next_back()
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> ExactSizeIterator for IterPersVec<'a, B, T, A> where
    [(); bytes(B)]:
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let new: PersVector<8, char> = PersVector::new().append('c').append('h');

        assert_eq!(new.get(0), Some(&'c'));
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), None);
        let new = new.append('g');
        assert_eq!(new.get(0), Some(&'c'));
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), Some(&'g'));
        assert_eq!(new.get(3), None);
    }

    #[test]
    fn borrow_test() {
        let new: PersVector<8, char> = PersVector::new().append('c').append('h');
        {
            let next = new.partial_clone();
            assert_eq!(next.get(1), Some(&'h'));
            let next = next.append('p');
            assert_eq!(next.get(2), Some(&'p'));
        }
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), None);
        let new = new.append('i');
        assert_eq!(new.get(2), Some(&'i'));
    }
    #[test]
    fn tree_follow() {
        let mut pers: PersVector<4, usize> = PersVector::new();

        for i in 0..100 {
            pers = pers.append(i);
        }
        for i in 0..100 {
            assert_eq!(pers.get(i), Some(&i));
        }
        assert_eq!(pers.get(100), None);

        for _ in 0..2 {
            let mut clone = pers.partial_clone();
            for i in 1..=200 {
                clone = clone.append(i);
            }
            for i in 1..=200 {
                assert_eq!(clone.get(i + 99), Some(&i));
            }
        }
    }
}
