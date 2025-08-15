use crate::{
    alloc::{Allocator, Global},
    borrow::PartialClone,
    boxed::Box,
    bytes, into_non_null,
    node::{Node, PopPair},
};
use core::marker::PhantomData;
use core::ops::Index;

/// BRANCH_FACTOR must be a power of 2 and 2 <= BRANCH_FACTOR <= 256.
pub struct PersVec<'a, T: 'a, const BRANCH_FACTOR: usize = 32, A: Allocator + Clone = Global>
where
    [(); bytes(BRANCH_FACTOR)]:,
{
    allocator: A,
    total_length: usize,
    head: Node<BRANCH_FACTOR, T, A>,
    tail: Node<BRANCH_FACTOR, T, A>, // tail always has values only
    _borrow_lifetime: PhantomData<&'a T>,
}

unsafe impl<const B: usize, T: Sync, A: Allocator + Clone> Send for PersVec<'_, T, B, A> where
    [(); bytes(B)]:
{
}
unsafe impl<const B: usize, T: Sync, A: Allocator + Clone> Sync for PersVec<'_, T, B, A> where
    [(); bytes(B)]:
{
}
impl<'a, const B: usize, T: 'a, A: Allocator + Clone> Drop for PersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
{
    fn drop(&mut self) {
        self.tail.drop_node(
            Self::tail_length(self.total_length),
            0,
            self.allocator.clone(),
        );
        self.head.drop_node(
            self.total_length - Self::tail_length(self.total_length),
            Self::depth(self.total_length),
            self.allocator.clone(),
        );
    }
}
impl<const B: usize, T, A: Allocator + Clone + Default> PersVec<'static, T, B, A>
where
    [(); bytes(B)]:,
{
    pub fn new() -> Self {
        PersVec::new_in(A::default())
    }
}
impl<const B: usize, T, A: Allocator + Clone> PersVec<'static, T, B, A>
where
    [(); bytes(B)]:,
{
    pub const fn new_in(allocator: A) -> Self {
        assert!(2usize.pow(B.ilog2()) == B);
        Self {
            allocator,
            total_length: 0,
            head: Node::<B, T, A>::empty(),
            tail: Node::<B, T, A>::empty(),
            _borrow_lifetime: PhantomData,
        }
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> PersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
{
    ///```
    /// #![feature(generic_const_exprs)]
    /// use norc_pers::PersVec;
    /// for i in 69..=260 {
    ///     assert_eq!(PersVec::<u8, 4>::depth(i), 3);
    /// }
    /// for i in 21..=68 {
    ///     assert_eq!(PersVec::<u8, 4>::depth(i), 2);
    /// }
    /// for i in 9..=20 {
    ///     assert_eq!(PersVec::<u8, 4>::depth(i), 1);
    /// }
    /// for i in 0..=8 {
    ///     assert_eq!(PersVec::<u8, 4>::depth(i), 0);
    /// }
    ///```
    pub fn depth(length: usize) -> u32 {
        if length <= B {
            0
        } else {
            (length - Self::tail_length(length) - 1).ilog(B)
        }
    }
    fn tail_length(length: usize) -> usize {
        let mod_b = length % B;
        if length == 0 {
            0
        } else if mod_b == 0 {
            B
        } else {
            mod_b
        }
    }
    pub fn iter<'c>(&'c self) -> IterPersVec<'c, T, B, A> {
        self.partial_clone().into_iter()
    }
    pub fn len(&self) -> usize {
        self.total_length
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    ///```compile_fail
    /// #![feature(generic_const_exprs)]
    /// use norc_pers::PersVec;
    /// let new: PersVec<char> = PersVec::new().append('c');
    /// let first = new.get(0);
    /// let new = new.append('h');
    /// println!("{}", first.unwrap());
    ///```
    pub fn get(&self, idx: usize) -> Option<&T> {
        if idx >= self.total_length {
            return None;
        }
        if idx / B == (self.total_length - 1) / B {
            let idx = (idx % B) as u8;
            return Some(unsafe { self.tail.branches.values.get(idx).unwrap().as_ref() });
        }
        let depth = Self::depth(self.total_length);
        let bits_needed = B.ilog2();
        let mask = B - 1;
        let mut node = &self.head;
        for i in (1..(depth + 1)).map(|x| x * bits_needed).rev() {
            let idx = idx >> i;
            let branch_idx = (idx & mask) as u8;
            // println!("i: {i}");
            node = unsafe { node.branches.nodes.get(branch_idx).unwrap().as_ref() };
        }
        let branch_idx = (idx & mask) as u8;
        Some(unsafe { node.branches.values.get(branch_idx).unwrap().as_ref() })
    }
    /// If given index is out of bounds, we return self unchanged
    pub fn update(mut self, idx: usize, value: T) -> Self {
        if idx >= self.total_length {
            return self;
        }
        if idx / B == (self.total_length - 1) / B {
            let idx = (idx % B) as u8;
            if self.tail.owned_branches.get(idx as usize) {
                unsafe {
                    *(*self.tail.branches.values)
                        .get_mut(idx)
                        .as_mut()
                        .unwrap()
                        .as_mut() = value
                };
            } else {
                unsafe {
                    *(*self.tail.branches.values).get_mut(idx).as_mut().unwrap() =
                        into_non_null(Box::new_in(value, self.allocator.clone()))
                };
                self.tail.owned_branches.set(idx as usize);
            }
        } else {
            let depth = Self::depth(self.total_length);
            let bits_needed = B.ilog2();
            let mask = B - 1;
            let mut node = &mut self.head;
            for i in (1..(depth + 1)).map(|x| x * bits_needed).rev() {
                let idx = idx >> i;
                let branch_idx = (idx & mask) as u8;
                if !node.owned_branches.get(branch_idx as usize) {
                    let clone = unsafe {
                        node.branches
                            .nodes
                            .get(branch_idx)
                            .unwrap()
                            .as_ref()
                            .partial_borrow()
                    };
                    unsafe {
                        *(*node.branches.nodes).get_mut(branch_idx).as_mut().unwrap() =
                            into_non_null(Box::new_in(clone, self.allocator.clone()))
                    };
                    node.owned_branches.set(branch_idx as usize);
                }
                node = unsafe { (*node.branches.nodes).get_mut(branch_idx).unwrap().as_mut() };
            }
            let branch_idx = (idx & mask) as u8;
            if node.owned_branches.get(branch_idx as usize) {
                unsafe {
                    *(*node.branches.values)
                        .get_mut(branch_idx)
                        .as_mut()
                        .unwrap()
                        .as_mut() = value
                };
            } else {
                unsafe {
                    *(*node.branches.values)
                        .get_mut(branch_idx)
                        .as_mut()
                        .unwrap() = into_non_null(Box::new_in(value, self.allocator.clone()))
                };
                node.owned_branches.set(branch_idx as usize);
            }
        }
        self
    }
    fn append_mut(&mut self, value: T) {
        let tail_length = Self::tail_length(self.total_length);

        let mut tail = core::mem::replace(&mut self.tail, Node::<B, T, A>::empty());
        if tail_length == B {
            let tail = core::mem::replace(&mut tail, Node::<B, T, A>::empty());
            let head = core::mem::replace(&mut self.head, Node::<B, T, A>::empty());
            let depth = Self::depth(self.total_length);
            let length_without_tail = self.total_length - tail_length;
            let head = if length_without_tail > 1 && B.pow(depth + 1) == length_without_tail {
                let result_node = Node::new_internal(head, self.allocator.clone());
                let mut node = tail;
                for _ in 0..depth {
                    node = Node::new_internal(node, self.allocator.clone());
                }
                result_node.branches_append_node(node, 1, self.allocator.clone())
            } else {
                head.vector_append_tail(tail, length_without_tail, depth, self.allocator.clone())
            };
            self.head = head;
        }
        self.tail = tail.branches_append_value(value, tail_length % B, self.allocator.clone());
        self.total_length += 1;
    }
    #[must_use]
    pub fn append(mut self, value: T) -> Self {
        self.append_mut(value);
        self
    }
    fn pop_mut(&mut self) {
        if self.total_length == 0 {
            return;
        }
        let tail_length = Self::tail_length(self.total_length);
        let tail = core::mem::replace(&mut self.tail, Node::empty());
        self.tail = tail.branches_pop_value(tail_length, self.allocator.clone());

        if self.total_length > 1 && tail_length == 1 {
            let length_without_tail = self.total_length - tail_length;
            let depth = Self::depth(self.total_length);
            let head = core::mem::replace(&mut self.head, Node::empty());
            if depth == 0 {
                self.tail = head;
            } else if B.pow(depth) == length_without_tail - B {
                let PopPair { head, mut tail } = head.branches_pop_node(2, self.allocator.clone());
                let PopPair { tail: head, .. } = head.branches_pop_node(1, self.allocator.clone());
                for _ in 0..(depth - 1) {
                    // TODO currently, tail ownership would need to be tracked so we can properly free it
                    // change tail to owned node in PopPair rather than nonnull, so we can free in
                    // vector_pop_tail instead
                    let pair = tail.branches_pop_node(1, self.allocator.clone());
                    tail = pair.tail;
                }
                self.head = head;
                self.tail = tail;
            } else {
                let pair = head.vector_pop_tail(length_without_tail, depth, self.allocator.clone());
                self.head = pair.head;
                self.tail = pair.tail;
            }
        }
        self.total_length -= 1;
    }
    #[must_use]
    pub fn pop(mut self) -> Self {
        self.pop_mut();
        self
    }
}
impl<const B: usize, T, A: Allocator + Clone> PartialClone for PersVec<'_, T, B, A>
where
    [(); bytes(B)]:,
{
    type Cloned<'a>
        = PersVec<'a, T, B, A>
    where
        Self: 'a;
    fn partial_clone<'c>(&'c self) -> Self::Cloned<'c> {
        Self {
            head: Node::<B, T, A>::partial_borrow(&self.head),
            tail: Node::<B, T, A>::partial_borrow(&self.tail),
            allocator: self.allocator.clone(),
            ..*self
        }
    }
}

impl<const B: usize, T, A: Allocator + Clone + Default> Default for PersVec<'static, T, B, A>
where
    [(); bytes(B)]:,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const B: usize, T, A: Allocator + Clone> Index<usize> for PersVec<'_, T, B, A>
where
    [(); bytes(B)]:,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}
impl<'a, const B: usize, T, A: Allocator + Clone> IntoIterator for PersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
{
    type Item = &'a T;
    type IntoIter = IterPersVec<'a, T, B, A>;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            front: 0,
            back: self.len(),
            vector: self,
        }
    }
}

impl<const B: usize, T, A: Allocator + Clone + Default> FromIterator<T>
    for PersVec<'static, T, B, A>
where
    [(); bytes(B)]:,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut pv = PersVec::new_in(A::default());
        for t in iter {
            pv = pv.append(t);
        }
        pv
    }
}

pub struct IterPersVec<'a, T, const B: usize, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    front: usize,
    back: usize,
    vector: PersVec<'a, T, B, A>,
}

impl<'a, const B: usize, T, A: Allocator + Clone> Iterator for IterPersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
{
    // TODO could pop items, or just chain iterators of branches for impl, will bm this and ensure
    // we get traits
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
impl<const B: usize, T, A: Allocator + Clone> DoubleEndedIterator for IterPersVec<'_, T, B, A>
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
impl<const B: usize, T, A: Allocator + Clone> ExactSizeIterator for IterPersVec<'_, T, B, A> where
    [(); bytes(B)]:
{
}

#[cfg(test)]
mod tests {
    use crate::*;
    use borrow::PartialClone;

    #[test]
    fn it_works() {
        let new: PersVec<char, 8> = PersVec::new().append('c').append('h');

        assert_eq!(new.get(0), Some(&'c'));
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), None);
        let new = new.append('g');
        assert_eq!(new.get(0), Some(&'c'));
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), Some(&'g'));
        assert_eq!(new.get(3), None);
        let mut new = new.pop();
        assert_eq!(new.get(0), Some(&'c'));
        assert_eq!(new.get(1), Some(&'h'));
        assert_eq!(new.get(2), None);
        for _ in 0..new.len() {
            new = new.pop();
        }
        assert_eq!(new.get(0), None);
        let new = new.pop();
        assert_eq!(new.get(0), None);
    }

    #[test]
    fn borrow_test() {
        let new: PersVec<char, 8> = pers_vec!['c', 'h'];
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
        let mut pers: PersVec<isize, 4> = pers_vec![];

        for i in 0..100 {
            pers = pers.append(i);
        }
        for i in 0..100 {
            assert_eq!(pers.get(i as usize), Some(&i));
        }
        assert_eq!(pers.get(100), None);
        assert_eq!(pers.len(), 100);

        for _ in 0..2 {
            let mut clone = pers.partial_clone();
            assert_eq!(clone.len(), 100);
            for i in 0..100 {
                assert_eq!(clone.get(i as usize), Some(&i));
            }
            for i in 1..=200 {
                clone = clone.append(i);
            }
            for i in 0..100 {
                clone = clone.update(i, -(i as isize));
            }
            for i in 0..100 {
                assert_eq!(clone.get(i as usize), Some(&-i));
            }
            assert_eq!(clone.len(), 300);
            for i in 1..=200 {
                assert_eq!(clone.get(i as usize + 99), Some(&i));
            }
            for _ in 1..=200 {
                clone = clone.pop();
            }
            assert_eq!(clone.len(), 100);
            for i in 1..=200 {
                assert_eq!(clone.get(i + 99), None);
            }
            for _ in 0..100 {
                clone = clone.pop();
            }
            assert!(clone.is_empty());
            for i in 0..100 {
                assert_eq!(clone.get(i), None);
            }
        }
        for _ in 0..100 {
            pers = pers.pop();
        }
        assert!(pers.is_empty());
    }
}
