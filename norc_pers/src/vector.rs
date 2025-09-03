use crate::{
    alloc::{Allocator, Global},
    borrow::{PartialClone, Succeed},
    boxed::Box,
    bytes, into_non_null,
    node::{Node, PopPair},
};
use core::ops::Index;
use core::{marker::PhantomData, sync::atomic::AtomicUsize};

/// BRANCH_FACTOR must be a power of 2 and in [2, 256].
pub struct PersVec<'a, T: 'a, const BRANCH_FACTOR: usize = 32, A: Allocator + Clone = Global>
where
    [(); bytes(BRANCH_FACTOR)]:,
{
    allocator: A,
    total_length: usize,
    head: Node<BRANCH_FACTOR, T, A>,
    tail: Node<BRANCH_FACTOR, T, A>, // tail always has values only
    id: usize,
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
static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);
impl<const B: usize, T, A: Allocator + Clone> PersVec<'static, T, B, A>
where
    [(); bytes(B)]:,
{
    pub fn new_in(allocator: A) -> Self {
        assert!(2usize.pow(B.ilog2()) == B);
        Self {
            allocator,
            total_length: 0,
            head: Node::<B, T, A>::empty(),
            tail: Node::<B, T, A>::empty(),
            id: ID_COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
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
        IterPersVec {
            front: 0,
            back: self.len(),
            vector: self,
        }
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
    pub fn last(&self) -> Option<&T> {
        self.get(self.total_length - 1)
    }
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }
    /// If given index is out of bounds, we return self unchanged
    pub fn update(mut self, idx: usize, value: T) -> Self {
        if idx >= self.total_length {
            return self;
        }
        if idx / B == (self.total_length - 1) / B {
            let idx = (idx % B) as u8;
            if self.tail.owned_branches.get_mut().get(idx as usize) {
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
                self.tail.owned_branches.get_mut().set(idx as usize);
            }
        } else {
            let depth = Self::depth(self.total_length);
            let bits_needed = B.ilog2();
            let mask = B - 1;
            let mut node = &mut self.head;
            for i in (1..(depth + 1)).map(|x| x * bits_needed).rev() {
                let idx = idx >> i;
                let branch_idx = (idx & mask) as u8;
                if !node.owned_branches.get_mut().get(branch_idx as usize) {
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
                    node.owned_branches.get_mut().set(branch_idx as usize);
                }
                node = unsafe { (*node.branches.nodes).get_mut(branch_idx).unwrap().as_mut() };
            }
            let branch_idx = (idx & mask) as u8;
            if node.owned_branches.get_mut().get(branch_idx as usize) {
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
                node.owned_branches.get_mut().set(branch_idx as usize);
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
impl<'a, const B: usize, T, A: Allocator + Clone> PersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
    T: PartialClone + Succeed,
{
    /// If the given function returns `None`, or the given index is out of bounds,
    /// we return `self` unchanged
    pub fn then_update_with<F>(mut self, idx: usize, f: F) -> Self
    where
        F: FnOnce(&'a T) -> Option<T::Cloned<'a>>,
    {
        if idx >= self.total_length {
            return self;
        }
        if idx / B == (self.total_length - 1) / B {
            let idx = (idx % B) as u8;
            let non_null_ref =
                unsafe { (*self.tail.branches.values).get_mut(idx).as_mut().unwrap() };
            let Some(value) = f(unsafe { non_null_ref.as_ref() }) else {
                return self;
            };
            if self.tail.owned_branches.get_mut().get(idx as usize) {
                unsafe {
                    non_null_ref.as_ref().succeed(&value);
                    *non_null_ref.as_mut() = PartialClone::extend_inner_lifetime(value);
                }
            } else {
                unsafe {
                    *non_null_ref = into_non_null(Box::new_in(
                        PartialClone::extend_inner_lifetime(value),
                        self.allocator.clone(),
                    ))
                };
                self.tail.owned_branches.get_mut().set(idx as usize);
            }
        } else {
            let depth = Self::depth(self.total_length);
            let bits_needed = B.ilog2();
            let mask = B - 1;
            let mut node = &mut self.head;
            for i in (1..(depth + 1)).map(|x| x * bits_needed).rev() {
                let idx = idx >> i;
                let branch_idx = (idx & mask) as u8;
                if !node.owned_branches.get_mut().get(branch_idx as usize) {
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
                    node.owned_branches.get_mut().set(branch_idx as usize);
                }
                node = unsafe { (*node.branches.nodes).get_mut(branch_idx).unwrap().as_mut() };
            }
            let branch_idx = (idx & mask) as u8;
            let non_null_ref = unsafe {
                (*node.branches.values)
                    .get_mut(branch_idx)
                    .as_mut()
                    .unwrap()
            };
            let Some(value) = f(unsafe { non_null_ref.as_ref() }) else {
                return self;
            };
            if node.owned_branches.get_mut().get(branch_idx as usize) {
                unsafe {
                    non_null_ref.as_ref().succeed(&value);
                    *non_null_ref.as_mut() = PartialClone::extend_inner_lifetime(value);
                }
            } else {
                unsafe {
                    *non_null_ref = into_non_null(Box::new_in(
                        PartialClone::extend_inner_lifetime(value),
                        self.allocator.clone(),
                    ))
                };
                node.owned_branches.get_mut().set(branch_idx as usize);
            }
        }
        self
    }
    /// If given index is out of bounds, we return self unchanged
    pub fn update_with<F>(self, idx: usize, f: F) -> Self
    where
        F: FnOnce(&'a T) -> T::Cloned<'a>,
    {
        self.then_update_with(idx, |x| Some(f(x)))
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
    unsafe fn extend_inner_lifetime<'c>(clone: Self::Cloned<'c>) -> Self
    where
        Self: 'c,
    {
        unsafe { core::mem::transmute(clone) }
    }
}

impl<const B: usize, T, A: Allocator + Clone> Succeed for PersVec<'_, T, B, A>
where
    [(); bytes(B)]:,
{
    unsafe fn succeed<'c>(&'c self, clone: &Self::Cloned<'c>) {
        if self.id == clone.id && self.total_length != 0 && clone.total_length != 0 {
            let orig_depth = Self::depth(self.total_length);
            let clone_depth = Self::depth(clone.total_length);

            let min_depth = orig_depth.min(clone_depth);

            let orig_length_without_tail = self.total_length - Self::tail_length(self.total_length);
            let clone_length_without_tail =
                clone.total_length - Self::tail_length(clone.total_length);
            let min_length_without_tail = orig_length_without_tail.min(clone_length_without_tail);

            let orig_head = &self.head;
            let orig_tail = &self.tail;
            let clone_head = &clone.head;
            let clone_tail = &clone.tail;

            // AT ANY POINT IN TRAVERSAL IF WE ENCOUNTER A BORROWED NODE WE NEED NOT CONTINUE THERE
            // NO SUCCESSION ALLOWED PAST ANY BORROWS
            if self.total_length.div_ceil(B) == clone.total_length.div_ceil(B) {
                // 1: self and clone are within same node boundary
                //  =>  can directly succeed_nodes on head, and on tails with min(tail_lengths)
                let orig_tail_length = Self::tail_length(self.total_length);
                let clone_tail_length = Self::tail_length(clone.total_length);
                let min_tail_length = orig_tail_length.min(clone_tail_length);
                unsafe {
                    orig_head.succeed_nodes(clone_head, min_length_without_tail, min_depth);
                    orig_tail.succeed_nodes(clone_tail, min_tail_length, 0);
                }
            } else if orig_depth == clone_depth {
                // 2: self and clone have the same depth, but different node boundaries
                //  =>  tails no longer refer to the same node location, succeed_nodes no longer
                //      valid, instead requires we traverse down heads in the same process as
                //      succeed_nodes on a length of min_length_with_tail, and substitute the tail
                //      for where it should be at the end of the shorter tree, if we reach it
                unsafe {
                    if self.total_length > clone.total_length {
                        // special case: the only length is in the tail, so we succeed that
                        let clone_tail_length = Self::tail_length(clone.total_length);
                        if min_length_without_tail == 0 {
                            orig_head.succeed_nodes(clone_tail, clone_tail_length, 0);
                        } else {
                            orig_head.succeed_nodes_missing_clone_tail(
                                clone_head,
                                min_length_without_tail,
                                min_depth,
                                clone_tail,
                                clone_tail_length,
                            );
                        }
                    } else {
                        // self.total_length < clone.total_length
                        // special case: the only length is in the tail, so we succeed that
                        let orig_tail_length = Self::tail_length(self.total_length);
                        if min_length_without_tail == 0 {
                            orig_tail.succeed_nodes(clone_head, orig_tail_length, 0);
                        } else {
                            orig_head.succeed_nodes_missing_self_tail(
                                clone_head,
                                min_length_without_tail,
                                min_depth,
                                orig_tail,
                                orig_tail_length,
                            );
                        }
                    }
                }
            } else if min_length_without_tail / B == B.pow(min_depth) {
                // 3: self and clone have different depths, and the shorter tree is "full",
                //    that is, `length_without_tail(short) / B == B.pow(short_depth)`
                //  =>  traverse down the leftmost nodes of the longer vector until at a depth of
                //      short_depth + 1, then take the leftmost node there, which we will call
                //      inner_long_head, and separately, in the second leftmost node, traverse down
                //      the leftmost node to a depth of 0 to obtain the inner_long_tail. We can now
                //      call succeed_nodes on short_head and inner_long_head, and on short_tail and
                //      inner_long_tail with a length of short_tail_length, if inner_tail is owned
                let delta = orig_depth as isize - clone_depth as isize;
                let mut node = if delta > 0 { orig_head } else { clone_head };
                for _ in 0..(delta.abs() - 1) {
                    if unsafe { !node.owned_branches.get().as_ref().unwrap().get(0) } {
                        return;
                    }
                    node = unsafe { node.branches.nodes.get(0).unwrap().as_ref() };
                }
                let owned_head = unsafe { node.owned_branches.get().as_ref().unwrap().get(0) };
                let inner_long_head = unsafe { node.branches.nodes.get(0).unwrap().as_ref() };

                let mut owned_tail = unsafe { node.owned_branches.get().as_ref().unwrap().get(1) };
                node = unsafe { node.branches.nodes.get(1).unwrap().as_ref() };
                for _ in 0..min_depth {
                    if !owned_tail || unsafe { !node.owned_branches.get().as_ref().unwrap().get(0) }
                    {
                        owned_tail = false;
                        break;
                    }
                    node = unsafe { node.branches.nodes.get(0).unwrap().as_ref() };
                }
                let inner_long_tail = node;

                if delta > 0 {
                    let clone_tail_length = Self::tail_length(clone.total_length);
                    unsafe {
                        if owned_head {
                            inner_long_head.succeed_nodes(
                                clone_head,
                                min_length_without_tail,
                                min_depth,
                            );
                        }
                        if owned_tail {
                            inner_long_tail.succeed_nodes(clone_tail, clone_tail_length, 0);
                        }
                    }
                } else {
                    let orig_tail_length = Self::tail_length(self.total_length);
                    unsafe {
                        if owned_head {
                            orig_head.succeed_nodes(
                                inner_long_head,
                                min_length_without_tail,
                                min_depth,
                            );
                        }
                        if owned_tail {
                            orig_tail.succeed_nodes(inner_long_tail, orig_tail_length, 0);
                        }
                    }
                }
            } else {
                // 4: self and clone have different depths, and the shorter tree isnt "full",
                //  =>  traverse down the leftmost nodes of the longer vector until at a depth of
                //      short_depth, this node will be inner_long_head. Since the node location of
                //      short_tail would be within inner_long_head, succeed_nodes is not valid,
                //      instead requires we traverse down heads in the same process as
                //      succeed_nodes on a length of min_length_with_tail, and substitute the tail
                //      for where it should be at the end of the shorter tree, if we reach it
                let delta = orig_depth as isize - clone_depth as isize;
                let mut node = if delta > 0 { orig_head } else { clone_head };
                for _ in 0..delta.abs() {
                    if unsafe { !node.owned_branches.get().as_ref().unwrap().get(0) } {
                        return;
                    }
                    node = unsafe { node.branches.nodes.get(0).unwrap().as_ref() };
                }
                let inner_long_head = node;
                unsafe {
                    if delta > 0 {
                        // special case: the only length is in the tail, so we succeed the tail
                        let clone_tail_length = Self::tail_length(clone.total_length);
                        if min_length_without_tail == 0 {
                            inner_long_head.succeed_nodes(clone_tail, clone_tail_length, 0);
                        } else {
                            inner_long_head.succeed_nodes_missing_clone_tail(
                                clone_head,
                                min_length_without_tail,
                                min_depth,
                                clone_tail,
                                clone_tail_length,
                            );
                        }
                    } else {
                        // special case: the only length is in the tail, so we succeed the tail
                        let orig_tail_length = Self::tail_length(self.total_length);
                        if min_length_without_tail == 0 {
                            orig_tail.succeed_nodes(inner_long_head, orig_tail_length, 0);
                        } else {
                            orig_head.succeed_nodes_missing_self_tail(
                                inner_long_head,
                                min_length_without_tail,
                                min_depth,
                                orig_tail,
                                orig_tail_length,
                            );
                        }
                    }
                }
            }
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
    vector: &'a PersVec<'a, T, B, A>,
}

impl<'a, const B: usize, T, A: Allocator + Clone> Iterator for IterPersVec<'a, T, B, A>
where
    [(); bytes(B)]:,
{
    // TODO could pop items, or just chain iterators of branches for impl, will bm this and ensure
    // we get iter extension traits
    type Item = &'a T;
    // these unsafes are fine to extend the lifetime of element borrows
    // since vector cant be mutated or taken once it enters the iterator
    fn next(&mut self) -> Option<Self::Item> {
        self.front += 1;
        if self.front > self.back {
            return None;
        };
        self.vector.get(self.front - 1)
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.front += n + 1;
        if self.front > self.back {
            return None;
        };
        self.vector.get(self.front - 1)
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
    // these unsafes are fine to extend the lifetime of element borrows
    // since vector cant be mutated or taken once it enters the iterator
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back = self.back.checked_sub(1)?;
        if self.front > self.back {
            return None;
        };
        self.vector.get(self.back)
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
    use crate::{borrow::Succeed, *};
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
    #[test]
    fn succeed_update() {
        let mut new: PersVec<PersVec<usize, 2>, 2> = pers_vec![];
        for _ in 0..10 {
            new = new.append(PersVec::new());
        }

        for i in 1..=10 {
            new = new.update_with(i - 1, |_| PersVec::from_iter(0..i))
        }

        assert!(new.get(10).is_none());
        for i in 1..=10 {
            for j in 0..i {
                assert_eq!(new.get(i - 1).unwrap().get(j), Some(&j));
            }
            assert_eq!(new.get(i - 1).unwrap().get(i), None);
        }

        for i in 0..10 {
            new = new.update_with(i, |pv| {
                (1..=10)
                    .map(|x| pv.last().map_or(x - 1, |start| start + x))
                    .fold(pv.partial_clone(), PersVec::append)
            });
        }
        for i in 0..10 {
            let inner = new.get(i).unwrap();
            for j in 0..=(i + 10) {
                assert_eq!(inner.get(j), Some(&j));
            }
        }
        for i in 0..10 {
            new = new.update_with(i, |pv| pv.partial_clone().append(*pv.last().unwrap() + 1));
        }
        for i in 0..10 {
            let inner = new.get(i).unwrap();
            for j in 0..=(i + 11) {
                assert_eq!(inner.get(j), Some(&j));
            }
        }
        for i in 0..10 {
            new = new.update_with(i, |pv| pv.partial_clone().pop().update(0, usize::MAX));
        }

        for i in 0..10 {
            let inner = new.get(i).unwrap();
            assert_eq!(inner.get(0), Some(&usize::MAX));
            for j in 1..=(i + 10) {
                assert_eq!(inner.get(j), Some(&j));
            }
            assert_eq!(inner.get(i + 11), None);
        }

        for i in 0..10 {
            new = new.update_with(i, |pv| {
                (0..10)
                    .fold(pv.partial_clone(), |v, _| v.pop())
                    .update(0, 0)
            });
        }
        for i in 1..=10 {
            for j in 0..i {
                assert_eq!(new.get(i - 1).unwrap().get(j), Some(&j));
            }
            assert_eq!(new.get(i - 1).unwrap().get(i), None);
        }
    }
    #[test]
    fn many_succeed() {
        let mut new: PersVec<usize, 4> = pers_vec![];
        for i in 0..100 {
            let clone = new.partial_clone().append(i);
            unsafe { new.succeed(&clone) };
            new = unsafe { PartialClone::extend_inner_lifetime(clone) };
            println!("{i}");
            for j in 0..=i {
                assert_eq!(new.get(j), Some(&j));
            }
        }
    }
}
