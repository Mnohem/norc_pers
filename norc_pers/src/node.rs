use crate::{BitArray, alloc::Allocator, boxed::Box, bytes, into_non_null};
use core::{cell::UnsafeCell, marker::PhantomData, mem::ManuallyDrop, ops::Range, ptr::NonNull};

pub(crate) struct Branches<const BRANCH_FACTOR: usize, T> {
    array: [Option<NonNull<T>>; BRANCH_FACTOR],
}
impl<const B: usize, T> Branches<B, T> {
    pub(crate) const fn none() -> ManuallyDrop<Self> {
        ManuallyDrop::new(Branches { array: [None; B] })
    }
    pub(crate) fn first(value: NonNull<T>) -> ManuallyDrop<Self> {
        let mut array = [None; B];
        array[0] = Some(value);
        ManuallyDrop::new(Branches { array })
    }
    pub(crate) fn append(&mut self, len: u8, value: NonNull<T>) -> bool {
        self.array
            .get_mut(len as usize)
            .map(|x| *x = Some(value))
            .is_some()
    }
    pub(crate) fn pop(&mut self, len: u8) -> Option<NonNull<T>> {
        self.array
            .get_mut(len.checked_sub(1)? as usize)
            .and_then(|x| x.take())
    }
    pub(crate) fn get(&self, idx: u8) -> Option<NonNull<T>> {
        self.array[idx as usize]
    }
    pub(crate) fn get_mut(&mut self, idx: u8) -> &mut Option<NonNull<T>> {
        &mut self.array[idx as usize]
    }
    pub(crate) fn range_mut(&mut self, r: Range<u8>) -> &mut [Option<NonNull<T>>] {
        &mut self.array[Range {
            start: r.start as usize,
            end: r.end as usize,
        }]
    }
    pub(crate) unsafe fn unchecked_range_mut(&mut self, r: Range<u8>) -> &mut [NonNull<T>] {
        unsafe {
            core::mem::transmute(
                &mut self.array[Range {
                    start: r.start as usize,
                    end: r.end as usize,
                }],
            )
        }
    }
}
pub(crate) union AmbiguousBranches<const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    pub values: ManuallyDrop<Branches<B, T>>,
    pub nodes: ManuallyDrop<Branches<B, Node<B, T, A>>>,
    _phantom: PhantomData<A>,
}

pub(crate) struct Node<const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    pub owned_branches: UnsafeCell<BitArray<B>>, // UnsafeCell here allows us to impl succeed_nodes
    // on refs, since sharing will still be valid
    // during succession
    pub branches: AmbiguousBranches<B, T, A>,
}

pub(crate) struct PopPair<const B: usize, T, A: Allocator + Clone>
where
    [(); bytes(B)]:,
{
    pub head: Node<B, T, A>,
    pub tail: Node<B, T, A>,
}
impl<const B: usize, T, A: Allocator + Clone> Node<B, T, A>
where
    [(); bytes(B)]:,
{
    pub(crate) const fn empty() -> Self {
        Self {
            owned_branches: UnsafeCell::new(BitArray::new()),
            branches: AmbiguousBranches::<B, T, A> {
                values: Branches::none(),
            },
        }
    }
    pub(crate) fn _new_leaf(initial_value: T, allocator: A) -> Self {
        let values = Branches::first(unsafe {
            into_non_null(Box::<T, A>::new_in(initial_value, allocator))
        });
        let mut owned_branches = BitArray::new();
        owned_branches.set(0);
        Self {
            owned_branches: UnsafeCell::new(owned_branches),
            branches: AmbiguousBranches::<B, T, A> { values },
        }
    }
    pub(crate) fn _new_leaf_ref(initial_ref: &T) -> Self {
        let values = Branches::first(NonNull::from_ref(initial_ref));
        Self {
            owned_branches: UnsafeCell::new(BitArray::new()),
            branches: AmbiguousBranches::<B, T, A> { values },
        }
    }
    pub(crate) fn new_internal(child_node: Self, allocator: A) -> Self {
        let nodes = Branches::first(unsafe {
            into_non_null(Box::<Self, A>::new_in(child_node, allocator))
        });
        let mut owned_branches = BitArray::new();
        owned_branches.set(0);
        Self {
            owned_branches: UnsafeCell::new(owned_branches),
            branches: AmbiguousBranches::<B, T, A> { nodes },
        }
    }
    pub(crate) fn partial_borrow(&self) -> Self {
        Self {
            owned_branches: UnsafeCell::new(BitArray::new()),
            branches: unsafe { core::mem::transmute_copy(&self.branches) },
        }
    }
    pub(crate) fn branches_append_value(mut self, value: T, length: usize, allocator: A) -> Self {
        debug_assert!(length < B);
        unsafe {
            debug_assert!((*self.branches.values).append(
                length as u8,
                into_non_null(Box::<T, A>::new_in(value, allocator)),
            ))
        }
        self.owned_branches.get_mut().set(length);
        self
    }
    pub(crate) fn branches_pop_value(mut self, length: usize, allocator: A) -> Self {
        debug_assert!(length <= B);
        let value = unsafe { (*self.branches.values).pop(length as u8) };
        debug_assert!(value.is_some());
        if self.owned_branches.get_mut().get(length - 1) {
            drop(unsafe { Box::from_raw_in(value.unwrap_unchecked().as_ptr(), allocator) });
            self.owned_branches.get_mut().unset(length - 1);
        }
        self
    }
    pub(crate) fn branches_append_node(mut self, node: Self, length: usize, allocator: A) -> Self {
        debug_assert!(length < B);
        unsafe {
            debug_assert!((*self.branches.nodes).append(
                length as u8,
                into_non_null(Box::<Self, A>::new_in(node, allocator)),
            ))
        }
        self.owned_branches.get_mut().set(length);
        self
    }
    pub(crate) fn branches_pop_node(mut self, length: usize, allocator: A) -> PopPair<B, T, A> {
        debug_assert!(length <= B);
        let node = unsafe { (*self.branches.nodes).pop(length as u8) }.unwrap();
        PopPair {
            tail: if self.owned_branches.get_mut().get(length - 1) {
                self.owned_branches.get_mut().unset(length - 1);
                Box::into_inner(unsafe { Box::from_raw_in(node.as_ptr(), allocator) })
            } else {
                unsafe { node.as_ref() }.partial_borrow()
            },
            head: self,
        }
    }
    pub(crate) fn drop_node(&mut self, length: usize, depth: u32, allocator: A) {
        let branches_amount = length.div_ceil(B.pow(depth)) as u8;
        if depth == 0 {
            for (i, value) in unsafe { (*self.branches.values).range_mut(0..branches_amount) }
                .iter()
                .enumerate()
            {
                if self.owned_branches.get_mut().get(i) {
                    unsafe {
                        drop(Box::<T, A>::from_raw_in(
                            value.unwrap().as_ptr(),
                            allocator.clone(),
                        ))
                    };
                }
            }
        } else {
            let next_length = B.pow(depth);
            for (i, node) in unsafe { (*self.branches.nodes).range_mut(0..branches_amount) }
                .iter_mut()
                .enumerate()
            {
                if i == branches_amount as usize - 1 && !length.is_multiple_of(next_length) {
                    if self
                        .owned_branches
                        .get_mut()
                        .get(branches_amount as usize - 1)
                    {
                        let last_length = length % next_length;
                        let boxed_node = node.unwrap().as_ptr();
                        Self::drop_node(
                            &mut Box::<Self, A>::into_inner(unsafe {
                                Box::<Self, A>::from_raw_in(boxed_node, allocator.clone())
                            }),
                            last_length,
                            depth - 1,
                            allocator.clone(),
                        )
                    }
                } else if self.owned_branches.get_mut().get(i) {
                    let boxed_node = node.unwrap().as_ptr();
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
    pub(crate) fn vector_append_tail(
        mut self,
        tail: Self,
        length_without_tail: usize,
        depth: u32,
        allocator: A,
    ) -> Self {
        let next_length = length_without_tail % B.pow(depth);
        if depth == 0 {
            debug_assert_eq!(length_without_tail, 0);
            tail
        } else if depth == 1 {
            self.branches_append_node(tail, length_without_tail / B, allocator)
        } else if next_length == 0 {
            // add a new node with the correct depth
            let mut node = tail;
            for _ in 0..(depth - 1) {
                node = Node::new_internal(node, allocator.clone());
            }
            let branches_amount = length_without_tail / B.pow(depth);
            self.branches_append_node(node, branches_amount, allocator.clone())
        } else {
            let branches_amount = length_without_tail.div_ceil(B.pow(depth)) as u8;
            let node = unsafe { (*self.branches.nodes).unchecked_range_mut(0..branches_amount) }
                .last_mut()
                .unwrap();
            if self
                .owned_branches
                .get_mut()
                .get(branches_amount as usize - 1)
            {
                unsafe {
                    node.write(node.read().vector_append_tail(
                        tail,
                        next_length,
                        depth - 1,
                        allocator.clone(),
                    ))
                };
            } else {
                *node = unsafe {
                    into_non_null(Box::<Self, A>::new_in(
                        node.as_ref().partial_borrow().vector_append_tail(
                            tail,
                            next_length,
                            depth - 1,
                            allocator.clone(),
                        ),
                        allocator.clone(),
                    ))
                };
            }
            self.owned_branches
                .get_mut()
                .set(branches_amount as usize - 1);
            self
        }
    }
    pub(crate) fn vector_pop_tail(
        mut self,
        length: usize,
        depth: u32,
        allocator: A,
    ) -> PopPair<B, T, A> {
        debug_assert!(depth > 0);
        let next_length = length % B.pow(depth);
        let next_length = if next_length == 0 {
            B.pow(depth)
        } else {
            next_length
        };
        if depth == 1 {
            self.branches_pop_node(length / B, allocator)
        } else if next_length == B {
            let PopPair { head, mut tail } =
                self.branches_pop_node(length.div_ceil(B.pow(depth)), allocator.clone());
            for _ in 0..(depth - 1) {
                PopPair { tail, .. } = tail.branches_pop_node(1, allocator.clone());
            }
            PopPair { head, tail }
        } else {
            let branches_amount = length.div_ceil(B.pow(depth));
            let node = unsafe { (*self.branches.nodes).get_mut((branches_amount - 1) as u8) }
                .as_mut()
                .expect("Null pointer");
            let tail;
            // TODO is everything dropped here?
            if self.owned_branches.get_mut().get(branches_amount - 1) {
                let PopPair { head, tail: t } = unsafe { node.read() }.vector_pop_tail(
                    next_length,
                    depth - 1,
                    allocator.clone(),
                );
                tail = t;
                unsafe { node.write(head) };
            } else {
                let PopPair { head, tail: t } = unsafe { node.as_ref() }
                    .partial_borrow()
                    .vector_pop_tail(next_length, depth - 1, allocator.clone());
                tail = t;
                *node = unsafe { into_non_null(Box::<Self, A>::new_in(head, allocator.clone())) };
                self.owned_branches.get_mut().set(branches_amount - 1);
            }
            PopPair { head: self, tail }
        }
    }
    // after this call, self will be the borrower of all shared values and clone will be the owner
    pub(crate) unsafe fn succeed_nodes(&self, clone: &Self, length: usize, depth: u32) {
        let branch_length = length.div_ceil(B.pow(depth));

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);
        for i in branch_length..B {
            new_owner_flags.update(i, clone_owned_flags.get(i));
            new_borrower_flags.update(i, self_owned_flags.get(i));
        }
        unsafe {
            self.owned_branches.get().write(new_borrower_flags);
            clone.owned_branches.get().write(new_owner_flags);
        }
        if depth == 0 {
            return;
        }

        for i in 0..branch_length {
            // TODO optimize loop condition
            if new_borrower_flags.get(i) {
                let next_full_length = B.pow(depth);
                let next_length = if i == branch_length - 1 {
                    let tmp = length % next_full_length;
                    if tmp == 0 { next_full_length } else { tmp }
                } else {
                    next_full_length
                };
                let idx = i as u8;
                let clone_child = unsafe { clone.branches.nodes.get(idx).unwrap().as_ref() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes(clone_child, next_length, depth - 1);
                }
            }
        }
    }
    pub(crate) unsafe fn succeed_nodes_missing_self_tail(
        &self,
        clone: &Self,
        length_without_tail: usize,
        depth: u32,
        self_tail_substitute: &Self,
        tail_length: usize,
    ) {
        let next_full_length = B.pow(depth);
        let branch_length = length_without_tail.div_ceil(next_full_length);

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);

        for i in branch_length..B {
            new_borrower_flags.update(i, self_owned_flags.get(i));
            new_owner_flags.update(i, clone_owned_flags.get(i));
        }
        unsafe {
            self.owned_branches.get().write(new_borrower_flags);
            clone.owned_branches.get().write(new_owner_flags);
        }
        let last_length = length_without_tail % next_full_length;

        'label: {
            let last_idx = branch_length;
            if depth == 0 {
                return;
            } else if last_length == 0 && clone_owned_flags.get(last_idx) {
                let mut clone =
                    unsafe { clone.branches.nodes.get(last_idx as u8).unwrap().as_ref() };
                for _ in 0..(depth - 1) {
                    unsafe {
                        if !clone.owned_branches.get().as_ref().unwrap().get(0) {
                            break 'label;
                        }
                        clone = clone.branches.nodes.get(0).unwrap().as_ref();
                    }
                }
                unsafe { self_tail_substitute.succeed_nodes(clone, tail_length, 0) };
            }
        }

        let last_branch_idx = branch_length - 1;

        for i in 0..last_branch_idx {
            if new_borrower_flags.get(i) {
                let next_length = next_full_length;
                let idx = i as u8;
                let clone_child = unsafe { clone.branches.nodes.get(idx).unwrap().as_ref() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes(clone_child, next_length, depth - 1);
                }
            }
        }
        if new_borrower_flags.get(last_branch_idx) {
            let clone_child = unsafe {
                clone
                    .branches
                    .nodes
                    .get(last_branch_idx as u8)
                    .unwrap()
                    .as_ref()
            };
            if last_length == 0 {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes(clone_child, next_full_length, depth - 1);
                }
            } else {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes_missing_self_tail(
                            clone_child,
                            last_length,
                            depth - 1,
                            self_tail_substitute,
                            tail_length,
                        );
                }
            };
        }
    }
    pub(crate) unsafe fn succeed_nodes_missing_clone_tail(
        &self,
        clone: &Self,
        length_without_tail: usize,
        depth: u32,
        clone_tail_substitute: &Self,
        tail_length: usize,
    ) {
        let next_full_length = B.pow(depth);
        let branch_length = length_without_tail.div_ceil(next_full_length);

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);

        for i in branch_length..B {
            new_borrower_flags.update(i, self_owned_flags.get(i));
            new_owner_flags.update(i, clone_owned_flags.get(i));
        }
        unsafe {
            self.owned_branches.get().write(new_borrower_flags);
            clone.owned_branches.get().write(new_owner_flags);
        }
        let last_length = length_without_tail % next_full_length;

        'label: {
            let last_idx = branch_length;
            if depth == 0 {
                return;
            } else if last_length == 0 && self_owned_flags.get(last_idx) {
                let mut orig = unsafe { self.branches.nodes.get(last_idx as u8).unwrap().as_ref() };
                for _ in 0..(depth - 1) {
                    unsafe {
                        if !orig.owned_branches.get().as_ref().unwrap().get(0) {
                            break 'label;
                        }
                        orig = orig.branches.nodes.get(0).unwrap().as_ref();
                    }
                }
                unsafe { orig.succeed_nodes(clone_tail_substitute, tail_length, 0) };
            }
        }

        let last_branch_idx = branch_length - 1;

        for i in 0..last_branch_idx {
            if new_borrower_flags.get(i) {
                let next_length = next_full_length;
                let idx = i as u8;
                let clone_child = unsafe { clone.branches.nodes.get(idx).unwrap().as_ref() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes(clone_child, next_length, depth - 1);
                }
            }
        }
        if new_borrower_flags.get(last_branch_idx) {
            let clone_child = unsafe {
                clone
                    .branches
                    .nodes
                    .get(last_branch_idx as u8)
                    .unwrap()
                    .as_ref()
            };
            if last_length == 0 {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes(clone_child, next_full_length, depth - 1);
                }
            } else {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .unwrap()
                        .as_ref()
                        .succeed_nodes_missing_clone_tail(
                            clone_child,
                            last_length,
                            depth - 1,
                            clone_tail_substitute,
                            tail_length,
                        );
                }
            };
        }
    }
}
