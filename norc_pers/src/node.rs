use crate::{
    BRANCH_FACTOR, BitArray,
    alloc::Allocator,
    borrow::{Consign, Lend, WordAddress},
    boxed::Box,
    into_non_null,
};
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Range,
    ptr::{self, NonNull},
};

pub(crate) struct Branches<T: WordAddress> {
    array: [*const T::Pointee; BRANCH_FACTOR],
}
impl<T: WordAddress> Branches<T> {
    pub(crate) const fn none() -> ManuallyDrop<Self> {
        ManuallyDrop::new(Branches {
            array: [ptr::null(); _],
        })
    }
    pub(crate) fn first(value: *const T::Pointee) -> ManuallyDrop<Self> {
        let mut array = [ptr::null(); BRANCH_FACTOR];
        array[0] = value;
        ManuallyDrop::new(Branches { array })
    }
    pub(crate) fn append(&mut self, len: u8, value: T) {
        self.set(len, value);
    }
    pub(crate) fn pop(&mut self, len: u8) -> *const T::Pointee {
        core::mem::replace(&mut self.array[len as usize - 1], ptr::null())
    }
    pub(crate) fn get(&self, idx: u8) -> &*const T::Pointee {
        &self.array[idx as usize]
    }
    // put value in array without dropping
    pub(crate) fn set(&mut self, idx: u8, value: T) {
        self.array[idx as usize] = value.into_addr();
    }
    pub(crate) fn set_by_ptr(&mut self, idx: u8, p: *const T::Pointee) {
        self.array[idx as usize] = p;
    }
    pub(crate) fn get_mut(&mut self, idx: u8) -> &mut *const T::Pointee {
        &mut self.array[idx as usize]
    }
    pub(crate) fn range_mut(&mut self, r: Range<u8>) -> &mut [*const T::Pointee] {
        &mut self.array[Range {
            start: r.start as usize,
            end: r.end as usize,
        }]
    }
}
pub(crate) union AmbiguousBranches<T: WordAddress, A: Allocator + Clone> {
    pub values: ManuallyDrop<Branches<T>>,
    pub nodes: ManuallyDrop<Branches<Option<NonNull<Node<T, A>>>>>,
    _phantom: PhantomData<A>,
}

pub(crate) struct Node<T: WordAddress, A: Allocator + Clone> {
    pub owned_branches: UnsafeCell<BitArray>, // UnsafeCell here allows us to impl succeed_nodes
    // on refs, since sharing will still be valid
    // during succession
    pub branches: AmbiguousBranches<T, A>,
}

pub(crate) struct PopPair<T: WordAddress, A: Allocator + Clone> {
    pub head: Node<T, A>,
    pub tail: Node<T, A>,
}
impl<T: WordAddress, A: Allocator + Clone> Node<T, A> {
    pub(crate) const fn empty() -> Self {
        Self {
            owned_branches: UnsafeCell::new(BitArray::zeroes()),
            branches: AmbiguousBranches::<T, A> {
                values: Branches::none(),
            },
        }
    }
    pub(crate) fn new_internal(child_node: Self, allocator: A) -> Self {
        let nodes = Branches::first(
            Box::into_raw_with_allocator(Box::<Self, A>::new_in(child_node, allocator)).0,
        );
        let mut owned_branches = BitArray::zeroes();
        owned_branches.set(0);
        Self {
            owned_branches: UnsafeCell::new(owned_branches),
            branches: AmbiguousBranches::<T, A> { nodes },
        }
    }
    pub(crate) fn partial_borrow(&self) -> Self {
        Self {
            owned_branches: UnsafeCell::new(BitArray::zeroes()),
            branches: unsafe { core::mem::transmute_copy(&self.branches) },
        }
    }
    pub(crate) fn branches_append_value(mut self, value: T, length: usize) -> Self {
        debug_assert!(length < BRANCH_FACTOR);
        unsafe { (*self.branches.values).append(length as u8, value) };
        self.owned_branches.get_mut().set(length);
        self
    }
    pub(crate) fn branches_pop_value(mut self, length: usize) -> Self {
        debug_assert!(length <= BRANCH_FACTOR);
        let value = unsafe { (*self.branches.values).pop(length as u8) };
        if self.owned_branches.get_mut().get(length - 1) {
            drop(unsafe { core::mem::transmute_copy::<T, T>(T::reform(&value)) });
            self.owned_branches.get_mut().unset(length - 1);
        }
        self
    }
    pub(crate) fn branches_append_node(mut self, node: Self, length: usize, allocator: A) -> Self {
        debug_assert!(length < BRANCH_FACTOR);
        unsafe {
            (*self.branches.nodes).append(
                length as u8,
                Some(into_non_null(Box::<Self, A>::new_in(node, allocator))),
            );
        }
        self.owned_branches.get_mut().set(length);
        self
    }
    pub(crate) fn branches_pop_node(mut self, length: usize, allocator: A) -> PopPair<T, A> {
        debug_assert!(length <= BRANCH_FACTOR);
        let node =
            NonNull::new(unsafe { (*self.branches.nodes).pop(length as u8) as *mut Self }).unwrap();
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
        let branches_amount = length.div_ceil(BRANCH_FACTOR.pow(depth)) as u8;
        if depth == 0 {
            for (i, value) in unsafe { (*self.branches.values).range_mut(0..branches_amount) }
                .iter()
                .enumerate()
            {
                if self.owned_branches.get_mut().get(i) {
                    drop(unsafe { core::mem::transmute_copy::<T, T>(T::reform(value)) });
                }
            }
        } else {
            let next_length = BRANCH_FACTOR.pow(depth);
            for (i, node) in unsafe { (*self.branches.nodes).range_mut(0..branches_amount) }
                .iter_mut()
                .enumerate()
            {
                let boxed_node = *node as *mut _;
                if i == branches_amount as usize - 1 && !length.is_multiple_of(next_length) {
                    if self
                        .owned_branches
                        .get_mut()
                        .get(branches_amount as usize - 1)
                    {
                        let last_length = length % next_length;
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
        let next_length = length_without_tail % BRANCH_FACTOR.pow(depth);
        if depth == 0 {
            debug_assert_eq!(length_without_tail, 0);
            tail
        } else if depth == 1 {
            self.branches_append_node(tail, length_without_tail / BRANCH_FACTOR, allocator)
        } else if next_length == 0 {
            // add a new node with the correct depth
            let mut node = tail;
            for _ in 0..(depth - 1) {
                node = Node::new_internal(node, allocator.clone());
            }
            let branches_amount = length_without_tail / BRANCH_FACTOR.pow(depth);
            self.branches_append_node(node, branches_amount, allocator.clone())
        } else {
            let branches_amount = length_without_tail.div_ceil(BRANCH_FACTOR.pow(depth)) as u8;
            let node = unsafe { (*self.branches.nodes).get_mut(branches_amount - 1) };
            if self
                .owned_branches
                .get_mut()
                .get(branches_amount as usize - 1)
            {
                unsafe {
                    (*node as *mut Self).write(node.read().vector_append_tail(
                        tail,
                        next_length,
                        depth - 1,
                        allocator.clone(),
                    ))
                };
            } else {
                *node = unsafe {
                    Box::into_raw_with_allocator(Box::<Self, A>::new_in(
                        node.as_ref().unwrap().partial_borrow().vector_append_tail(
                            tail,
                            next_length,
                            depth - 1,
                            allocator.clone(),
                        ),
                        allocator.clone(),
                    ))
                    .0
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
    ) -> PopPair<T, A> {
        debug_assert!(depth > 0);
        let next_length = length % BRANCH_FACTOR.pow(depth);
        let next_length = if next_length == 0 {
            BRANCH_FACTOR.pow(depth)
        } else {
            next_length
        };
        if depth == 1 {
            self.branches_pop_node(length / BRANCH_FACTOR, allocator)
        } else if next_length == BRANCH_FACTOR {
            let PopPair { head, mut tail } = self
                .branches_pop_node(length.div_ceil(BRANCH_FACTOR.pow(depth)), allocator.clone());
            for _ in 0..(depth - 1) {
                PopPair { tail, .. } = tail.branches_pop_node(1, allocator.clone());
            }
            PopPair { head, tail }
        } else {
            let branches_amount = length.div_ceil(BRANCH_FACTOR.pow(depth));
            let node = unsafe { (*self.branches.nodes).get_mut((branches_amount - 1) as u8) };
            let tail;
            // TODO is everything dropped here?
            if self.owned_branches.get_mut().get(branches_amount - 1) {
                let PopPair { head, tail: t } = unsafe { node.read() }.vector_pop_tail(
                    next_length,
                    depth - 1,
                    allocator.clone(),
                );
                tail = t;
                unsafe { (*node as *mut Self).write(head) };
            } else {
                let PopPair { head, tail: t } = unsafe { node.as_ref() }
                    .unwrap()
                    .partial_borrow()
                    .vector_pop_tail(next_length, depth - 1, allocator.clone());
                tail = t;
                *node =
                    Box::into_raw_with_allocator(Box::<Self, A>::new_in(head, allocator.clone())).0;
                self.owned_branches.get_mut().set(branches_amount - 1);
            }
            PopPair { head: self, tail }
        }
    }
}

impl<T: WordAddress, A: Allocator + Clone> Node<T, A>
where
    T::Pointee: Consign,
{
    // after this call, self will be the borrower of all shared values and clone will be the owner
    pub(crate) unsafe fn succeed_nodes(&self, clone: &Self, length: usize, depth: u32) {
        let branch_length = length.div_ceil(BRANCH_FACTOR.pow(depth));

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);
        for i in branch_length..BRANCH_FACTOR {
            new_owner_flags.update(i, clone_owned_flags.get(i));
            new_borrower_flags.update(i, self_owned_flags.get(i));
        }
        unsafe {
            self.owned_branches.get().write(new_borrower_flags);
            clone.owned_branches.get().write(new_owner_flags);
        }
        if depth == 0 {
            for i in 0..branch_length {
                // If clone owns this element, we attempt to consign
                //  If self does not own their copy of this element, we could still lend it, so we
                //  must attempt to consign
                // If this element is independent from the element in self, consign will noop
                if clone_owned_flags.get(i) {
                    let idx = i as u8;
                    let Some(self_child): Option<&T::Pointee> =
                        (unsafe { self.branches.values.get(idx).as_ref() })
                    else {
                        continue;
                    };
                    let Some(clone_child) = (unsafe {
                        clone
                            .branches
                            .values
                            .get(idx)
                            .cast::<<T::Pointee as Lend>::Lended<'_>>()
                            .as_ref()
                    }) else {
                        continue;
                    };
                    unsafe { Consign::consign(self_child, clone_child) };
                }
            }
            return;
        }

        for i in 0..branch_length {
            // TODO optimize loop condition
            if new_borrower_flags.get(i) {
                let next_full_length = BRANCH_FACTOR.pow(depth);
                let next_length = if i == branch_length - 1 {
                    let tmp = length % next_full_length;
                    if tmp == 0 { next_full_length } else { tmp }
                } else {
                    next_full_length
                };
                let idx = i as u8;
                let clone_child = unsafe { clone.branches.nodes.get(idx).as_ref().unwrap() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .as_ref()
                        .unwrap()
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
        let next_full_length = BRANCH_FACTOR.pow(depth);
        let branch_length = length_without_tail.div_ceil(next_full_length);

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);

        for i in branch_length..BRANCH_FACTOR {
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
                for i in 0..branch_length {
                    // TODO optimize loop condition
                    if clone_owned_flags.get(i) {
                        let idx = i as u8;
                        let Some(self_child) = (unsafe { self.branches.values.get(idx).as_ref() })
                        else {
                            continue;
                        };
                        let Some(clone_child) = (unsafe {
                            clone
                                .branches
                                .values
                                .get(idx)
                                .cast::<<T::Pointee as Lend>::Lended<'_>>()
                                .as_ref()
                        }) else {
                            continue;
                        };
                        unsafe { Consign::consign(self_child, clone_child) };
                    }
                }
                return;
            } else if last_length == 0 && clone_owned_flags.get(last_idx) {
                let mut clone =
                    unsafe { clone.branches.nodes.get(last_idx as u8).as_ref().unwrap() };
                for _ in 0..(depth - 1) {
                    unsafe {
                        if !clone.owned_branches.get().as_ref().unwrap().get(0) {
                            break 'label;
                        }
                        clone = clone.branches.nodes.get(0).as_ref().unwrap();
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
                let clone_child = unsafe { clone.branches.nodes.get(idx).as_ref().unwrap() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .as_ref()
                        .unwrap()
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
                    .as_ref()
                    .unwrap()
            };
            if last_length == 0 {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .as_ref()
                        .unwrap()
                        .succeed_nodes(clone_child, next_full_length, depth - 1);
                }
            } else {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .as_ref()
                        .unwrap()
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
        let next_full_length = BRANCH_FACTOR.pow(depth);
        let branch_length = length_without_tail.div_ceil(next_full_length);

        let self_owned_flags = unsafe { self.owned_branches.get().read() };
        let clone_owned_flags = unsafe { clone.owned_branches.get().read() };
        let mut new_owner_flags = self_owned_flags.or(clone_owned_flags);
        let mut new_borrower_flags = self_owned_flags.and(clone_owned_flags);

        for i in branch_length..BRANCH_FACTOR {
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
                for i in 0..branch_length {
                    // TODO optimize loop condition
                    if clone_owned_flags.get(i) {
                        let idx = i as u8;
                        let Some(self_child) = (unsafe { self.branches.values.get(idx).as_ref() })
                        else {
                            continue;
                        };
                        let Some(clone_child) = (unsafe {
                            clone
                                .branches
                                .values
                                .get(idx)
                                .cast::<<T::Pointee as Lend>::Lended<'_>>()
                                .as_ref()
                        }) else {
                            continue;
                        };
                        unsafe { Consign::consign(self_child, clone_child) };
                    }
                }
                return;
            } else if last_length == 0 && self_owned_flags.get(last_idx) {
                let mut orig = unsafe { self.branches.nodes.get(last_idx as u8).as_ref().unwrap() };
                for _ in 0..(depth - 1) {
                    unsafe {
                        if !orig.owned_branches.get().as_ref().unwrap().get(0) {
                            break 'label;
                        }
                        orig = orig.branches.nodes.get(0).as_ref().unwrap();
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
                let clone_child = unsafe { clone.branches.nodes.get(idx).as_ref().unwrap() };
                unsafe {
                    self.branches
                        .nodes
                        .get(idx)
                        .as_ref()
                        .unwrap()
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
                    .as_ref()
                    .unwrap()
            };
            if last_length == 0 {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .as_ref()
                        .unwrap()
                        .succeed_nodes(clone_child, next_full_length, depth - 1);
                }
            } else {
                unsafe {
                    self.branches
                        .nodes
                        .get(last_branch_idx as u8)
                        .as_ref()
                        .unwrap()
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
