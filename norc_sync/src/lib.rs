#![expect(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(box_into_inner)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    marker::PhantomData,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicBool, AtomicPtr, Ordering},
};
use norc_pers::borrow::{PartialClone, Succeed};
cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        use allocator_api2::alloc::Allocator;
        use allocator_api2::boxed::Box;
        use allocator_api2::alloc::Global;
        use allocator_api2::sync::Arc;
    } else {
        extern crate alloc as mem;
        use mem::alloc::Allocator;
        use mem::boxed::Box;
        use mem::alloc::Global;
        use mem::sync::Arc;
    }
}

struct Node<T> {
    data: T,
    next: Option<NonNull<Node<T>>>,
}

pub struct Transactor<
    't,
    T: 't + PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone = Global,
> {
    history: AtomicPtr<Node<Arc<T, A>>>,
    ongoing_succession: AtomicBool,
    _inner_lifetime: PhantomData<&'t T>,
    allocator: A,
}

impl<'t, T: 't + PartialClone + Succeed, A: Allocator + Send + Sync + Clone> Drop
    for Transactor<'t, T, A>
{
    fn drop(&mut self) {
        let mut node = unsafe { Box::from_raw_in(*self.history.as_ptr(), self.allocator.clone()) };
        while let Some(next_ptr) = node.next {
            node = unsafe { Box::from_raw_in(next_ptr.as_ptr(), self.allocator.clone()) };
        }
    }
}
impl<'t, T: 't + PartialClone + Succeed> Transactor<'t, T, Global> {
    pub fn new(item: T) -> Self {
        Self::new_in(item, Global)
    }
}
impl<'t, T: 't + PartialClone + Succeed, A: 't + Allocator + Clone + Send + Sync>
    Transactor<'t, T, A>
{
    pub fn new_in(item: T, allocator: A) -> Self {
        Self {
            history: AtomicPtr::new(
                Box::into_raw_with_allocator(Box::new_in(
                    Node {
                        data: Arc::new_in(item, allocator.clone()),
                        next: None,
                    },
                    allocator.clone(),
                ))
                .0,
            ),
            ongoing_succession: AtomicBool::new(false),
            _inner_lifetime: PhantomData,
            allocator,
        }
    }
    /// Returns the snapshot that was just released from the history,
    /// or `None` if there is nothing to free or the lock was already taken
    pub fn release_last_snapshot(&self) -> Option<Arc<T::Cloned<'t>, A>> {
        if !self.ongoing_succession.swap(true, Ordering::Acquire) {
            let latest = self.history.load(Ordering::Acquire);
            let previous_ref = unsafe { latest.as_ref().unwrap_unchecked().next? };
            let previous =
                unsafe { Box::from_raw_in(previous_ref.as_ptr(), self.allocator.clone()) };
            unsafe {
                previous.data.succeed(
                    &latest
                        .cast::<Node<Arc<T::Cloned<'_>, A>>>()
                        .as_ref()
                        .unwrap_unchecked()
                        .data,
                )
            };
            unsafe { (*latest).next = previous.next };
            self.ongoing_succession.store(false, Ordering::Release);
            Some(unsafe {
                previous_ref
                    .as_ptr()
                    .cast::<Node<Arc<T::Cloned<'_>, A>>>()
                    .read()
                    .data
            })
        } else {
            None
        }
    }
    /// Returns true if all history has been cleared from the transactor, false if the
    /// history is already being cleared elsewhere
    pub fn clear_history(&self) -> bool {
        if !self.ongoing_succession.swap(true, Ordering::Acquire) {
            let latest = self.history.load(Ordering::Acquire);
            loop {
                let Some(previous_ref) = unsafe { latest.as_ref().unwrap_unchecked() }.next else {
                    self.ongoing_succession.store(false, Ordering::Release);
                    break true;
                };
                let previous = Box::into_inner(unsafe {
                    Box::from_raw_in(previous_ref.as_ptr(), self.allocator.clone())
                });
                unsafe {
                    previous.data.succeed(
                        &latest
                            .cast::<Node<Arc<T::Cloned<'_>, A>>>()
                            .as_ref()
                            .unwrap_unchecked()
                            .data,
                    )
                };
                drop(previous.data);
                unsafe { (*latest).next = previous.next };
            }
        } else {
            false
        }
    }

    pub fn snapshot(&self) -> Arc<T::Cloned<'t>, A> {
        Arc::clone(
            &unsafe {
                self.history
                    .load(Ordering::Acquire)
                    .cast::<Node<Arc<T::Cloned<'_>, A>>>()
                    .as_ref()
                    .unwrap_unchecked()
            }
            .data,
        )
    }

    // Returns back the pointer value on failure
    fn inner_commit_loop<F>(
        &self,
        history_head: *mut Node<Arc<T, A>>,
        f: F,
        needs_consistency: bool,
    ) -> Option<*mut Node<Arc<T, A>>>
    where
        F: Fn(&'t T) -> Option<T::Cloned<'t>>,
    {
        let new_value = unsafe {
            PartialClone::extend_inner_lifetime(f(history_head
                .as_ref()
                .unwrap_unchecked()
                .data
                .deref())?)
        };
        let new_history_head: *mut Node<Arc<T, A>> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                next: NonNull::new(history_head),
            },
            self.allocator.clone(),
        ))
        .0;
        if !needs_consistency {
            self.history.store(new_history_head, Ordering::Release);
            None
        } else if let Err(swapped_in_history_head) = self.history.compare_exchange_weak(
            history_head,
            new_history_head,
            Ordering::Release,
            Ordering::Acquire,
        ) {
            drop(unsafe { Box::from_raw_in(new_history_head, self.allocator.clone()) });
            Some(swapped_in_history_head)
        } else {
            None
        }
    }
    /// Attempts to run the given closure on the in-transaction-value and update the transactor
    /// with the result. If the in-transaction-value has changed during this, we do not update.
    /// If successful, returns `true`, else `false`.
    pub fn raw_commit<F>(&self, f: F) -> bool
    where
        F: FnOnce(&'t T) -> T::Cloned<'t>,
    {
        let history_head = self.history.load(Ordering::Acquire);
        let new_value = unsafe {
            PartialClone::extend_inner_lifetime(f(history_head
                .as_ref()
                .unwrap_unchecked()
                .data
                .deref()))
        };
        let new_history_head: *mut Node<Arc<T, A>> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                next: NonNull::new(history_head),
            },
            self.allocator.clone(),
        ))
        .0;
        if self
            .history
            .compare_exchange_weak(
                history_head,
                new_history_head,
                Ordering::Release,
                Ordering::Acquire,
            )
            .is_err()
        {
            drop(unsafe { Box::from_raw_in(new_history_head, self.allocator.clone()) });
            false
        } else {
            true
        }
    }

    pub fn transact<F: Fn(&'t T) -> Option<T::Cloned<'t>>>(
        &'t self,
        f: F,
    ) -> Transaction<'t, T, A, F> {
        Transaction {
            transactor: self,
            action: f,
            needs_consistency: true,
        }
    }
    pub fn alter<F: Fn(&'t T) -> T::Cloned<'t> + 't>(
        &'t self,
        f: F,
    ) -> Transaction<'t, T, A, impl Fn(&'t T) -> Option<T::Cloned<'t>>> {
        Transaction {
            transactor: self,
            action: move |x| Some(f(x)),
            needs_consistency: true,
        }
    }
    pub fn set_with<F: Fn() -> T::Cloned<'t> + 't>(
        &'t self,
        f: F,
    ) -> Transaction<'t, T, A, impl Fn(&'t T) -> Option<T::Cloned<'t>>> {
        Transaction {
            transactor: self,
            action: move |_| Some(f()),
            needs_consistency: false,
        }
    }
    // TODO Should be able to react to change in ref. this should be called after an asynchronous
    // commit finishes. The user will probably consume this as a stream
    pub fn wake_waiter(&self) {
        todo!()
    }
}

pub struct Transaction<
    't,
    T: PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone + 't,
    F: Fn(&'t T) -> Option<T::Cloned<'t>>,
> {
    transactor: &'t Transactor<'t, T, A>,
    action: F,
    needs_consistency: bool,
}

impl<
    't,
    T: PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone,
    F: Fn(&'t T) -> Option<T::Cloned<'t>>,
> Transaction<'t, T, A, F>
{
    pub fn commit(&self) {
        let Transaction {
            transactor,
            action,
            needs_consistency,
        } = self;
        let mut history_ptr = transactor.history.load(Ordering::Acquire);
        while let Some(swapped_in_ptr) =
            transactor.inner_commit_loop(history_ptr, action, *needs_consistency)
        {
            history_ptr = swapped_in_ptr;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use norc_pers::PersVec;
    use std::thread::scope;
    #[test]
    fn simple_multithread() {
        let transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new());
        scope(|s| {
            s.spawn(|| {
                for i in 0..1000usize {
                    transactor.alter(|pv| pv.partial_clone().append(i)).commit();
                }
            });
            s.spawn(|| {
                for i in 1000..2000usize {
                    transactor.alter(|pv| pv.partial_clone().append(i)).commit();
                }
            });
        });
        assert!(transactor.clear_history());
    }
    #[test]
    fn snapshot_check() {
        let transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new().append(1));
        {
            let snapshot = transactor.snapshot();
            scope(|s| {
                s.spawn(|| {
                    transactor
                        .set_with(|| snapshot.partial_clone().append(3))
                        .commit();
                    transactor
                        .set_with(|| snapshot.partial_clone().append(2))
                        .commit();
                });
            });
            assert_eq!(snapshot.len(), 1);
            assert_eq!(snapshot.first().unwrap(), &1);
        }
        assert!(transactor.clear_history());
        assert_eq!(*transactor.snapshot().first().unwrap(), 1);
        assert_eq!(*transactor.snapshot().last().unwrap(), 2);
        assert_eq!(transactor.snapshot().len(), 2);
    }
}
