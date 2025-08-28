#![expect(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(box_into_inner)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    marker::PhantomData,
    mem::forget,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
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

struct Node<T, A: Allocator + Send + Sync + Clone = Global> {
    data: Arc<T, A>,
    next: Option<NonNull<Node<T, A>>>,
}

pub struct Transactor<
    'a,
    T: 'a + PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone = Global,
> {
    history: AtomicPtr<Node<T, A>>,
    _inner_lifetime: PhantomData<&'a T>,
    allocator: A,
}

impl<'a, T: 'a + PartialClone + Succeed, A: Allocator + Send + Sync + Clone> Drop
    for Transactor<'a, T, A>
{
    fn drop(&mut self) {
        let mut node = unsafe { Box::from_raw_in(*self.history.as_ptr(), self.allocator.clone()) };
        while let Some(next_ptr) = node.next {
            node = unsafe { Box::from_raw_in(next_ptr.as_ptr(), self.allocator.clone()) };
        }
    }
}
impl<'a, T: 'a + PartialClone + Succeed> Transactor<'a, T, Global> {
    pub fn new(item: T) -> Self {
        Self::new_in(item, Global)
    }
}
impl<'a, T: 'a + PartialClone + Succeed, A: 'a + Allocator + Clone + Send + Sync>
    Transactor<'a, T, A>
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
            _inner_lifetime: PhantomData,
            allocator,
        }
    }

    pub fn snapshot(&self) -> Arc<T, A> {
        unsafe {
            self.history
                .load(Ordering::Relaxed)
                .as_ref()
                .unwrap_unchecked()
        }
        .data
        .clone()
    }

    // Returns back the pointer value on failure
    fn inner_commit_loop<F>(&self, history_head: *mut Node<T, A>, f: F) -> Option<*mut Node<T, A>>
    where
        F: Fn(&'a T) -> Option<T::Cloned<'a>>,
    {
        let new_value = unsafe {
            PartialClone::extend_inner_lifetime(f(history_head
                .as_ref()
                .unwrap_unchecked()
                .data
                .deref())?)
        };
        let new_history_head: *mut Node<T, A> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                next: NonNull::new(history_head),
            },
            self.allocator.clone(),
        ))
        .0;
        if let Err(swapped_in_history_head) = self.history.compare_exchange_weak(
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
    pub fn raw_commit<'t, F>(&'t self, f: F) -> bool
    where
        F: FnOnce(&'a T) -> T::Cloned<'a>,
    {
        let history_head = self.history.load(Ordering::Acquire);
        let new_value = unsafe {
            PartialClone::extend_inner_lifetime(f(history_head
                .as_ref()
                .unwrap_unchecked()
                .data
                .deref()))
        };
        let new_history_head: *mut Node<T, A> = Box::into_raw_with_allocator(Box::new_in(
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
    // TODO Should be able to react to change in ref. this should be called after an asynchronous
    // commit finishes. The user will probably consume this as a stream
    pub fn wake_waiter() {
        todo!()
    }
}

pub trait Transact<'t>
where
    Self: 't,
{
    type Alloc: Allocator + Clone + Send + Sync;
    type Item: PartialClone + Succeed;

    fn transactor(&self) -> &Transactor<'t, Self::Item, Self::Alloc>;
    fn action(
        &self,
    ) -> impl Fn(&'t Self::Item) -> Option<<<Self as Transact>::Item as PartialClone>::Cloned<'t>>;
    /// Runs the given closure on the in-transaction-value and update the transactor with the
    /// result. If the in-transaction-value has changed during this, we rerun the closure and try
    /// again, blocking until we succeed.
    fn commit(&self) {
        let transactor = self.transactor();
        let mut history_ptr = transactor.history.load(Ordering::Acquire);
        while let Some(swapped_in_ptr) = transactor.inner_commit_loop(history_ptr, self.action()) {
            history_ptr = swapped_in_ptr;
        }
    }
}

#[must_use]
pub fn alter<'t, T, F, A>(transactor: &'t Transactor<'t, T, A>, act: F) -> Alteration<'t, T, F, A>
where
    T: PartialClone + Succeed,
    F: Fn(&'t T) -> T::Cloned<'t>,
    A: Allocator + Clone + Send + Sync,
{
    Alteration { transactor, act }
}

pub struct Alteration<'t, T, F, A = Global>
where
    T: PartialClone + Succeed,
    F: Fn(&'t T) -> T::Cloned<'t>,
    A: Allocator + Clone + Send + Sync,
{
    transactor: &'t Transactor<'t, T, A>,
    act: F,
}
impl<'t, T, F: 't, A> Transact<'t> for Alteration<'t, T, F, A>
where
    T: PartialClone + Succeed,
    F: Fn(&'t T) -> T::Cloned<'t>,
    A: Allocator + Clone + Send + Sync,
{
    type Alloc = A;
    type Item = T;
    fn transactor(&self) -> &Transactor<'t, T, A> {
        self.transactor
    }
    fn action(&self) -> impl Fn(&'t T) -> Option<<T as PartialClone>::Cloned<'t>> {
        |t| Some((self.act)(t))
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
                    alter(&transactor, |pv| pv.partial_clone().append(i)).commit();
                }
            });
            s.spawn(|| {
                for i in 1000..2000usize {
                    alter(&transactor, |pv| pv.partial_clone().append(i)).commit();
                }
            });
        });
    }
    #[test]
    fn lifetime_check() {
        let transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new().append(1));
        {
            let snapshot = transactor.snapshot();
            scope(|s| {
                s.spawn(|| {
                    alter(&transactor, |_| snapshot.partial_clone().append(3)).commit();
                    alter(&transactor, |_| snapshot.partial_clone().append(2)).commit();
                });
            });
        }
        assert_eq!(*transactor.snapshot().first().unwrap(), 1);
        assert_eq!(*transactor.snapshot().last().unwrap(), 2);
        assert_eq!(transactor.snapshot().len(), 2);
    }
}
