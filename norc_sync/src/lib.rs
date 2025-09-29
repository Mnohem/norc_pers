#![expect(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(box_into_inner)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
    task::Waker,
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
    newer: UnsafeCell<Option<NonNull<Node<T>>>>,
    data: T,
}

pub struct Transactor<'t, T, A = Global>
where
    T: 't + PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone,
{
    oldest: NonNull<Node<Arc<T, A>>>,
    newest: AtomicPtr<Node<Arc<T, A>>>, // tagged with 3 bit version to counteract ABA
    waiters: (),
    _inner_lifetime: PhantomData<&'t T>,
    allocator: A,
}

unsafe impl<'t, T, A> Send for Transactor<'t, T, A>
where
    T: 't + PartialClone + Succeed + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

unsafe impl<'t, T, A> Sync for Transactor<'t, T, A>
where
    T: 't + PartialClone + Succeed + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

impl<'t, T, A> Drop for Transactor<'t, T, A>
where
    T: 't + PartialClone + Succeed,
    A: Allocator + Send + Sync + Clone,
{
    fn drop(&mut self) {
        let Node {
            newer: mut node,
            mut data,
        } = Box::into_inner(unsafe {
            Box::from_raw_in(self.oldest.as_ptr(), self.allocator.clone())
        });
        while node.get_mut().is_some() {
            Node { newer: node, data } = Box::into_inner(unsafe {
                Box::from_raw_in(
                    node.get_mut().unwrap_unchecked().as_ptr(),
                    self.allocator.clone(),
                )
            });
        }
        drop(data)
    }
}
impl<'t, T> Transactor<'t, T, Global>
where
    T: 't + PartialClone + Succeed,
{
    pub fn new(item: T) -> Self {
        Self::new_in(item, Global)
    }
}
impl<'t, T, A> Transactor<'t, T, A>
where
    T: 't + PartialClone + Succeed,
    A: 't + Allocator + Clone + Send + Sync,
{
    pub fn new_in(item: T, allocator: A) -> Self {
        let first = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(item, allocator.clone()),
                newer: UnsafeCell::new(None),
            },
            allocator.clone(),
        ))
        .0;
        Self {
            oldest: unsafe { NonNull::new(first).unwrap_unchecked() },
            newest: AtomicPtr::new(first),
            waiters: (),
            _inner_lifetime: PhantomData,
            allocator,
        }
    }
    /// Returns the snapshot that was just released from the history,
    /// or `None` if there is nothing to free
    fn inner_release_oldest(&mut self) -> Option<Arc<T::Cloned<'t>, A>> {
        let mut oldest = self.oldest;
        let second_oldest = (*unsafe { oldest.as_mut() }.newer.get_mut())?;
        unsafe {
            self.oldest.as_ref().data.succeed(
                &second_oldest
                    .cast::<Node<Arc<T::Cloned<'_>, A>>>()
                    .as_ref()
                    .data,
            );
            self.oldest = second_oldest;
        };
        let oldest_alloc: Box<Node<Arc<T::Cloned<'_>, A>>, A> =
            unsafe { Box::from_raw_in(oldest.as_ptr().cast(), self.allocator.clone()) };
        Some(oldest_alloc.data)
    }

    pub fn release_oldest_snapshot(&mut self) -> Option<Arc<T::Cloned<'t>, A>> {
        self.inner_release_oldest()
    }
    /// Returns true if some history has been cleared from the transactor, false if the
    /// history is already being cleared elsewhere
    pub fn clear_history(&mut self) {
        while self.inner_release_oldest().is_some() {}
    }

    pub fn snapshot(&self) -> Arc<T::Cloned<'t>, A> {
        Arc::clone(unsafe {
            self.newest
                .load(Ordering::Acquire)
                .cast::<Arc<T::Cloned<'_>, A>>()
                .as_ref()
                .unwrap_unchecked()
        })
    }

    /// Returns true if we were able to try to alter the value, false if we saw the address change
    fn inner_optional_commit_loop<F>(
        &self,
        newest: *mut Node<Arc<T, A>>,
        f: F,
    ) -> Option<*mut Node<Arc<T, A>>>
    where
        F: Fn(&'t T) -> Option<T::Cloned<'t>>,
    {
        let new_value = unsafe {
            f(newest.as_ref().unwrap_unchecked().data.deref())
                .map(|x| PartialClone::extend_inner_lifetime(x))
        }?;

        let to_be_newest_node: *mut Node<Arc<T, A>> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                newer: UnsafeCell::new(None),
            },
            self.allocator.clone(),
        ))
        .0;
        if let Err(other_ptr) = self.newest.compare_exchange_weak(
            newest,
            to_be_newest_node,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            unsafe { Box::from_raw_in(to_be_newest_node, self.allocator.clone()) };
            Some(other_ptr)
        } else {
            unsafe {
                (*newest).newer.get().write(NonNull::new(to_be_newest_node));
            };
            self.wake_waiters();
            None
        }
    }
    fn inner_set_commit<F>(&self, newest: *mut Node<Arc<T, A>>, f: F)
    where
        F: Fn(&'t T) -> Option<T::Cloned<'t>>,
    {
        let new_value = unsafe {
            f(newest.as_ref().unwrap_unchecked().data.deref())
                .map(|x| PartialClone::extend_inner_lifetime(x))
                .unwrap_unchecked()
        };

        let to_be_newest_node: *mut Node<Arc<T, A>> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                newer: UnsafeCell::new(None),
            },
            self.allocator.clone(),
        ))
        .0;
        let old = self.newest.swap(to_be_newest_node, Ordering::AcqRel);
        unsafe {
            (*old).newer.get().write(NonNull::new(to_be_newest_node));
        };
        self.wake_waiters();
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
    // TODO Should be able to react to change in ref. this should be called after an
    // commit finishes. The user will probably consume this as a stream
    pub fn wake_waiters(&self) {
        // todo!()
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
        let mut newest = transactor.newest.load(Ordering::Acquire);
        if *needs_consistency {
            while let Some(other_ptr) = transactor.inner_optional_commit_loop(newest, action) {
                newest = other_ptr;
            }
        } else {
            transactor.inner_set_commit(newest, action);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use norc_pers::PersVec;
    use std::thread::scope;
    #[test]
    fn singlethread_clear_history() {
        let mut transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new());
        for i in 0..100usize {
            transactor.alter(|pv| pv.partial_clone().append(i)).commit();
        }
        transactor.clear_history();
        assert_eq!(transactor.snapshot().len(), 100);
        let mut sum = 0;
        for &i in transactor.snapshot().iter() {
            assert!(i < 100);
            sum += i;
        }
        assert_eq!(sum, 4950);
    }
    #[test]
    fn simple_multithread_clear_history() {
        let mut transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new());
        scope(|s| {
            s.spawn(|| {
                for i in 0..100usize {
                    transactor.alter(|pv| pv.partial_clone().append(i)).commit();
                }
            });
            s.spawn(|| {
                for i in 100..200usize {
                    transactor.alter(|pv| pv.partial_clone().append(i)).commit();
                }
            });
        });
        transactor.clear_history();
        assert_eq!(transactor.snapshot().len(), 200);
        let mut sum = 0;
        for &i in transactor.snapshot().iter() {
            println!("{i}");
            assert!(i < 200);
            sum += i;
        }
        assert_eq!(sum, 19900);
    }
    #[test]
    fn all_concurrent() {
        let transactor: Transactor<PersVec<usize, 4>> = Transactor::new(PersVec::new());
        let append_1000 = || {
            for _ in 0..1000usize {
                transactor
                    .alter(|pv| pv.partial_clone().append(*pv.last().unwrap_or(&0) + 1))
                    .commit();
            }
        };
        let check_sum = || {
            let s = transactor.snapshot();
            let expected_sum = if s.len() >= 2 {
                s.len() * (s.len() + 1) / 2
            } else {
                return;
            };
            for (i, &x) in s.iter().enumerate() {
                assert_eq!(i + 1, x);
            }
            assert_eq!(expected_sum, s.iter().sum());
        };
        scope(|s| {
            s.spawn(append_1000);
            s.spawn(append_1000);
            s.spawn(append_1000);
            s.spawn(|| {
                for _ in 0..100 {
                    check_sum();
                }
            });
        });
        check_sum();
    }
    #[test]
    fn snapshot_check() {
        let mut transactor: Transactor<PersVec<usize, 4>> =
            Transactor::new(PersVec::new().append(1));
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
        transactor.clear_history();
        assert_eq!(*transactor.snapshot().first().unwrap(), 1);
        assert_eq!(*transactor.snapshot().last().unwrap(), 2);
        assert_eq!(transactor.snapshot().len(), 2);
    }
}
