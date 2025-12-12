#![feature(box_into_inner)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
    task::Waker,
};
use norc_pers::borrow::{Consign, Lend};
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

struct WakerNode {
    older: *mut WakerNode,
    waker: Waker,
}

pub struct TransactionToken(usize);

static TOKEN_ID: AtomicUsize = AtomicUsize::new(0);
pub struct Transactor<'t, T, A = Global>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone,
{
    oldest: UnsafeCell<NonNull<Node<Arc<T, A>>>>,
    newest: AtomicPtr<Node<Arc<T, A>>>,
    wakers: AtomicPtr<WakerNode>,
    id: usize,
    _inner_lifetime: PhantomData<&'t T>,
    allocator: A,
}

unsafe impl<'t, T, A> Send for Transactor<'t, T, A>
where
    T: 't + Lend + Consign + Send + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

unsafe impl<T, A> Sync for Transactor<'_, T, A>
where
    T: Lend + Consign + Send + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

impl<'t, T, A> Drop for Transactor<'t, T, A>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone,
{
    fn drop(&mut self) {
        let Node {
            newer: mut node,
            mut data,
        } = Box::into_inner(unsafe {
            Box::from_raw_in(self.oldest.get_mut().as_ptr(), self.allocator.clone())
        });
        while node.get_mut().is_some() {
            Node { newer: node, data } = Box::into_inner(unsafe {
                Box::from_raw_in(
                    node.get_mut().unwrap_unchecked().as_ptr(),
                    self.allocator.clone(),
                )
            });
        }
        drop(data);
        if let Some(wakers) = NonNull::new(*self.wakers.get_mut()) {
            let WakerNode {
                mut older,
                mut waker,
            } = Box::into_inner(unsafe {
                Box::from_raw_in(wakers.as_ptr(), self.allocator.clone())
            });
            while !older.is_null() {
                WakerNode { older, waker } =
                    Box::into_inner(unsafe { Box::from_raw_in(older, self.allocator.clone()) });
            }
            drop(waker);
        }
    }
}
impl<'t, T, A> Transactor<'t, T, A>
where
    T: 't + Lend + Consign,
    A: 't + Allocator + Clone + Send + Sync + Default,
{
    pub fn new(item: T) -> (Self, TransactionToken) {
        Self::new_in(item, Default::default())
    }
}
impl<'t, T, A> Transactor<'t, T, A>
where
    T: 't + Lend + Consign,
    A: 't + Allocator + Clone + Send + Sync,
{
    pub fn new_in(item: T, allocator: A) -> (Self, TransactionToken) {
        let first = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(item, allocator.clone()),
                newer: UnsafeCell::new(None),
            },
            allocator.clone(),
        ))
        .0;
        let id = TOKEN_ID.fetch_add(1, Ordering::Relaxed);
        (
            Self {
                oldest: unsafe { NonNull::new(first).unwrap_unchecked() }.into(),
                newest: AtomicPtr::new(first),
                wakers: AtomicPtr::new(core::ptr::null_mut()),
                id,
                _inner_lifetime: PhantomData,
                allocator,
            },
            TransactionToken(id),
        )
    }
    /// Returns the snapshot that was just released from the history,
    /// or `None` if there is nothing to free
    fn inner_release_oldest(&self) -> Option<Arc<T, A>> {
        let mut oldest = unsafe { *self.oldest.get() };
        let second_oldest = (*unsafe { oldest.as_mut() }.newer.get_mut())?;
        unsafe {
            oldest.as_ref().data.consign(
                &second_oldest
                    .cast::<Node<Arc<T::Lended<'_>, A>>>()
                    .as_ref()
                    .data,
            );
            self.oldest.get().write(second_oldest);
        };
        let oldest_alloc = unsafe { Box::from_raw_in(oldest.as_ptr(), self.allocator.clone()) };
        Some(oldest_alloc.data)
    }

    pub fn release_oldest_snapshot(&self, token: &mut TransactionToken) -> Option<Arc<T, A>> {
        if token.0 == self.id {
            self.inner_release_oldest()
        } else {
            panic!(
                "Transactor ID of {} and token with ID {} incompatible",
                self.id, token.0
            );
        }
    }
    /// Returns true if some history has been cleared from the transactor, false if the
    /// history is already being cleared elsewhere
    pub fn clear_history(&self, token: &mut TransactionToken) {
        if token.0 == self.id {
            while self.inner_release_oldest().is_some() {}
        } else {
            panic!(
                "Transactor ID of {} and token with ID {} incompatible",
                self.id, token.0
            );
        }
    }

    pub fn snapshot(&self) -> Arc<T, A> {
        Arc::clone(unsafe { &(*self.newest.load(Ordering::Acquire)).data })
    }

    /// Returns `None` if we were able to alter the value, `Some` if we saw the address change
    fn inner_optional_commit_loop<F>(
        &self,
        newest: *mut Node<Arc<T, A>>,
        f: F,
    ) -> Option<*mut Node<Arc<T, A>>>
    where
        F: for<'a> Fn(&'a T) -> T::Lended<'a>,
    {
        let new_value = unsafe {
            Lend::extend_inner_lifetime(f(newest.as_ref().unwrap_unchecked().data.deref()))
        };

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
            self.wake_wakers();
            None
        }
    }
    fn inner_set_commit<F>(&self, newest: *mut Node<Arc<T, A>>, f: F)
    where
        F: for<'a> Fn(&'a T) -> T::Lended<'a>,
    {
        let new_value = unsafe {
            Lend::extend_inner_lifetime(f(newest.as_ref().unwrap_unchecked().data.deref()))
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
        self.wake_wakers();
    }

    pub fn alter<F: for<'a> Fn(&'a T) -> T::Lended<'a>>(
        &'t self,
        f: F,
    ) -> Transaction<'t, T, A, F> {
        Transaction {
            transactor: self,
            action: f,
            needs_consistency: true,
        }
    }
    pub fn next_change(&'t self) -> Subscriber<'t, T, A> {
        Subscriber {
            init: None,
            transactor: self,
        }
    }
    fn send_waker(&self, waker: Waker) {
        let mut prev_waker = self.wakers.load(Ordering::Acquire);
        let new_waker = Box::into_raw_with_allocator(Box::new_in(
            WakerNode {
                waker,
                older: prev_waker,
            },
            self.allocator.clone(),
        ))
        .0;
        while let Err(other_waker) = self.wakers.compare_exchange_weak(
            prev_waker,
            new_waker,
            Ordering::Release,
            Ordering::Acquire,
        ) {
            prev_waker = other_waker;
            unsafe { (&raw mut (*new_waker).older).write(other_waker) };
        }
    }
    fn wake_wakers(&self) {
        let mut node = self.wakers.swap(core::ptr::null_mut(), Ordering::AcqRel);
        while !node.is_null() {
            let box_node = unsafe { Box::from_raw_in(node, self.allocator.clone()) };
            box_node.waker.wake();
            node = box_node.older;
        }
    }
}
pub struct Subscriber<'t, T, A>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
{
    init: Option<Arc<T, A>>,
    transactor: &'t Transactor<'t, T, A>,
}
impl<'t, T, A> Future for Subscriber<'t, T, A>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
{
    type Output = Arc<T, A>;

    fn poll(
        mut self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let snapshot = self.transactor.snapshot();
        let Some(ref init) = self.init else {
            self.init = Some(Arc::clone(&snapshot));
            return core::task::Poll::Ready(snapshot);
        };
        if Arc::as_ptr(init) == Arc::as_ptr(&snapshot) {
            self.transactor.send_waker(cx.waker().clone());
            core::task::Poll::Pending
        } else {
            self.init = Some(Arc::clone(&snapshot));
            core::task::Poll::Ready(snapshot)
        }
    }
}

pub struct Transaction<'t, T, A, F>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
    F: for<'a> Fn(&'a T) -> T::Lended<'a>,
{
    transactor: &'t Transactor<'t, T, A>,
    action: F,
    needs_consistency: bool,
}

impl<'t, T, A, F> Transaction<'t, T, A, F>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
    F: for<'a> Fn(&'a T) -> T::Lended<'a>,
{
    pub fn commit_blocking(&self, token: &TransactionToken)
    where
        T: 't + Lend + Consign,
    {
        let Transaction {
            transactor,
            action,
            needs_consistency,
            ..
        } = self;
        if token.0 != transactor.id {
            panic!(
                "Transactor ID of {} and token with ID {} incompatible",
                transactor.id, token.0
            );
        }
        let mut newest = transactor.newest.load(Ordering::Acquire);
        if *needs_consistency {
            while let Some(other_ptr) = transactor.inner_optional_commit_loop(newest, action) {
                newest = other_ptr;
            }
        } else {
            transactor.inner_set_commit(newest, action);
        }
    }
    pub async fn commit(&self, token: &TransactionToken) {
        let Transaction {
            transactor,
            action,
            needs_consistency,
            ..
        } = self;
        if token.0 != transactor.id {
            panic!(
                "Transactor ID of {} and token with ID {} incompatible",
                transactor.id, token.0
            );
        }
        let mut newest = transactor.newest.load(Ordering::Acquire);
        if *needs_consistency {
            while self
                .transactor
                .inner_optional_commit_loop(newest, action)
                .is_some()
            {
                SelfWaker(false).await;
                newest = transactor.newest.load(Ordering::Acquire);
            }
        } else {
            self.transactor.inner_set_commit(newest, action);
        }
    }
}

struct SelfWaker(bool);
impl Future for SelfWaker {
    type Output = ();
    fn poll(
        mut self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        if self.0 {
            core::task::Poll::Ready(())
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            core::task::Poll::Pending
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
        let (transactor, mut token): (Transactor<PersVec<usize>>, TransactionToken) =
            Transactor::new(PersVec::new());
        for i in 0..100usize {
            transactor
                .alter(|pv| pv.lend().append(i))
                .commit_blocking(&token);
        }
        transactor.clear_history(&mut token);
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
        let (transactor, mut token): (Transactor<PersVec<usize>>, TransactionToken) =
            Transactor::new(PersVec::new());
        scope(|s| {
            s.spawn(|| {
                for i in 0..100usize {
                    transactor
                        .alter(|pv| pv.lend().append(i))
                        .commit_blocking(&token);
                }
            });
            s.spawn(|| {
                for i in 100..200usize {
                    transactor
                        .alter(|pv| pv.lend().append(i))
                        .commit_blocking(&token);
                }
            });
        });
        transactor.clear_history(&mut token);
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
    fn all_concurrent_sync() {
        let (transactor, token): (Transactor<PersVec<usize>>, _) = Transactor::new(PersVec::new());
        let append_1000 = || {
            for _ in 0..1000usize {
                transactor
                    .alter(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1))
                    .commit_blocking(&token);
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
    #[cfg_attr(miri, ignore)]
    fn all_concurrent_async() {
        let (transactor, token): (Transactor<PersVec<usize>>, _) = Transactor::new(PersVec::new());
        let append_1000 = async {
            for _ in 0..1000usize {
                transactor
                    .alter(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1))
                    .commit(&token)
                    .await;
            }
        };
        let check_sum = async {
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

        smol::block_on(append_1000);
        smol::block_on(check_sum);
    }
}
