#![feature(box_into_inner)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    num::NonZeroUsize,
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
    older: *const Node<T>,
    data: T,
}

struct WakerNode {
    older: *mut WakerNode,
    waker: Waker,
}

pub struct History<'t, T, A = Global>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone,
{
    len: AtomicUsize, // basically how many successful transactions
    oldest: UnsafeCell<NonNull<Node<Arc<T, A>>>>,
    newest: AtomicPtr<Node<Arc<T, A>>>,
    wakers: AtomicPtr<WakerNode>,
    _inner_lifetime: PhantomData<&'t T>,
    allocator: A,
}

unsafe impl<'t, T, A> Send for History<'t, T, A>
where
    T: 't + Lend + Consign + Send + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

unsafe impl<T, A> Sync for History<'_, T, A>
where
    T: Lend + Consign + Send + Sync,
    A: Allocator + Send + Sync + Clone,
{
}

impl<'t, T, A> Drop for History<'t, T, A>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone,
{
    fn drop(&mut self) {
        let Node {
            newer: mut node,
            mut data,
            ..
        } = Box::into_inner(unsafe {
            Box::from_raw_in(self.oldest.get_mut().as_ptr(), self.allocator.clone())
        });
        while node.get_mut().is_some() {
            Node {
                newer: node,
                data,
                ..
            } = Box::into_inner(unsafe {
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
impl<'t, T, A> History<'t, T, A>
where
    T: 't + Lend + Consign,
    A: 't + Allocator + Clone + Send + Sync + Default,
{
    #[must_use]
    pub fn new(item: T) -> Self {
        Self::new_in(item, Default::default())
    }
}
impl<'t, T, A> History<'t, T, A>
where
    T: 't + Lend + Consign,
    A: 't + Allocator + Clone + Send + Sync,
{
    #[must_use]
    pub fn new_in(item: T, allocator: A) -> Self {
        let first = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(item, allocator.clone()),
                newer: UnsafeCell::new(None),
                older: core::ptr::null(),
            },
            allocator.clone(),
        ))
        .0;
        Self {
            len: AtomicUsize::new(1),
            oldest: unsafe { NonNull::new(first).unwrap_unchecked() }.into(),
            newest: AtomicPtr::new(first),
            wakers: AtomicPtr::new(core::ptr::null_mut()),
            _inner_lifetime: PhantomData,
            allocator,
        }
    }
    /// Returns the amount of values currently recorded.
    /// `History` can never be empty, so we return a `NonZeroUsize`
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.len.load(Ordering::Acquire)) }
    }

    fn node_at(&self, relative_age: usize) -> Option<*const Node<Arc<T, A>>> {
        if self.len().get() <= relative_age {
            return None;
        }
        let mut node = self.newest.load(Ordering::Acquire) as *const Node<Arc<T, A>>;
        for _ in 0..relative_age {
            node = unsafe { (*node).older };
        }
        Some(node)
    }

    #[must_use]
    pub fn snapshot(&self, relative_age: usize) -> Option<Arc<T, A>> {
        let node = self.node_at(relative_age)?;
        Some(Arc::clone(unsafe { &(*node).data }))
    }
    #[must_use]
    pub fn latest(&self) -> Arc<T, A> {
        unsafe { self.snapshot(0).unwrap_unchecked() }
    }
    #[must_use]
    pub fn previous(&self) -> Option<Arc<T, A>> {
        self.snapshot(1)
    }
    // Returns the oldest snapshot released from the history,
    // or `None` if there is nothing to free
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

    /// Clears the oldest value from the history and returns
    /// Returns `None` if the history only contains one value
    pub fn take_oldest(&mut self) -> Option<Arc<T, A>> {
        if let Some(data) = self.inner_release_oldest() {
            *self.len.get_mut() -= 1;
            Some(data)
        } else {
            None
        }
    }
    /// Clears the all but the newest value from the history
    pub fn clear_oldest(&mut self, to_drop: usize) {
        for _ in 0..to_drop {
            if self.inner_release_oldest().is_some() {
                *self.len.get_mut() -= 1;
            } else {
                return;
            }
        }
    }
    /// Clears all but the newest value from the history
    pub fn clear_history(&mut self) {
        while self.inner_release_oldest().is_some() {}
        *self.len.get_mut() = 1;
    }

    fn inner_release_from_newest(&mut self, mut newest: *mut Node<Arc<T, A>>, to_release: usize) {
        for _ in 0..to_release {
            let newest_alloc = unsafe { Box::from_raw_in(newest, self.allocator.clone()) };
            newest = newest_alloc.older as *mut _;
        }
    }
    /// Reverts the history back to `steps_back` transactions ago.
    /// Returns the length after this operation, unchanged in `Err` if the requested reversion was too large
    /// (`steps_back >= self.len()`), otherwise the new length in `Ok`
    pub fn revert(&mut self, steps_back: usize) -> Result<NonZeroUsize, NonZeroUsize> {
        let Some(new_root) = self.node_at(steps_back) else {
            return Err(self.len());
        };
        unsafe { (*new_root).newer.get().write(None) };
        let old_root = self.newest.swap(new_root as *mut _, Ordering::Relaxed);
        self.inner_release_from_newest(old_root, steps_back);
        *self.len.get_mut() -= steps_back;
        Ok(unsafe { NonZeroUsize::new_unchecked(*self.len.get_mut()) })
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
            Consign::extend_inner_lifetime(f(newest.as_ref().unwrap_unchecked().data.deref()))
        };

        let to_be_newest_node: *mut Node<Arc<T, A>> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                data: Arc::new_in(new_value, self.allocator.clone()),
                newer: UnsafeCell::new(None),
                older: newest,
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
            unsafe { drop(Box::from_raw_in(to_be_newest_node, self.allocator.clone())) };
            Some(other_ptr)
        } else {
            unsafe {
                (*newest).newer.get().write(NonNull::new(to_be_newest_node));
            };
            self.len.fetch_add(1, Ordering::Release);
            self.wake_wakers();
            None
        }
    }

    pub fn alter<F: for<'a> Fn(&'a T) -> T::Lended<'a>>(
        &'t self,
        f: F,
    ) -> Transaction<'t, T, A, F> {
        Transaction {
            transactor: self,
            action: f,
        }
    }
    pub fn subscriber(&'t self) -> Subscriber<'t, T, A> {
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
#[must_use = "A Subscriber does nothing unless polled"]
pub struct Subscriber<'t, T, A>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
{
    init: Option<Arc<T, A>>,
    transactor: &'t History<'t, T, A>,
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
        let snapshot = self.transactor.latest();
        let Some(ref init) = self.init else {
            self.init = Some(Arc::clone(&snapshot));
            return core::task::Poll::Ready(snapshot);
        };
        if Arc::ptr_eq(init, &snapshot) {
            self.transactor.send_waker(cx.waker().clone());
            core::task::Poll::Pending
        } else {
            self.init = Some(Arc::clone(&snapshot));
            core::task::Poll::Ready(snapshot)
        }
    }
}

#[must_use = "A Transaction does nothing unless committed"]
pub struct Transaction<'t, T, A, F>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
    F: for<'a> Fn(&'a T) -> T::Lended<'a>,
{
    transactor: &'t History<'t, T, A>,
    action: F,
}

impl<'t, T, A, F> Transaction<'t, T, A, F>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone + 't,
    F: for<'a> Fn(&'a T) -> T::Lended<'a>,
{
    pub fn commit_blocking(&self)
    where
        T: 't + Lend + Consign,
    {
        let Transaction {
            transactor, action, ..
        } = self;
        let mut newest = transactor.newest.load(Ordering::Acquire);
        while let Some(other_ptr) = transactor.inner_optional_commit_loop(newest, action) {
            newest = other_ptr;
        }
    }
    pub async fn commit(&self) {
        let Transaction {
            transactor, action, ..
        } = self;
        let mut newest = transactor.newest.load(Ordering::Acquire);
        while self
            .transactor
            .inner_optional_commit_loop(newest, action)
            .is_some()
        {
            SelfWaker(false).await;
            newest = transactor.newest.load(Ordering::Acquire);
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
        let mut history: History<PersVec<usize>> = History::new(PersVec::new());
        for i in 0..100usize {
            history.alter(|pv| pv.lend().append(i)).commit_blocking();
        }
        history.clear_history();
        assert_eq!(history.latest().len(), 100);
        let mut sum = 0;
        for &i in history.latest().iter() {
            assert!(i < 100);
            sum += i;
        }
        assert_eq!(sum, 4950);
    }
    #[test]
    fn many_values_revert() {
        let mut history: History<PersVec<usize>> = History::new(PersVec::new());
        assert_eq!(history.len().get(), 1);
        for i in 0..100 {
            history.alter(|pv| pv.lend().append(i)).commit_blocking();
        }
        for i in 0..=100 {
            assert_eq!(history.snapshot(i).unwrap().len(), 100 - i);
        }
        let snapshot50 = history.snapshot(50).unwrap();
        assert_eq!(history.len().get(), 101);
        assert!(history.revert(50).is_ok());
        assert_eq!(history.len().get(), 51);
        assert!(Arc::ptr_eq(&history.latest(), &snapshot50));

        assert_eq!(snapshot50.iter().sum::<usize>(), (49 * 50) / 2);
        for i in 0..50 {
            history.alter(|pv| pv.lend().append(i)).commit_blocking();
        }
        assert_eq!(history.len().get(), 101);
        assert_eq!(history.latest().iter().sum::<usize>(), 49 * 50);
    }
    #[test]
    fn simple_multithread_clear_history() {
        let mut history: History<PersVec<usize>> = History::new(PersVec::new());
        scope(|s| {
            s.spawn(|| {
                for i in 0..100usize {
                    history.alter(|pv| pv.lend().append(i)).commit_blocking();
                }
            });
            s.spawn(|| {
                for i in 100..200usize {
                    history.alter(|pv| pv.lend().append(i)).commit_blocking();
                }
            });
        });
        history.clear_history();
        assert_eq!(history.latest().len(), 200);
        let mut sum = 0;
        for &i in history.latest().iter() {
            println!("{i}");
            assert!(i < 200);
            sum += i;
        }
        assert_eq!(sum, 19900);
    }
    #[test]
    fn all_concurrent_sync() {
        let history: History<PersVec<usize>> = History::new(PersVec::new());
        let append_1000 = || {
            for _ in 0..1000usize {
                history
                    .alter(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1))
                    .commit_blocking();
            }
        };
        let check_sum = || {
            let s = history.latest();
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
        let history: History<PersVec<usize>> = History::new(PersVec::new());
        let append_1000 = async {
            for _ in 0..1000usize {
                history
                    .alter(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1))
                    .commit()
                    .await;
            }
        };
        let check_sum = async {
            let s = history.latest();
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
