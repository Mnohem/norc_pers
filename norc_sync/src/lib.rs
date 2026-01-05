#![feature(box_into_inner)]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(not(feature = "allocator-api2"), feature(allocator_api))]
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    num::NonZeroUsize,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, Ordering},
};
use norc_pers::borrow::{Consign, Lend};
cfg_if::cfg_if! {
    if #[cfg(feature = "allocator-api2")] {
        use allocator_api2::alloc::Allocator;
        use allocator_api2::boxed::Box;
        use allocator_api2::alloc::Global;
    } else {
        extern crate alloc as mem;
        use mem::alloc::Allocator;
        use mem::boxed::Box;
        use mem::alloc::Global;
    }
}

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct Timestamp(NonZeroUsize);
impl Timestamp {
    pub fn next(self, n: usize) -> Option<Timestamp> {
        Some(Timestamp(self.0.checked_add(n)?))
    }
    pub fn previous(self, n: usize) -> Option<Timestamp> {
        Some(Timestamp(NonZeroUsize::new(self.0.get() - n)?))
    }
    pub fn delta(self, other: Self) -> usize {
        if self > other {
            self.0.get() - other.0.get()
        } else {
            other.0.get() - self.0.get()
        }
    }
}

pub struct Entry<T> {
    pub stamp: Timestamp,
    pub item: T,
}
struct Node<T> {
    newer: AtomicPtr<Node<T>>,
    older: *const Node<T>,
    entry: Entry<T>,
}

pub struct History<'t, T, A = Global>
where
    T: 't + Lend + Consign,
    A: Allocator + Send + Sync + Clone,
{
    oldest: UnsafeCell<NonNull<Node<T>>>,
    newest: AtomicPtr<Node<T>>,
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
            mut entry,
            ..
        } = Box::into_inner(unsafe {
            Box::from_raw_in(self.oldest.get_mut().as_ptr(), self.allocator.clone())
        });
        while !node.get_mut().is_null() {
            Node {
                newer: node,
                entry,
                ..
            } = Box::into_inner(unsafe {
                Box::from_raw_in(*node.get_mut(), self.allocator.clone())
            });
        }
        drop(entry);
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
    fn node_at_time(&self, ts: Timestamp) -> Option<*const Node<T>> {
        let latest = self.newest.load(Ordering::Relaxed);
        let earliest = unsafe { (*self.oldest.get()).as_ptr() };
        let latest_ts = unsafe { (*latest).entry.stamp };
        let earliest_ts = unsafe { (*earliest).entry.stamp };
        if ts > latest_ts || ts < earliest_ts {
            return None;
        }
        let offset_from_earliest = ts.0.get() - earliest_ts.0.get();
        let total_offset = latest_ts.0.get() - earliest_ts.0.get();
        let mut node;
        if offset_from_earliest >= total_offset / 2 {
            let offset_from_latest = latest_ts.0.get() - ts.0.get();
            node = latest;
            for _ in 0..offset_from_latest {
                node = unsafe { (*node).older } as *mut _;
            }
        } else {
            node = earliest;
            for _ in 0..offset_from_earliest {
                node = unsafe { (*node).newer.load(Ordering::Relaxed) };
            }
        }
        Some(node)
    }

    // Returns the oldest snapshot released from the history,
    // or `None` if there is nothing to free
    fn inner_release_oldest(&self) -> Option<Box<Node<T>, A>> {
        let oldest = unsafe { *self.oldest.get() };
        let second_oldest =
            NonNull::new(unsafe { (*oldest.as_ptr()).newer.load(Ordering::Acquire) })?;
        unsafe {
            oldest.as_ref().entry.item.consign(
                &second_oldest
                    .cast::<Node<T::Lended<'_>>>()
                    .as_ref()
                    .entry
                    .item,
            );
            self.oldest.get().write(second_oldest);
        };
        let oldest_alloc = unsafe { Box::from_raw_in(oldest.as_ptr(), self.allocator.clone()) };
        Some(oldest_alloc)
    }

    // Returns `None` if we were unable to alter the value, `Some` if we could
    fn inner_optional_commit_loop<F>(
        &self,
        f: F,
        newest: *mut Node<T>,
    ) -> Result<Timestamp, Option<*mut Node<T>>>
    where
        F: for<'a> Fn(&'a T) -> T::Lended<'a>,
    {
        let Some(to_be_newest_stamp) = unsafe { (*newest).entry.stamp }.next(1) else {
            return Err(None);
        };
        let new_value = unsafe {
            Consign::extend_inner_lifetime(f(&newest.as_ref().unwrap_unchecked().entry.item))
        };
        let to_be_newest_node: *mut Node<T> = Box::into_raw_with_allocator(Box::new_in(
            Node {
                entry: Entry {
                    stamp: to_be_newest_stamp,
                    item: new_value,
                },
                newer: AtomicPtr::new(ptr::null_mut()),
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
            Err(Some(other_ptr))
        } else {
            unsafe {
                (*newest).newer.store(to_be_newest_node, Ordering::Release);
            };
            Ok(to_be_newest_stamp)
        }
    }

    #[must_use]
    pub fn new_in(item: T, allocator: A) -> Self {
        let first = Box::into_raw_with_allocator(Box::new_in(
            Node {
                entry: Entry {
                    item,
                    stamp: Timestamp(unsafe { NonZeroUsize::new_unchecked(1) }),
                },
                newer: AtomicPtr::new(ptr::null_mut()),
                older: ptr::null(),
            },
            allocator.clone(),
        ))
        .0;
        Self {
            oldest: unsafe { NonNull::new(first).unwrap_unchecked() }.into(),
            newest: AtomicPtr::new(first),
            _inner_lifetime: PhantomData,
            allocator,
        }
    }
    /// Returns the amount of values currently recorded.
    /// `History` can never be empty, so we return a `NonZeroUsize`
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        unsafe {
            NonZeroUsize::new_unchecked(
                ((*self.newest.load(Ordering::Acquire)).entry.stamp.0.get()
                    - (*(*self.oldest.get()).as_ptr()).entry.stamp.0.get())
                    + 1,
            )
        }
    }
    #[must_use]
    pub fn snapshot(&self, ts: Timestamp) -> Option<&Entry<T>> {
        let node = self.node_at_time(ts)?;
        Some(unsafe { &(*node).entry })
    }
    #[must_use]
    pub fn earliest(&self) -> &Entry<T> {
        let node = unsafe { &*(*self.oldest.get()).as_ptr() };
        &node.entry
    }
    #[must_use]
    pub fn latest(&self) -> &Entry<T> {
        let node = unsafe { &*self.newest.load(Ordering::Acquire) };
        &node.entry
    }
    /// Returns all entries preceding the given timestamp in chronological order.
    /// Even if the given timestamp is not contained in history, we still iterate over all prior
    /// entries.
    pub fn before(&self, ts: Timestamp) -> impl Iterator<Item = &Entry<T>> {
        let mut node = Some(unsafe { (*self.oldest.get()).as_ref() });
        core::iter::from_fn(move || {
            let entry = &node?.entry;
            if ts <= entry.stamp {
                None
            } else {
                node = unsafe { node?.newer.load(Ordering::Relaxed).as_ref() };
                Some(entry)
            }
        })
    }
    /// Returns all entries succeeding the given timestamp in chronological order.
    /// If the given timestamp is not contained in history, we still iterate over all posterior
    /// entries.
    pub fn after(&self, ts: Timestamp) -> impl Iterator<Item = &Entry<T>> {
        let mut node = if ts < self.earliest().stamp {
            Some(unsafe { (*self.oldest.get()).as_ref() })
        } else {
            self.node_at_time(ts)
                .and_then(|node| unsafe { node.as_ref()?.newer.load(Ordering::Relaxed).as_ref() })
        };
        core::iter::from_fn(move || {
            let entry = &node?.entry;
            node = unsafe { node?.newer.load(Ordering::Relaxed).as_ref() };
            Some(entry)
        })
    }

    /// Clears the oldest value from the history and returns it
    /// Returns `None` if the history only contains one value
    pub fn take_earliest(&mut self) -> Option<Entry<T>> {
        self.inner_release_oldest().map(|x| x.entry)
    }
    /// Clears all the history before a given timestamp
    /// Returns the earliest timestamp in an `Err` variant if the given timestamp is not in the history
    /// Attempts to clear the `n` oldest values from history
    pub fn clear_to(&mut self, ts: Timestamp) -> Result<(), Timestamp> {
        let latest = self.newest.load(Ordering::Relaxed);
        let earliest = unsafe { (*self.oldest.get()).as_ptr() };
        let latest_ts = unsafe { (*latest).entry.stamp };
        let earliest_ts = unsafe { (*earliest).entry.stamp };
        if ts > latest_ts || ts < earliest_ts {
            return Err(earliest_ts);
        }
        let offset_from_earliest = ts.0.get() - earliest_ts.0.get();
        let mut prev = earliest;
        let mut node = unsafe { *(*prev).newer.as_ptr() };
        for _ in 0..offset_from_earliest {
            unsafe {
                prev.as_ref().unwrap_unchecked().entry.item.consign(
                    &node
                        .cast::<Node<T::Lended<'_>>>()
                        .as_ref()
                        .unwrap_unchecked()
                        .entry
                        .item,
                );
            }
            unsafe { Box::from_raw_in(prev, self.allocator.clone()) };
            prev = node;
            node = unsafe { *(*prev).newer.as_ptr() };
        }
        unsafe { (&raw mut (*prev).older).write(ptr::null()) };
        *self.oldest.get_mut() = unsafe { NonNull::new_unchecked(prev) };
        Ok(())
    }
    /// Clears all but the newest value from history
    pub fn clear_history(&mut self) {
        while self.inner_release_oldest().is_some() {}
    }

    /// Reverts the history back to a given timestamp
    /// Returns the latest timestamp in an `Err` variant if the timestamp is not in the history
    pub fn revert_to(&mut self, ts: Timestamp) -> Result<(), Timestamp> {
        let latest = self.newest.load(Ordering::Relaxed);
        let earliest = unsafe { (*self.oldest.get()).as_ptr() };
        let latest_ts = unsafe { (*latest).entry.stamp };
        let earliest_ts = unsafe { (*earliest).entry.stamp };
        if ts > latest_ts || ts < earliest_ts {
            return Err(latest_ts);
        }
        let offset_from_latest = latest_ts.0.get() - ts.0.get();
        let mut node = latest;
        for _ in 0..offset_from_latest {
            node = unsafe { Box::from_raw_in(node, self.allocator.clone()).older } as *mut _;
        }
        *self.newest.get_mut() = node;
        Ok(())
    }

    pub fn commit_blocking<F>(&self, f: F) -> Timestamp
    where
        F: for<'a> Fn(&'a T) -> T::Lended<'a>,
    {
        let mut newest = self.newest.load(Ordering::Acquire);
        loop {
            match self.inner_optional_commit_loop(&f, newest) {
                Ok(ts) => break ts,
                Err(Some(other_ptr)) => newest = other_ptr,
                Err(None) => newest = self.newest.load(Ordering::Acquire),
            }
        }
    }
    pub async fn commit<F>(&self, f: F) -> Timestamp
    where
        F: for<'a> Fn(&'a T) -> T::Lended<'a>,
    {
        loop {
            let newest = self.newest.load(Ordering::Acquire);
            if let Ok(ts) = self.inner_optional_commit_loop(&f, newest) {
                break ts;
            }
            SelfWaker(false).await;
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
            history.commit_blocking(|pv| pv.lend().append(i));
        }
        history.clear_history();
        assert_eq!(history.latest().item.len(), 100);
        let mut sum = 0;
        for &i in history.latest().item.iter() {
            assert!(i < 100);
            sum += i;
        }
        assert_eq!(sum, 4950);
    }
    #[test]
    fn many_values_revert() {
        let mut history: History<PersVec<usize>> = History::new(PersVec::new());
        assert_eq!(history.len().get(), 1);
        let origin = history.earliest().stamp;
        for i in 0..100 {
            history.commit_blocking(|pv| pv.lend().append(i));
        }
        for i in 0..=100 {
            assert_eq!(
                history
                    .snapshot(origin.next(i).unwrap())
                    .unwrap()
                    .item
                    .len(),
                i
            );
        }
        let stamp = history.latest().stamp.previous(50).unwrap();
        let stamp50 = history.snapshot(stamp).unwrap().stamp;
        assert_eq!(history.len().get(), 101);
        assert!(history.revert_to(stamp).is_ok());

        let snapshot50 = history.snapshot(stamp50).unwrap();
        assert_eq!(history.len().get(), 51);
        assert!(ptr::eq(&history.latest().item, &snapshot50.item));

        assert_eq!(snapshot50.item.iter().sum::<usize>(), (49 * 50) / 2);
        for i in 0..50 {
            history.commit_blocking(|pv| pv.lend().append(i));
        }
        assert_eq!(history.len().get(), 101);
        assert!(
            history
                .clear_to(history.earliest().stamp.next(50).unwrap())
                .is_ok()
        );
        assert_eq!(history.len().get(), 51);
        assert_eq!(history.latest().item.iter().sum::<usize>(), 49 * 50);
    }
    #[test]
    fn before_after_check() {
        let mut history: History<PersVec<usize>> = History::new(PersVec::new());
        let origin = history.latest().stamp;
        scope(|s| {
            s.spawn(|| {
                for i in 0..100usize {
                    history.commit_blocking(|pv| pv.lend().append(i));
                }
            });
            s.spawn(|| {
                for i in 100..200usize {
                    history.commit_blocking(|pv| pv.lend().append(i));
                }
            });
            s.spawn(|| {
                for entry in history.after(origin) {
                    let mut zero_max = 0;
                    let mut hundred_max = 100;
                    entry.item.iter().for_each(|x| {
                        if *x / 100 > 0 {
                            if *x >= hundred_max {
                                hundred_max = *x;
                            } else {
                                panic!("{x} should not be smaller than {hundred_max}");
                            }
                        } else if *x >= zero_max {
                            zero_max = *x;
                        } else {
                            panic!("{x} should not be smaller than {zero_max}");
                        }
                    });
                }
            });
        });
        assert!(history.before(origin).next().is_none());
        history.clear_history();
        assert_eq!(history.latest().item.len(), 200);
        let mut sum = 0;
        for &i in history.latest().item.iter() {
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
                history.commit_blocking(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1));
            }
        };
        let check_sum = || {
            let s = &history.latest().item;
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
                    .commit(|pv| pv.lend().append(*pv.last().unwrap_or(&0) + 1))
                    .await;
            }
        };
        let check_sum = async {
            let s = &history.latest().item;
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
