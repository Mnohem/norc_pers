use allocator_api2::{
    alloc::{self, handle_alloc_error},
    boxed::Box,
};
use core::{alloc::Layout, fmt::Debug, marker::Unsize, mem::take};
use crate::Ref;

type Link<'a, T> = Option<Ref<'a, Node<'a, T>>>;

/// A Persistent Linked List. Does not use reference counting, so `clone` is a *deep clone. Use
/// `reborrow` for expected, cheap cloning behavior.
///     * `clone` is only a deep clone for those values which a `List` owns itself
/// This collection can hold unsized values, but they must implement `Default` for a safe
/// interface. Otherwise you need to use `prepend_with_uninit`.
#[derive(Debug, Clone)]
pub struct List<'a, T: ?Sized> {
    head: Link<'a, T>,
    length: usize,
}

impl<'a, T: ?Sized> Default for List<'a, T> {
    fn default() -> Self {
        Self {
            head: None,
            length: 0,
        }
    }
}

impl<'a, T: ?Sized + 'a> List<'a, T> {
    #[must_use]
    pub fn reborrow<'b>(&'b self) -> List<'b, T>
    where
        'a: 'b,
    {
        List {
            head: self.head.as_deref().map(Ref::Borrowed),
            length: self.length,
        }
    }

    #[must_use]
    pub const fn new() -> Self {
        Self {
            head: None,
            length: 0,
        }
    }
    #[must_use]
    pub fn prepend(mut self, value: T) -> Self
    where
        T: Sized,
    {
        self.length += 1;
        Self {
            head: Some(Ref::Owned(Box::new(Node {
                value,
                next: self.head,
            }))),
            ..self
        }
    }
    #[must_use]
    pub fn prepend_sized<U: Unsize<T>>(mut self, value: U) -> Self {
        self.length += 1;
        Self {
            head: Some(Ref::Owned(Node::init(self.head, value))),
            ..self
        }
    }
    #[must_use]
    pub fn from_iter_sized<U, I>(iter: I) -> Self
    where
        U: Unsize<T>,
        I: IntoIterator<Item = U>,
    {
        let mut iter = iter.into_iter();
        let mut result = Self::new();
        let Some(first_elem) = iter.next() else {
            return result;
        };
        result = result.prepend_sized(first_elem);
        let mut last_node =
            result.head.as_mut().map(Ref::mut_unchecked).unwrap() as *mut Node<'a, T>;

        for i in iter {
            result.length += 1;
            let mut new_last = Node::init(None, i);
            let old_last_next = unsafe { (&raw mut (*last_node).next) };
            last_node = new_last.as_mut() as *mut Node<'a, T>;
            unsafe {
                old_last_next.write(Some(Ref::Owned(new_last)));
            }
        }
        result
    }
    #[must_use]
    pub fn pop_front(mut self) -> Self {
        if self.is_empty() {
            return self;
        };
        self.length -= 1;
        self.head = match self.head.unwrap() {
            Ref::Owned(mut node) => node.next.take(),
            Ref::Borrowed(node) => node.next.as_deref().map(Ref::Borrowed),
        };
        self
    }
    // Currently implementation detail, might expose later once correct
    fn pop_front_with_val(mut self) -> (Option<Ref<'a, T>>, Self) {
        if self.is_empty() {
            return (None, self);
        };
        self.length -= 1;
        let val = match self.head.unwrap() {
            Ref::Owned(_) => {
                todo!()
                // self.head = node.next.take();
                // let node = Box::into_raw(node);
                // unsafe {
                //     // TODO This is not correct, does not account for padding/alignment
                //     // Though this branch isnt tested or used
                //     drop(Box::from_raw(&raw mut (*node).next));
                //     Ref::Owned(Box::from_raw(&raw mut (*node).value))
                // }
            }
            Ref::Borrowed(node) => {
                let val = &node.value;
                self.head = node.next.as_deref().map(Ref::Borrowed);
                Ref::Borrowed(val)
            }
        };
        (Some(val), self)
    }
    #[must_use]
    pub fn first(&'a self) -> Option<&'a T> {
        self.head.as_deref().map(|n| &n.value)
    }
    pub fn iter(&'a self) -> Iter<'a, T> {
        Iter {
            list: self.reborrow(),
        }
    }
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Clone, Default)]
struct Node<'a, T: ?Sized> {
    next: Link<'a, T>,
    value: T,
}
impl<'a, T: ?Sized> Node<'a, T> {
    fn init<U: Unsize<T>>(next: Link<'a, T>, value: U) -> Box<Node<'a, T>> {
        let head: *mut Node<'a, T> = unsafe {
            let unsized_value: *const T = &raw const value;
            let head_ptr = &raw const next;
            let modified_ptr = head_ptr.with_metadata_of(unsized_value) as *const Node<'a, T>;

            let layout = Layout::for_value_raw(modified_ptr);
            let layout = layout.align_to(align_of::<U>()).unwrap().pad_to_align();
            let allocation = alloc::alloc(layout);
            if allocation.is_null() {
                handle_alloc_error(layout);
            }
            allocation.with_metadata_of(unsized_value) as *mut Node<'a, T>
        };
        unsafe {
            (&raw mut (*head).next).write(next);
            (&raw mut (*head).value as *mut U).write(value);
            Box::from_raw(head)
        }
    }
}

impl<'a, T> FromIterator<T> for List<'a, T> {
    // currently reverses order of given iterator
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let mut result = Self::new();
        let Some(first_elem) = iter.next() else {
            return result;
        };
        result = result.prepend(first_elem);
        let mut last_node =
            result.head.as_mut().map(Ref::mut_unchecked).unwrap() as *mut Node<'a, T>;

        for i in iter {
            result.length += 1;
            let mut new_last = Box::new(Node {
                value: i,
                next: None,
            });
            let old_last_next = unsafe { (&raw mut (*last_node).next) };
            last_node = new_last.as_mut() as *mut Node<'a, T>;
            unsafe {
                old_last_next.write(Some(Ref::Owned(new_last)));
            }
        }
        result
    }
}

pub struct Iter<'a, T: ?Sized> {
    list: List<'a, T>, // given as a reborrow from List::iter
}
impl<'a, T: ?Sized> Iterator for Iter<'a, T>
where
    List<'a, T>: Sized,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let (val, new_list) = take(&mut self.list).pop_front_with_val();
        self.list = new_list;
        // ref_unchecked is valid here because List::iter gives us a reborrowed list
        val.map(Ref::ref_unchecked)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len(), Some(self.list.len()))
    }
}
impl<'a, T: ?Sized> ExactSizeIterator for Iter<'a, T> {}
