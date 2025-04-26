#![feature(set_ptr_value)]
#![feature(layout_for_ptr)]
#![feature(unsize)]
#![cfg_attr(not(test), no_std)]
pub mod list;
pub mod vector;

use allocator_api2::boxed::Box;
use core::{mem::ManuallyDrop, ops::Deref};
#[derive(Debug, Clone)]
enum Ref<'a, T: ?Sized> {
    Owned(Box<T>),
    Borrowed(&'a T),
}
impl<'a, T: ?Sized> Ref<'a, T> {
    // For when we know we are holding a reference to a value that isnt owned
    fn ref_unchecked(self) -> &'a T {
        match self {
            Self::Owned(_) => unreachable!(),
            Self::Borrowed(t) => t,
        }
    }
    // For when we know we are owning a value we want to mutate
    fn mut_unchecked(&mut self) -> &mut T {
        match self {
            Self::Owned(t) => t.as_mut(),
            Self::Borrowed(_) => unreachable!(),
        }
    }
}
impl<'a, T: ?Sized> Deref for Ref<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(bt) => bt.deref(),
            Self::Borrowed(t) => t,
        }
    }
}
impl<'a, T> AsRef<T> for Ref<'a, T>
where
    T: ?Sized,
    <Ref<'a, T> as Deref>::Target: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.deref()
    }
}
union UnsafeRef<'a, T: ?Sized> {
    boxed: ManuallyDrop<Box<T>>,
    borrowed: &'a T,
}
impl<'a, T: ?Sized> UnsafeRef<'a, T> {
    pub fn from_ref(val: &'a T) -> Self {
        UnsafeRef {
            borrowed: val
        }
    }
    pub fn from_box(val: Box<T>) -> Self {
        UnsafeRef {
            boxed: ManuallyDrop::new(val)
        }
    }
}
impl<'a, T: ?Sized> Deref for UnsafeRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.borrowed }
    }
}
impl<'a, T> AsRef<T> for UnsafeRef<'a, T>
where
    T: ?Sized,
    <UnsafeRef<'a, T> as Deref>::Target: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.deref()
    }
}


// TODO more tests
#[cfg(test)]
mod tests {
    use super::list::*;
    use std::fmt::Debug;

    #[test]
    fn it_works() {
        let new: List<char> = List::new();
        let new = new.prepend('b');

        let first = new.first();
        assert_eq!(first, Some(&'b'))
    }
    #[test]
    fn iterate() {
        let new = List::new();
        let new = new.prepend('!');
        let new = new.prepend('d');
        let new = new.prepend('l');
        let new = new.prepend('r');
        let new = new.prepend('o');
        let new = new.prepend('W');

        for (c1, c2) in new.iter().zip("World!".chars()) {
            assert_eq!(*c1, c2);
        }
    }
    #[test]
    fn from_iter() {
        let range = 0..10;
        let mut new = List::from_iter(range.clone());

        let mut range = range;
        while let Some(head) = new.first() {
            assert_eq!(*head, range.next().unwrap());
            new = new.pop_front();
        }
    }
    #[test]
    fn from_iter_to_iter() {
        let new = List::from_iter(0..10);

        let mut sum = 0;
        for (_, n) in new.iter().zip(core::iter::repeat(4)) {
            sum += n;
        }
        assert_eq!(sum, 40);
    }
    #[test]
    fn unsized_slice_tests() {
        let new: List<[i32]> = List::new();
        let new = new.prepend_sized([1, 1, 1]);
        let new = new.prepend_sized([2]);
        let new = new.prepend_sized([3; 76]);

        let iterator = new.iter();
        let new = new.reborrow();

        assert_eq!(new.first(), Some([3i32; 76].as_slice()));
        let new = new.pop_front();
        assert_eq!(new.first(), Some([2].as_slice()));
        let new = new.pop_front();
        assert_eq!(new.first(), Some([1, 1, 1].as_slice()));

        let mut sum = 0;
        for i in iterator.map(<[i32]>::iter).flatten() {
            sum += i;
        }
        assert_eq!(sum, 3 * 76 + 2 + 3 * 1);
    }
    #[test]
    fn dyn_test() {
        let new: List<dyn Debug> =
            List::from_iter_sized((0..5).map(|x| char::from_digit(x, 10).unwrap()));
        let new = new.prepend_sized("balls");
        let new = new.prepend_sized(0);
        let new = new.prepend_sized(core::f32::consts::PI);

        let mut sum = String::new();
        for i in new.iter() {
            sum += &format!("{i:.2?}");
        }
        assert_eq!(&sum, "3.140\"balls\"'0''1''2''3''4'");
    }
}
