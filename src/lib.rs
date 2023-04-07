//! Provides fast min and max functionality for collections.
//!
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::max(&mut v, 3);
//! assert_eq!(max, [1, 4, 2]);
//! assert_eq!(out::slice::min(max, 2), [2, 1]);
//! ```
//!
//! The order of the returned items is not guaranteed to be sorted.
//!
//! This library can provide significant performance increase compared to sorting or
//! converting to a heap when `n` is small compared to the length of the slice or iterator.

#![cfg_attr(not(feature = "std"), no_std)]
#![doc(html_root_url = "https://docs.rs/out")]
#![deny(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod slice;

#[cfg(feature = "alloc")]
pub mod iter;

use core::cmp::Ordering;
use std::ptr;

fn make_min_heap<T>(v: &mut [T], f: &mut impl FnMut(&T, &T) -> Ordering) {
    let len = v.len();
    let mut i = len / 2;
    while i > 0 {
        i -= 1;
        unsafe { sift_down(v, i, len, f) };
    }
}

unsafe fn sift_down<T>(
    v: &mut [T],
    mut i: usize,
    end: usize,
    f: &mut impl FnMut(&T, &T) -> Ordering,
) {
    loop {
        let left = i * 2 + 1;
        if left >= end {
            break;
        }
        let right = left + 1;
        let child = if right < end && f(v.get_unchecked(right), v.get_unchecked(left)).is_lt() {
            right
        } else {
            left
        };

        if f(v.get_unchecked(child), v.get_unchecked(i)).is_ge() {
            break;
        }

        let p = v.as_mut_ptr();
        ptr::swap(p.add(child), p.add(i));
        i = child;
    }
}
