//! Provides fast min and max functionality for collections.
//!
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::max(&mut v, 3);
//! assert_eq!(max, [4, 2, 1]);
//! assert_eq!(v, [4, 2, 1, -5, -3]);
//! ```
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

/// Creates a min binary heap from the given slice using the comparator function provided.
fn make_min_heap<T>(v: &mut [T], f: &mut impl FnMut(&T, &T) -> Ordering) {
    let mut i = v.len() / 2;
    while i > 0 {
        i -= 1;
        sift_down(v, i, f);
    }
}

/// Sifts down the element at index `i` using the comparator function provided.
fn sift_down<T>(v: &mut [T], mut i: usize, f: &mut impl FnMut(&T, &T) -> Ordering) {
    let len = v.len();
    loop {
        let left = i * 2 + 1;
        if left >= len {
            break;
        }

        let right = left + 1;
        let child = if right < len && f(&v[right], &v[left]).is_lt() {
            right
        } else {
            left
        };

        if f(&v[child], &v[i]).is_ge() {
            break;
        }

        v.swap(i, child);
        i = child;
    }
}

/// Sorts the min binary heap using the comparator function provided.
fn sort_min_heap<T>(v: &mut [T], f: &mut impl FnMut(&T, &T) -> Ordering) {
    let mut i = v.len();
    while i > 1 {
        i -= 1;
        v.swap(0, i);
        sift_down(&mut v[..i], 0, f);
    }
}
