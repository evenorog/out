//! Provides fast min and max functionality for collections.
//!
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::max(&mut v, 3);
//! assert_eq!(max, [1, 2, 4]);
//! assert_eq!(out::slice::min(max, 2), [2, 1]);
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

fn make_min_heap<T, F>(v: &mut [T], f: &mut F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    let len = v.len();
    if len < 2 {
        return;
    }
    let mut i = len / 2 - 1;
    while i > 0 {
        sift_down(v, f, i, len);
        i -= 1;
    }
    sift_down(v, f, 0, len);
}

fn sift_down<T, F>(v: &mut [T], f: &mut F, mut i: usize, end: usize)
where
    F: FnMut(&T, &T) -> Ordering,
{
    loop {
        let left = i * 2 + 1;
        if left >= end {
            break;
        }
        let right = left + 1;
        let child = if right < end && f(&v[right], &v[left]).is_lt() {
            right
        } else {
            left
        };

        if f(&v[child], &v[i]).is_ge() {
            break;
        }

        v.swap(child, i);
        i = child;
    }
}
