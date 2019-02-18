//! Provides functionality to get the `n` largest items from a `&mut [T]`.
//!
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::max(&mut v, 3);
//! assert_eq!(max, [1, 2, 4]);
//! ```
//!
//! It's worth noting that the largest item will be the last item in the slice that is returned.
//! This library can provide significant performance increase compared to sorting or
//! converting to a heap when `n` is relatively small compared to the length of the slice.
//! In addition, the unstable methods can be used without
//! the standard library by disabling the default features.
//!
//! n = `100`, len = `1_000_000`:
//! ```text
//! test binary_heap   ... bench:   6,599,355 ns/iter (+/- 84,674)
//! test max           ... bench:     669,726 ns/iter (+/- 13,595)
//! test max_unstable  ... bench:     635,435 ns/iter (+/- 9,683)
//! test sort          ... bench:  62,585,547 ns/iter (+/- 1,361,258)
//! test sort_unstable ... bench:  34,595,265 ns/iter (+/- 739,255)
//! ```
//!
//! n = `1000`, len = `10_000_000`:
//! ```text
//! test binary_heap   ... bench:  78,343,761 ns/iter (+/- 2,579,283)
//! test max           ... bench:  14,970,673 ns/iter (+/- 580,660)
//! test max_unstable  ... bench:  14,870,344 ns/iter (+/- 573,286)
//! test sort          ... bench: 716,240,206 ns/iter (+/- 23,188,586)
//! test sort_unstable ... bench: 385,681,859 ns/iter (+/- 19,847,519)
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![doc(html_root_url = "https://docs.rs/out/2.0.1")]
#![deny(
    bad_style,
    bare_trait_objects,
    missing_debug_implementations,
    missing_docs,
    unused_import_braces,
    unused_qualifications
)]

#[cfg(not(feature = "std"))]
use core::{cmp::Ordering, mem, slice};
#[cfg(feature = "std")]
use std::{cmp::Ordering, mem, slice};

/// Get the `n` largest items.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::max(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
#[inline]
#[cfg(feature = "std")]
pub fn max<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_by(v, n, T::cmp)
}

/// Get the `n` largest items.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
/// This method should be faster than `max` in most cases, and can be used with `no_std`.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::max_unstable(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
#[inline]
pub fn max_unstable<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_unstable_by(v, n, T::cmp)
}

/// Get the `n` largest items with a comparator function.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::max_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [1, -3, -5]);
/// ```
#[inline]
#[cfg(feature = "std")]
pub fn max_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    if n == 0 {
        return &mut [];
    }
    let (mut left, mut right) = v.split_at_mut(n);
    left.sort_by(&mut cmp);
    let mut i = 0;
    while i < right.len() {
        // Using `==` seems to be 10-30% faster than `!=`.
        if cmp(&right[i], &left[0]) == Ordering::Less {
            i += 1;
        } else if cmp(&right[i], &left[n / 2]) == Ordering::Greater {
            right.swap(i, 0);
            let mut j = n - 1;
            if cmp(&left[j], &right[0]) == Ordering::Greater {
                mem::swap(&mut left[j], &mut right[0]);
                while cmp(&left[j], &left[j - 1]) == Ordering::Less {
                    left.swap(j, j - 1);
                    j -= 1;
                }
            }
            unsafe {
                shift_slice_right(&mut left, &mut right, 1);
            }
        } else {
            let mut j = 0;
            mem::swap(&mut right[i], &mut left[j]);
            while j < n - 1 && cmp(&left[j], &left[j + 1]) != Ordering::Less {
                left.swap(j, j + 1);
                j += 1;
            }
            i += 1;
        }
    }
    left
}

/// Get the `n` largest items with a comparator function.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
/// This method should be faster than `max_unstable_by` in most cases, and can be used with `no_std`.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::max_unstable_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [1, -3, -5]);
/// ```
#[inline]
pub fn max_unstable_by<T>(
    v: &mut [T],
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> &mut [T] {
    if n == 0 {
        return &mut [];
    }
    let (mut left, mut right) = v.split_at_mut(n);
    left.sort_unstable_by(&mut cmp);
    let mut i = 0;
    while i < right.len() {
        // Using `==` seems to be 10-30% faster than `!=`.
        if cmp(&left[0], &right[i]) == Ordering::Greater {
            i += 1;
        } else if cmp(&right[i], &left[n / 2]) == Ordering::Greater {
            right.swap(i, 0);
            let mut j = n - 1;
            if cmp(&left[j], &right[0]) == Ordering::Greater {
                mem::swap(&mut left[j], &mut right[0]);
                while cmp(&left[j], &left[j - 1]) == Ordering::Less {
                    left.swap(j, j - 1);
                    j -= 1;
                }
            }
            unsafe {
                shift_slice_right(&mut left, &mut right, 1);
            }
        } else {
            let mut j = 0;
            mem::swap(&mut right[i], &mut left[j]);
            while j < n - 1 && cmp(&left[j], &left[j + 1]) == Ordering::Greater {
                left.swap(j, j + 1);
                j += 1;
            }
            i += 1;
        }
    }
    left
}

/// Get the `n` largest items with a key extraction function.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::max_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
#[inline]
#[cfg(feature = "std")]
pub fn max_by_key<T, K: Ord>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T) -> K) -> &mut [T] {
    max_by(v, n, |a, b| cmp(a).cmp(&cmp(b)))
}

/// Get the `n` largest items with a key extraction function.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
/// This method should be faster than `max_unstable_by_key` in most cases, and can be used with `no_std`.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::max_unstable_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
#[inline]
pub fn max_unstable_by_key<T, K: Ord>(
    v: &mut [T],
    n: usize,
    mut cmp: impl FnMut(&T) -> K,
) -> &mut [T] {
    max_unstable_by(v, n, |a, b| cmp(a).cmp(&cmp(b)))
}

/// Shift the left slice to the right while shrinking the right slice by `count`.
///
/// ```text
/// [a, b][c, d, e] -> a [b, c][d, e]
/// ```
#[inline]
unsafe fn shift_slice_right<T>(left: &mut &mut [T], right: &mut &mut [T], count: usize) {
    let len = left.len();
    let ptr = left.as_mut_ptr();
    *left = slice::from_raw_parts_mut(ptr.add(count), len);
    let len = right.len();
    let ptr = right.as_mut_ptr();
    *right = slice::from_raw_parts_mut(ptr.add(count), len - count);
}
