//! Provides functionality to get `n` items from a `&mut [T]`.
//!
//! This library can provide significant performance increase compared to sorting the whole list
//! when `n` is relatively small.
//!
//! ```text
//! N = 100, LEN = 1_000_000, RANGE = 1_000_000:
//! test binary_heap   ... bench:   6,706,060 ns/iter (+/- 102,080)
//! test max           ... bench:     846,891 ns/iter (+/- 19,960)
//! test max_unstable  ... bench:     844,215 ns/iter (+/- 18,365)
//! test sort          ... bench:  62,280,523 ns/iter (+/- 997,028)
//! test sort_unstable ... bench:  34,822,256 ns/iter (+/- 3,047,204)
//! ```

#![cfg_attr(not(feature = "use_std"), no_std)]
#![doc(html_root_url = "https://docs.rs/out/0.5.5")]
#![deny(
    bad_style,
    bare_trait_objects,
    missing_debug_implementations,
    missing_docs,
    unused_import_braces,
    unused_qualifications
)]

#[cfg(not(feature = "use_std"))]
use core::cmp::Ordering;
#[cfg(not(feature = "use_std"))]
use core::mem;
#[cfg(not(feature = "use_std"))]
use core::slice;
#[cfg(feature = "use_std")]
use std::cmp::Ordering;
#[cfg(feature = "use_std")]
use std::mem;
#[cfg(feature = "use_std")]
use std::slice;

/// Get the `n` largest items.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::max(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
#[inline]
#[cfg(feature = "use_std")]
pub fn max<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_by(v, n, |a, b| a.cmp(b))
}

/// Get the `n` largest items.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::max_unstable(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
#[inline]
pub fn max_unstable<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_unstable_by(v, n, |a, b| a.cmp(b))
}

/// Get the `n` largest items with a comparator function.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::max_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [1, -3, -5]);
/// ```
#[inline]
#[cfg(feature = "use_std")]
pub fn max_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    if n == 0 {
        return &mut [];
    }
    let (mut max, mut v) = v.split_at_mut(n);
    max.sort_by(&mut cmp);
    let mut i = 0;
    while i < v.len() {
        if cmp(&v[i], &max[0]) == Ordering::Less {
            i += 1;
        } else if cmp(&v[i], &max[n / 2]) == Ordering::Greater && i < v.len() - 1 {
            v.swap(i, 0);
            let mut j = n - 1;
            if cmp(&max[j], &v[0]) == Ordering::Greater {
                mem::swap(&mut max[j], &mut v[0]);
                while cmp(&max[j], &max[j - 1]) == Ordering::Less {
                    max.swap(j, j - 1);
                    j -= 1;
                }
            }
            unsafe {
                shift_slice_right(&mut max, &mut v, 1);
            }
        } else {
            let mut j = 0;
            mem::swap(&mut v[i], &mut max[j]);
            while j < n - 1 && cmp(&max[j], &max[j + 1]) != Ordering::Less {
                max.swap(j, j + 1);
                j += 1;
            }
            i += 1;
        }
    }
    max
}

/// Get the `n` largest items with a comparator function.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
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
    let (mut max, mut v) = v.split_at_mut(n);
    max.sort_unstable_by(&mut cmp);
    let mut i = 0;
    while i < v.len() {
        if cmp(&v[i], &max[0]) != Ordering::Greater {
            i += 1;
        } else if cmp(&v[i], &max[n / 2]) == Ordering::Greater && i < v.len() - 1 {
            v.swap(i, 0);
            let mut j = n - 1;
            if cmp(&max[j], &v[0]) == Ordering::Greater {
                mem::swap(&mut max[j], &mut v[0]);
                while cmp(&max[j], &max[j - 1]) == Ordering::Less {
                    max.swap(j, j - 1);
                    j -= 1;
                }
            }
            unsafe {
                shift_slice_right(&mut max, &mut v, 1);
            }
        } else {
            let mut j = 0;
            mem::swap(&mut v[i], &mut max[j]);
            while j < n - 1 && cmp(&max[j], &max[j + 1]) == Ordering::Greater {
                max.swap(j, j + 1);
                j += 1;
            }
            i += 1;
        }
    }
    max
}

/// Get the `n` largest items with a key extraction function.
///
/// This method is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::max_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
#[inline]
#[cfg(feature = "use_std")]
pub fn max_by_key<T, K: Ord>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T) -> K) -> &mut [T] {
    max_by(v, n, |a, b| cmp(a).cmp(&cmp(b)))
}

/// Get the `n` largest items with a key extraction function.
///
/// This method is not stable, i.e. it may not preserve the order of equal elements.
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

/// Grow the left slice while shrinking the right slice by `count`.
///
/// ```text
/// [a, b][c, d, e] -> [a, b, c][d, e]
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
