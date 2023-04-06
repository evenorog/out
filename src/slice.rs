//! Functions for use with slices.
//!
//! # Examples
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::max(&mut v, 3);
//! assert_eq!(max, [1, 2, 4]);
//! assert_eq!(v, [-3, 1, 2, 4, -5]);
//! ```

use core::{cmp::Ordering, mem};

/// Implementation based on https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_cached_key.
macro_rules! find_n {
    ($t:ty, $slice:ident, $n:ident, $f: ident, $sort: expr) => {{
        let iter = $slice.iter().map($f).enumerate().map(|(i, k)| (k, i as $t));
        let mut sorted = $sort(iter, $n);
        for i in 0..$n {
            let mut idx = sorted[i].1;
            while (idx as usize) < i {
                idx = sorted[idx as usize].1;
            }
            sorted[i].1 = idx;
            $slice.swap(i, idx as usize);
        }
        &mut $slice[..$n]
    }};
}

/// Returns the `n` largest items.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::slice::max(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
pub fn max<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_by(v, n, T::cmp)
}

/// Returns the `n` smallest items.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::slice::min(&mut v, 3);
/// assert_eq!(min, [1, -3, -5]);
/// ```
pub fn min<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    min_by(v, n, T::cmp)
}

/// Returns the `n` largest items with a comparator function.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::slice::max_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [1, -3, -5]);
/// ```
pub fn max_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    if n == 0 {
        return &mut [];
    }

    let (left, right) = v.split_at_mut(n);
    crate::make_min_heap(left, &mut cmp);
    let mut i = 0;
    while i < right.len() {
        let item = &mut right[i];
        let root = &mut left[0];
        if cmp(root, item).is_lt() {
            mem::swap(root, item);
            crate::sift_down(left, &mut cmp, 0, n);
        }
        i += 1;
    }
    left
}

/// Returns the `n` smallest items with a comparator function.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::slice::min_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(max, [1, 2, 4]);
/// ```
pub fn min_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    max_by(v, n, |a, b| cmp(b, a))
}

/// Returns the `n` largest items with a key extraction function.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::slice::max_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
pub fn max_by_key<T, K: Ord>(v: &mut [T], n: usize, mut f: impl FnMut(&T) -> K) -> &mut [T] {
    max_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` smallest items with a key extraction function.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let min = out::slice::min_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(min, [-3, 2, 1]);
/// ```
pub fn min_by_key<T, K: Ord>(v: &mut [T], n: usize, mut f: impl FnMut(&T) -> K) -> &mut [T] {
    min_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` largest items with a key extraction function.
///
/// The key function is called only once per element, but for simple key functions `sort_by_key`
/// is likely to be faster.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::slice::max_by_cached_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
#[cfg(feature = "alloc")]
pub fn max_by_cached_key<T, K: Ord>(v: &mut [T], n: usize, f: impl FnMut(&T) -> K) -> &mut [T] {
    // Find the smallest type possible for the index, to reduce the amount of allocation needed.
    let sz_u8 = mem::size_of::<(K, u8)>();
    let sz_u16 = mem::size_of::<(K, u16)>();
    let sz_u32 = mem::size_of::<(K, u32)>();
    let sz_usize = mem::size_of::<(K, usize)>();
    if sz_u8 < sz_u16 && v.len() <= u8::MAX as usize {
        find_n!(u8, v, n, f, crate::iter::max)
    } else if sz_u16 < sz_u32 && v.len() <= u16::MAX as usize {
        find_n!(u16, v, n, f, crate::iter::max)
    } else if sz_u32 < sz_usize && v.len() <= u32::MAX as usize {
        find_n!(u32, v, n, f, crate::iter::max)
    } else {
        find_n!(usize, v, n, f, crate::iter::max)
    }
}

/// Returns the `n` smallest items with a key extraction function.
///
/// The key function is called only once per element, but for simple key functions `sort_by_key`
/// is likely to be faster.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let min = out::slice::min_by_cached_key(&mut v, 3, |a| a.abs());
/// assert_eq!(min, [-3, 2, 1]);
/// ```
#[cfg(feature = "alloc")]
pub fn min_by_cached_key<T, K: Ord>(v: &mut [T], n: usize, f: impl FnMut(&T) -> K) -> &mut [T] {
    // Find the smallest type possible for the index, to reduce the amount of allocation needed.
    let sz_u8 = mem::size_of::<(K, u8)>();
    let sz_u16 = mem::size_of::<(K, u16)>();
    let sz_u32 = mem::size_of::<(K, u32)>();
    let sz_usize = mem::size_of::<(K, usize)>();
    if sz_u8 < sz_u16 && v.len() <= u8::MAX as usize {
        find_n!(u8, v, n, f, crate::iter::min)
    } else if sz_u16 < sz_u32 && v.len() <= u16::MAX as usize {
        find_n!(u16, v, n, f, crate::iter::min)
    } else if sz_u32 < sz_usize && v.len() <= u32::MAX as usize {
        find_n!(u32, v, n, f, crate::iter::min)
    } else {
        find_n!(usize, v, n, f, crate::iter::min)
    }
}
