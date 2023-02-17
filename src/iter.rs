//! Functions for use with iterators.
//!
//! # Examples
//! ```
//! let max = out::iter::max(-10..10, 3);
//! assert_eq!(max, [7, 8, 9]);
//! let min = out::iter::min(max, 10);
//! assert_eq!(min, [9, 8, 7]);
//! ```

use alloc::vec::Vec;
use core::cmp::Ordering;

/// Returns the `n` largest items from an iterator.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let max = out::iter::max(-10..10, 3);
/// assert_eq!(max, [7, 8, 9]);
/// ```
pub fn max<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    max_by(iter, n, T::cmp)
}

/// Returns the `n` smallest items from an iterator.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let min = out::iter::min(-10..10, 3);
/// assert_eq!(min, [-8, -9, -10]);
/// ```
pub fn min<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    min_by(iter, n, T::cmp)
}

/// Returns the `n` largest items from an iterator with a comparator function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let min = out::iter::max_by(-10_i32..10, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [-8, -9, -10]);
/// ```
pub fn max_by<T>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Vec<T> {
    if n == 0 {
        return Vec::new();
    }

    let mut v = Vec::with_capacity(n);
    let mut iter = iter.into_iter();
    while v.len() < n {
        let Some(item) = iter.next() else {
            break;
        };
        v.push(item);
    }

    v.sort_by(&mut cmp);

    for item in iter {
        if cmp(&item, &v[0]) != Ordering::Less {
            v[0] = item;
            let mut i = 0;
            while i < n - 1 && cmp(&v[i], &v[i + 1]) != Ordering::Less {
                v.swap(i, i + 1);
                i += 1;
            }
        }
    }
    v
}

/// Returns the `n` smallest items from an iterator with a comparator function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let max = out::iter::min_by(-10_i32..10, 3, |a, b| b.cmp(a));
/// assert_eq!(max, [7, 8, 9]);
/// ```
pub fn min_by<T>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Vec<T> {
    max_by(iter, n, |a, b| cmp(b, a))
}

/// Returns the `n` largest items from an iterator with a key extraction function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let max = out::iter::max_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(max, [-9, 9, -10]);
/// ```
pub fn max_by_key<T, K: Ord>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> Vec<T> {
    max_by(iter, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` smallest items from an iterator with a key extraction function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
///
/// # Examples
/// ```
/// let max = out::iter::min_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(max, [-1, 1, 0]);
/// ```
pub fn min_by_key<T, K: Ord>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> Vec<T> {
    min_by(iter, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` largest items from an iterator.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`max`](fn.max.html).
///
/// # Examples
/// ```
/// let max = out::iter::max_unstable(-10..10, 3);
/// assert_eq!(max, [7, 8, 9]);
/// ```
pub fn max_unstable<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    max_unstable_by(iter, n, T::cmp)
}

/// Returns the `n` smallest items from an iterator.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`min`](fn.min.html).
///
/// # Examples
/// ```
/// let min = out::iter::min_unstable(-10..10, 3);
/// assert_eq!(min, [-8, -9, -10]);
/// ```
pub fn min_unstable<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    min_unstable_by(iter, n, T::cmp)
}

/// Returns the `n` largest items from an iterator with a comparator function.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`max_by`](fn.max_by.html).
///
/// # Examples
/// ```
/// let min = out::iter::max_unstable_by(-10..10, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [-8, -9, -10]);
/// ```
pub fn max_unstable_by<T>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Vec<T> {
    if n == 0 {
        return Vec::new();
    }

    let mut v = Vec::with_capacity(n);
    let mut iter = iter.into_iter();
    while v.len() < n {
        let Some(item) = iter.next() else {
            break;
        };
        v.push(item);
    }

    v.sort_unstable_by(&mut cmp);

    for item in iter {
        if cmp(&item, &v[0]) == Ordering::Greater {
            v[0] = item;
            let mut i = 0;
            while i < n - 1 && cmp(&v[i], &v[i + 1]) == Ordering::Greater {
                v.swap(i, i + 1);
                i += 1;
            }
        }
    }
    v
}

/// Returns the `n` smallest items from an iterator with a comparator function.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`min_by`](fn.min_by.html).
///
/// # Examples
/// ```
/// let max = out::iter::min_unstable_by(-10..10, 3, |a, b| b.cmp(a));
/// assert_eq!(max, [7, 8, 9]);
/// ```
pub fn min_unstable_by<T>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Vec<T> {
    max_unstable_by(iter, n, |a, b| cmp(b, a))
}

/// Returns the `n` largest items from an iterator with a key extraction function.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`max_by_key`](fn.max_by_key.html).
///
/// # Examples
/// ```
/// let max = out::iter::max_unstable_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(max, [9, -9, -10]);
/// ```
pub fn max_unstable_by_key<T, K: Ord>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> Vec<T> {
    max_unstable_by(iter, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` smallest items from an iterator with a key extraction function.
///
/// This sort is unstable (i.e. may reorder equal elements)
/// and typically faster than [`min_by_key`](fn.min_by_key.html).
///
/// # Examples
/// ```
/// let min = out::iter::min_unstable_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(min, [1, -1, 0]);
/// ```
pub fn min_unstable_by_key<T, K: Ord>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> Vec<T> {
    min_unstable_by(iter, n, |a, b| f(a).cmp(&f(b)))
}
