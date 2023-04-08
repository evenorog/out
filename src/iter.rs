//! Functions for use with iterators.

use alloc::vec::Vec;
use core::cmp::Ordering;

/// Returns the `n` largest items from an iterator.
///
/// # Examples
/// ```
/// let max = out::iter::max(-10..10, 3);
/// assert_eq!(max, [9, 8, 7]);
/// ```
pub fn max<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    max_by(iter, n, T::cmp)
}

/// Returns the `n` smallest items from an iterator.
///
/// # Examples
/// ```
/// let min = out::iter::min(-10..10, 3);
/// assert_eq!(min, [-10, -9, -8]);
/// ```
pub fn min<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
    min_by(iter, n, T::cmp)
}

/// Returns the `n` largest items from an iterator with a comparator function.
///
/// # Examples
/// ```
/// let min = out::iter::max_by(-10_i32..10, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [-10, -9, -8]);
/// ```
pub fn max_by<T>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Vec<T> {
    if n == 0 {
        return Vec::new();
    }

    let mut right = iter.into_iter();
    let mut left = right.by_ref().take(n).collect::<Vec<_>>();
    crate::make_min_heap(&mut left, &mut cmp);
    // Same as `slice::max_by`.
    for i in right {
        let min = &mut left[0];
        if cmp(&i, min).is_gt() {
            *min = i;
            crate::sift_down(&mut left, 0, &mut cmp);
        }
    }

    crate::sort_min_heap(&mut left, &mut cmp);
    left
}

/// Returns the `n` smallest items from an iterator with a comparator function.
///
/// # Examples
/// ```
/// let max = out::iter::min_by(-10_i32..10, 3, |a, b| b.cmp(a));
/// assert_eq!(max, [9, 8, 7]);
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
/// # Examples
/// ```
/// let max = out::iter::max_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(max, [-10, -9, 9]);
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
/// # Examples
/// ```
/// let min = out::iter::min_by_key(-10_i32..10, 3, |a| a.abs());
/// assert_eq!(min, [0, -1, 1]);
/// ```
pub fn min_by_key<T, K: Ord>(
    iter: impl IntoIterator<Item = T>,
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> Vec<T> {
    min_by(iter, n, |a, b| f(a).cmp(&f(b)))
}
