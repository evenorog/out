//! Functions for use with slices.
//!
//! # Examples
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::max(&mut v, 3);
//! assert_eq!(max, [1, 2, 4]);
//! assert_eq!(v, [-3, 1, 2, 4, -5]);
//! ```

use core::{cmp::Ordering, mem, slice};

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
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn max<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_by(v, n, T::cmp)
}

/// Returns the `n` smallest items.
///
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn min<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    min_by(v, n, T::cmp)
}

/// Returns the `n` largest items with a comparator function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn max_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    if n == 0 {
        return &mut [];
    }

    let (mut left, mut right) = v.split_at_mut(n);
    left.sort_by(&mut cmp);
    let mut i = 0;
    while i < right.len() {
        if cmp(&right[i], &left[0]) == Ordering::Less {
            i += 1;
        } else if cmp(&right[i], &left[n / 2]) == Ordering::Greater {
            swap_gt_half(&mut left, &mut right, n, i, &mut cmp);
        } else {
            swap_lt_half(left, right, n, &mut i, &mut cmp);
        }
    }
    left
}

/// Returns the `n` smallest items with a comparator function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn min_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
    max_by(v, n, |a, b| cmp(b, a))
}

/// Returns the `n` largest items with a key extraction function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn max_by_key<T, K: Ord>(v: &mut [T], n: usize, mut f: impl FnMut(&T) -> K) -> &mut [T] {
    max_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` smallest items with a key extraction function.
///
/// This function is stable, i.e. it preserves the order of equal elements.
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
#[cfg(feature = "alloc")]
pub fn min_by_key<T, K: Ord>(v: &mut [T], n: usize, mut f: impl FnMut(&T) -> K) -> &mut [T] {
    min_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` largest items with a key extraction function.
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
        find_n!(u8, v, n, f, crate::iter::max_unstable)
    } else if sz_u16 < sz_u32 && v.len() <= u16::MAX as usize {
        find_n!(u16, v, n, f, crate::iter::max_unstable)
    } else if sz_u32 < sz_usize && v.len() <= u32::MAX as usize {
        find_n!(u32, v, n, f, crate::iter::max_unstable)
    } else {
        find_n!(usize, v, n, f, crate::iter::max_unstable)
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
        find_n!(u8, v, n, f, crate::iter::min_unstable)
    } else if sz_u16 < sz_u32 && v.len() <= u16::MAX as usize {
        find_n!(u16, v, n, f, crate::iter::min_unstable)
    } else if sz_u32 < sz_usize && v.len() <= u32::MAX as usize {
        find_n!(u32, v, n, f, crate::iter::min_unstable)
    } else {
        find_n!(usize, v, n, f, crate::iter::min_unstable)
    }
}

/// Returns the `n` largest items.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`max`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::slice::max_unstable(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// ```
pub fn max_unstable<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    max_unstable_by(v, n, T::cmp)
}

/// Returns the `n` smallest items.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`min`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::slice::min_unstable(&mut v, 3);
/// assert_eq!(min, [1, -3, -5]);
/// ```
pub fn min_unstable<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
    min_unstable_by(v, n, T::cmp)
}

/// Returns the `n` largest items with a comparator function.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`max_by`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let min = out::slice::max_unstable_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(min, [1, -3, -5]);
/// ```
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
        if cmp(&left[0], &right[i]) == Ordering::Greater {
            i += 1;
        } else if cmp(&right[i], &left[n / 2]) == Ordering::Greater {
            swap_gt_half(&mut left, &mut right, n, i, &mut cmp);
        } else {
            swap_lt_half(left, right, n, &mut i, &mut cmp);
        }
    }
    left
}

/// Returns the `n` smallest items with a comparator function.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`min_by`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::slice::min_unstable_by(&mut v, 3, |a, b| b.cmp(a));
/// assert_eq!(max, [1, 2, 4]);
/// ```
pub fn min_unstable_by<T>(
    v: &mut [T],
    n: usize,
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> &mut [T] {
    max_unstable_by(v, n, |a, b| cmp(b, a))
}

/// Returns the `n` largest items with a key extraction function.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`max_by_key`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let max = out::slice::max_unstable_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(max, [-3, 4, -5]);
/// ```
pub fn max_unstable_by_key<T, K: Ord>(
    v: &mut [T],
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> &mut [T] {
    max_unstable_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Returns the `n` smallest items with a key extraction function.
///
/// This function is unstable (i.e. may reorder equal elements), in-place
/// (i.e. does not allocate), and typically faster than [`min_by_key`].
///
/// # Panics
/// Panics if `n > len`.
///
/// # Examples
/// ```
/// let mut v = [-5_i32, 4, 1, -3, 2];
/// let min = out::slice::min_unstable_by_key(&mut v, 3, |a| a.abs());
/// assert_eq!(min, [-3, 2, 1]);
/// ```
pub fn min_unstable_by_key<T, K: Ord>(
    v: &mut [T],
    n: usize,
    mut f: impl FnMut(&T) -> K,
) -> &mut [T] {
    min_unstable_by(v, n, |a, b| f(a).cmp(&f(b)))
}

/// Shift the left slice to the right while shrinking the right slice.
///
/// ```text
/// [a, b][c, d, e] -> a [b, c][d, e]
/// ```
///
/// # Safety
/// The two slices must be next to each other and `right` can not be empty.
unsafe fn shift_slice_right<T>(left: &mut &mut [T], right: &mut &mut [T]) {
    let len = left.len();
    let ptr = left.as_mut_ptr();
    *left = slice::from_raw_parts_mut(ptr.add(1), len);
    let len = right.len();
    let ptr = right.as_mut_ptr();
    *right = slice::from_raw_parts_mut(ptr.add(1), len - 1);
}

fn swap_gt_half<T>(
    left: &mut &mut [T],
    right: &mut &mut [T],
    n: usize,
    i: usize,
    cmp: &mut impl FnMut(&T, &T) -> Ordering,
) {
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
        shift_slice_right(left, right);
    }
}

fn swap_lt_half<T>(
    left: &mut [T],
    right: &mut [T],
    n: usize,
    i: &mut usize,
    cmp: &mut impl FnMut(&T, &T) -> Ordering,
) {
    mem::swap(&mut left[0], &mut right[*i]);
    let mut j = 0;
    while j < n - 1 && cmp(&left[j], &left[j + 1]) != Ordering::Less {
        left.swap(j, j + 1);
        j += 1;
    }
    *i += 1;
}
