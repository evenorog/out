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

#![no_std]
#![doc(html_root_url = "https://docs.rs/out")]
#![deny(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Functions for use with slices.
///
/// # Examples
/// ```
/// let mut v = [-5, 4, 1, -3, 2];
/// let max = out::slice::max(&mut v, 3);
/// assert_eq!(max, [1, 2, 4]);
/// assert_eq!(v, [-3, 1, 2, 4, -5]);
/// ```
pub mod slice {
    use core::{cmp::Ordering, mem, slice};

    /// Returns the `n` largest items.
    ///
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
                    shift_slice_right(&mut left, &mut right);
                }
            } else {
                mem::swap(&mut left[0], &mut right[i]);
                let mut j = 0;
                while j < n - 1 && cmp(&left[j], &left[j + 1]) != Ordering::Less {
                    left.swap(j, j + 1);
                    j += 1;
                }
                i += 1;
            }
        }
        left
    }

    /// Returns the `n` smallest items with a comparator function.
    ///
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
        // Implementation based on https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_cached_key.
        macro_rules! max_by_cached_key {
            ($t:ty) => {{
                // All elements are unique since they contain the index, so we can use the unstable version.
                let iter = v.iter().map(f).enumerate().map(|(i, k)| (k, i as $t));
                let mut sorted = crate::iter::max_unstable(iter, n);
                for i in 0..n {
                    let mut idx = sorted[i].1;
                    while (idx as usize) < i {
                        idx = sorted[idx as usize].1;
                    }
                    sorted[i].1 = idx;
                    v.swap(i, idx as usize);
                }
                &mut v[..n]
            }};
        }
        // Find the smallest type possible for the index, to reduce the amount of allocation needed.
        let sz_u8 = mem::size_of::<(K, u8)>();
        let sz_u16 = mem::size_of::<(K, u16)>();
        let sz_u32 = mem::size_of::<(K, u32)>();
        let sz_usize = mem::size_of::<(K, usize)>();
        if sz_u8 < sz_u16 && v.len() <= u8::max_value() as usize {
            max_by_cached_key!(u8)
        } else if sz_u16 < sz_u32 && v.len() <= u16::max_value() as usize {
            max_by_cached_key!(u16)
        } else if sz_u32 < sz_usize && v.len() <= u32::max_value() as usize {
            max_by_cached_key!(u32)
        } else {
            max_by_cached_key!(usize)
        }
    }

    /// Returns the `n` smallest items with a key extraction function.
    ///
    /// The key function is called only once per element, but for simple key functions `sort_by_key`
    /// is likely to be faster.
    ///
    /// This sort is stable, i.e. it preserves the order of equal elements.
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
        // Implementation based on https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_cached_key.
        macro_rules! min_by_cached_key {
            ($t:ty) => {{
                // All elements are unique since they contain the index, so we can use the unstable version.
                let iter = v.iter().map(f).enumerate().map(|(i, k)| (k, i as $t));
                let mut sorted = crate::iter::min_unstable(iter, n);
                for i in 0..n {
                    let mut idx = sorted[i].1;
                    while (idx as usize) < i {
                        idx = sorted[idx as usize].1;
                    }
                    sorted[i].1 = idx;
                    v.swap(i, idx as usize);
                }
                &mut v[..n]
            }};
        }
        // Find the smallest type possible for the index, to reduce the amount of allocation needed.
        let sz_u8 = mem::size_of::<(K, u8)>();
        let sz_u16 = mem::size_of::<(K, u16)>();
        let sz_u32 = mem::size_of::<(K, u32)>();
        let sz_usize = mem::size_of::<(K, usize)>();
        if sz_u8 < sz_u16 && v.len() <= u8::max_value() as usize {
            min_by_cached_key!(u8)
        } else if sz_u16 < sz_u32 && v.len() <= u16::max_value() as usize {
            min_by_cached_key!(u16)
        } else if sz_u32 < sz_usize && v.len() <= u32::max_value() as usize {
            min_by_cached_key!(u32)
        } else {
            min_by_cached_key!(usize)
        }
    }

    /// Returns the `n` largest items.
    ///
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`max`](fn.max.html).
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
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`min`](fn.min.html).
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
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`max_by`](fn.max_by.html).
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
                    shift_slice_right(&mut left, &mut right);
                }
            } else {
                mem::swap(&mut left[0], &mut right[i]);
                let mut j = 0;
                while j < n - 1 && cmp(&left[j], &left[j + 1]) == Ordering::Greater {
                    left.swap(j, j + 1);
                    j += 1;
                }
                i += 1;
            }
        }
        left
    }

    /// Returns the `n` smallest items with a comparator function.
    ///
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`min_by`](fn.min_by.html).
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
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`max_by_key`](fn.max_by_key.html).
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
    /// This sort is unstable (i.e. may reorder equal elements), in-place
    /// (i.e. does not allocate), and typically faster than [`min_by_key`](fn.min_by_key.html).
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
}

/// Functions for use with iterators.
///
/// # Examples
/// ```
/// let max = out::iter::max(-10..10, 3);
/// assert_eq!(max, [7, 8, 9]);
/// ```
#[cfg(feature = "alloc")]
pub mod iter {
    use alloc::vec::Vec;
    use core::cmp::Ordering;

    /// Returns the `n` largest items from an iterator.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
        let mut v = Vec::with_capacity(n);
        if n == 0 {
            return v;
        }
        let mut iter = iter.into_iter();
        while v.len() < n {
            let item = iter
                .next()
                .expect("`n` can not be larger than the iterator");
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
        let mut v = Vec::with_capacity(n);
        if n == 0 {
            return v;
        }
        let mut iter = iter.into_iter();
        while v.len() < n {
            let item = iter
                .next()
                .expect("`n` can not be larger than the iterator");
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
    /// # Panics
    /// Panics if `n > len`.
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
}
