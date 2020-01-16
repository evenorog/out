//! Provides partial sorting for slices and iterators.
//!
//! ```
//! let mut v = [-5, 4, 1, -3, 2];
//! let max = out::slice::sort(&mut v, 3);
//! assert_eq!(max, [1, 2, 4]);
//! ```
//!
//! This library can provide significant performance increase compared to sorting or
//! converting to a heap when `n` is small compared to the length of the slice or iterator.
//!
//! # Benchmarks
//!
//! *n = 100, len = 1_000_000:*
//!
//! ```text
//! openSUSE Tumbleweed, i7-5820K @ 3.30GHz, and 16GiB RAM:
//!
//! test iter::sort                ... bench:     918,253 ns/iter (+/- 99,863)
//! test iter::sort_unstable       ... bench:     916,908 ns/iter (+/- 58,050)
//! test slice::sort               ... bench:     698,643 ns/iter (+/- 46,373)
//! test slice::sort_by_cached_key ... bench:   1,516,099 ns/iter (+/- 37,853)
//! test slice::sort_unstable      ... bench:     655,286 ns/iter (+/- 25,017)
//! test std::binary_heap          ... bench:   6,592,801 ns/iter (+/- 780,590)
//! test std::sort                 ... bench:  63,192,028 ns/iter (+/- 2,338,506)
//! test std::sort_by_cached_key   ... bench:  66,058,834 ns/iter (+/- 5,447,387)
//! test std::sort_unstable        ... bench:  30,953,024 ns/iter (+/- 1,141,696)
//! ```
//!
//! ```text
//! Windows 10 (msvc), i7-5820K @ 3.30GHz, and 16GiB RAM:
//!
//! test iter::sort                ... bench:   2,650,615 ns/iter (+/- 1,427,458)
//! test iter::sort_unstable       ... bench:   2,604,860 ns/iter (+/- 1,001,639)
//! test slice::sort               ... bench:   2,353,487 ns/iter (+/- 1,140,791)
//! test slice::sort_by_cached_key ... bench:   3,317,930 ns/iter (+/- 1,115,283)
//! test slice::sort_unstable      ... bench:   2,221,975 ns/iter (+/- 1,232,170)
//! test std::binary_heap          ... bench:   8,666,095 ns/iter (+/- 3,790,987)
//! test std::sort                 ... bench:  73,953,630 ns/iter (+/- 23,036,689)
//! test std::sort_by_cached_key   ... bench:  79,681,540 ns/iter (+/- 24,554,555)
//! test std::sort_unstable        ... bench:  35,327,180 ns/iter (+/- 8,306,700)
//! ```

#![no_std]
#![doc(html_root_url = "https://docs.rs/out")]
#![deny(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Functions for use with slices.
pub mod slice {
    use core::{cmp::Ordering, mem, slice};

    /// Get the `n` largest items.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5, 4, 1, -3, 2];
    /// let max = out::slice::sort(&mut v, 3);
    /// assert_eq!(max, [1, 2, 4]);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn sort<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
        sort_by(v, n, T::cmp)
    }

    /// Get the `n` largest items with a comparator function.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5, 4, 1, -3, 2];
    /// let min = out::slice::sort_by(&mut v, 3, |a, b| b.cmp(a));
    /// assert_eq!(min, [1, -3, -5]);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn sort_by<T>(v: &mut [T], n: usize, mut cmp: impl FnMut(&T, &T) -> Ordering) -> &mut [T] {
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

    /// Get the `n` largest items with a key extraction function.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5_i32, 4, 1, -3, 2];
    /// let max = out::slice::sort_by_key(&mut v, 3, |a| a.abs());
    /// assert_eq!(max, [-3, 4, -5]);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn sort_by_key<T, K: Ord>(v: &mut [T], n: usize, mut f: impl FnMut(&T) -> K) -> &mut [T] {
        sort_by(v, n, |a, b| f(a).cmp(&f(b)))
    }

    /// Get the `n` largest items with a key extraction function.
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
    /// let max = out::slice::sort_by_cached_key(&mut v, 3, |a| a.abs());
    /// assert_eq!(max, [-3, 4, -5]);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn sort_by_cached_key<T, K: Ord>(
        v: &mut [T],
        n: usize,
        f: impl FnMut(&T) -> K,
    ) -> &mut [T] {
        // Implementation based on https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_cached_key.
        macro_rules! sort_by_cached_key {
            ($t:ty) => {{
                // All elements are unique since they contain the index, so we can use the unstable version.
                let iter = v.iter().map(f).enumerate().map(|(i, k)| (k, i as $t));
                let mut sorted = crate::iter::sort_unstable(iter, n);
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
            sort_by_cached_key!(u8)
        } else if sz_u16 < sz_u32 && v.len() <= u16::max_value() as usize {
            sort_by_cached_key!(u16)
        } else if sz_u32 < sz_usize && v.len() <= u32::max_value() as usize {
            sort_by_cached_key!(u32)
        } else {
            sort_by_cached_key!(usize)
        }
    }

    /// Get the `n` largest items.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5, 4, 1, -3, 2];
    /// let max = out::slice::sort_unstable(&mut v, 3);
    /// assert_eq!(max, [1, 2, 4]);
    /// ```
    pub fn sort_unstable<T: Ord>(v: &mut [T], n: usize) -> &mut [T] {
        sort_unstable_by(v, n, T::cmp)
    }

    /// Get the `n` largest items with a comparator function.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort_by` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5, 4, 1, -3, 2];
    /// let min = out::slice::sort_unstable_by(&mut v, 3, |a, b| b.cmp(a));
    /// assert_eq!(min, [1, -3, -5]);
    /// ```
    pub fn sort_unstable_by<T>(
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

    /// Get the `n` largest items with a key extraction function.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort_by_key` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let mut v = [-5_i32, 4, 1, -3, 2];
    /// let max = out::slice::sort_unstable_by_key(&mut v, 3, |a| a.abs());
    /// assert_eq!(max, [-3, 4, -5]);
    /// ```
    pub fn sort_unstable_by_key<T, K: Ord>(
        v: &mut [T],
        n: usize,
        mut f: impl FnMut(&T) -> K,
    ) -> &mut [T] {
        sort_unstable_by(v, n, |a, b| f(a).cmp(&f(b)))
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
#[cfg(feature = "alloc")]
pub mod iter {
    use alloc::vec::Vec;
    use core::cmp::Ordering;

    /// Get the `n` largest items from an iterator.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let max = out::iter::sort(-10..10, 3);
    /// assert_eq!(max, [7, 8, 9]);
    /// ```
    pub fn sort<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
        sort_by(iter, n, T::cmp)
    }

    /// Get the `n` largest items from an iterator with a comparator function.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let min = out::iter::sort_by(-10_i32..10, 3, |a, b| b.cmp(a));
    /// assert_eq!(min, [-8, -9, -10]);
    /// ```
    pub fn sort_by<T>(
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

    /// Get the `n` largest items from an iterator with a key extraction function.
    ///
    /// This function is stable, i.e. it preserves the order of equal elements.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let max = out::iter::sort_by_key(-10_i32..10, 3, |a| a.abs());
    /// assert_eq!(max, [-9, 9, -10]);
    /// ```
    pub fn sort_by_key<T, K: Ord>(
        iter: impl IntoIterator<Item = T>,
        n: usize,
        mut f: impl FnMut(&T) -> K,
    ) -> Vec<T> {
        sort_by(iter, n, |a, b| f(a).cmp(&f(b)))
    }

    /// Get the `n` largest items from an iterator.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort_from_iter` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let max = out::iter::sort_unstable(-10..10, 3);
    /// assert_eq!(max, [7, 8, 9]);
    /// ```
    pub fn sort_unstable<T: Ord>(iter: impl IntoIterator<Item = T>, n: usize) -> Vec<T> {
        sort_unstable_by(iter, n, T::cmp)
    }

    /// Get the `n` largest items from an iterator with a comparator function.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort_from_iter_by` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let min = out::iter::sort_unstable_by(-10..10, 3, |a, b| b.cmp(a));
    /// assert_eq!(min, [-8, -9, -10]);
    /// ```
    pub fn sort_unstable_by<T>(
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

    /// Get the `n` largest items from an iterator with a key extraction function.
    ///
    /// This function is not stable, i.e. it may not preserve the order of equal elements.
    /// This function should be faster than `sort_from_iter_by_key` in most cases.
    ///
    /// # Panics
    /// Panics if `n > len`.
    ///
    /// # Examples
    /// ```
    /// let max = out::iter::sort_unstable_by_key(-10_i32..10, 3, |a| a.abs());
    /// assert_eq!(max, [9, -9, -10]);
    /// ```
    pub fn sort_unstable_by_key<T, K: Ord>(
        iter: impl IntoIterator<Item = T>,
        n: usize,
        mut f: impl FnMut(&T) -> K,
    ) -> Vec<T> {
        sort_unstable_by(iter, n, |a, b| f(a).cmp(&f(b)))
    }
}
