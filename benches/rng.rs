#![feature(test)]

extern crate test;

use rand::prelude::*;

const N: usize = 1000;
const LEN: usize = 1_000_000;

fn rng_vec() -> Vec<i32> {
    let mut rng = SmallRng::seed_from_u64(0);
    let mut v: Vec<_> = (0..LEN as i32).collect();
    v.shuffle(&mut rng);
    v
}

mod slice {
    use crate::{rng_vec, N};

    #[bench]
    fn max(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            test::black_box(out::slice::max(&mut v, N));
        });
    }

    #[bench]
    fn min(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            test::black_box(out::slice::min(&mut v, N));
        });
    }

    #[bench]
    fn max_by_cached_key(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            test::black_box(out::slice::max_by_cached_key(&mut v, N, |&a| a));
        });
    }

    #[bench]
    fn min_by_cached_key(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            test::black_box(out::slice::min_by_cached_key(&mut v, N, |&a| a));
        });
    }
}

mod iter {
    use crate::{rng_vec, N};

    #[bench]
    fn max(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let v = v.clone();
            test::black_box(out::iter::max(v, N));
        });
    }

    #[bench]
    fn min(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let v = v.clone();
            test::black_box(out::iter::min(v, N));
        });
    }
}

mod std {
    use crate::{rng_vec, N};
    use std::collections::BinaryHeap;

    #[bench]
    fn sort(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            v.sort();
            test::black_box(&v[..N]);
        });
    }

    #[bench]
    fn sort_unstable(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            v.sort_unstable();
            test::black_box(&v[..N]);
        });
    }

    #[bench]
    fn sort_by_cached_key(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let mut v = v.clone();
            v.sort_by_cached_key(|&a| a);
            test::black_box(&v[..N]);
        });
    }

    #[bench]
    fn binary_heap(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let heap = BinaryHeap::from(v.clone());
            test::black_box(heap.into_iter().take(N).collect::<Vec<_>>());
        });
    }
}

mod itertools {
    use crate::{rng_vec, N};
    use itertools::Itertools;

    #[bench]
    fn k_smallest(b: &mut test::Bencher) {
        let v = rng_vec();
        b.iter(|| {
            let k_smallest = v.clone();
            test::black_box(k_smallest.into_iter().k_smallest(N));
        });
    }
}
