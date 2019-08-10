#![feature(test)]

extern crate test;

use rand::prelude::*;
use std::collections::BinaryHeap;

const N: usize = 100;
const LEN: usize = 1_000_000;

fn create_random_vec() -> Vec<i32> {
    let mut rng = SmallRng::seed_from_u64(0);
    let mut v: Vec<_> = (0..LEN as i32).collect();
    v.shuffle(&mut rng);
    v
}

#[bench]
fn max(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        test::black_box(out::max(&mut v, N));
    });
}

#[bench]
fn max_unstable(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        test::black_box(out::max_unstable(&mut v, N));
    });
}

#[bench]
fn max_by_cached_key(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        test::black_box(out::max_by_cached_key(&mut v, N, |&a| a));
    });
}

#[bench]
fn sort(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        v.sort();
        test::black_box(&v[..N]);
    });
}

#[bench]
fn sort_unstable(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        v.sort_unstable();
        test::black_box(&v[..N]);
    });
}

#[bench]
fn sort_by_cached_key(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let mut v = v.clone();
        v.sort_by_cached_key(|&a| a);
        test::black_box(&v[..N]);
    });
}

#[bench]
fn binary_heap(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let heap = BinaryHeap::from(v.clone());
        test::black_box(heap.into_iter().take(N).collect::<Vec<_>>());
    });
}
