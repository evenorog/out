#![feature(test)]

extern crate out;
extern crate rand;
extern crate test;

use rand::prelude::*;
use std::collections::BinaryHeap;

const N: usize = 100;
const LEN: usize = 1_000_000;
const RANGE: i32 = 1_000_000;

fn create_random_vec() -> Vec<i32> {
    let mut rng = SmallRng::from_seed([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
    let mut v = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        v.push(rng.gen_range(-RANGE, RANGE));
    }
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
fn binary_heap(b: &mut test::Bencher) {
    let v = create_random_vec();
    b.iter(|| {
        let heap = BinaryHeap::from(v.clone());
        test::black_box(heap.into_iter().take(N).collect::<Vec<_>>());
    });
}
