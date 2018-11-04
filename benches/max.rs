#![feature(test)]

extern crate out;
extern crate rand;
extern crate test;

use rand::prelude::*;

const N: usize = 100;
const LEN: usize = 1_000_000;
const RANGE: i32 = 1_000_000;

#[bench]
fn max(b: &mut test::Bencher) {
    b.iter(|| {
        let mut rng = thread_rng();
        let mut v = Vec::with_capacity(LEN);
        for _ in 0..LEN {
            v.push(rng.gen_range(-RANGE, RANGE));
        }
        test::black_box(out::max(&mut v, N));
    });
}

#[bench]
fn max_unstable(b: &mut test::Bencher) {
    b.iter(|| {
        let mut rng = thread_rng();
        let mut v = Vec::with_capacity(LEN);
        for _ in 0..LEN {
            v.push(rng.gen_range(-RANGE, RANGE));
        }
        test::black_box(out::max_unstable(&mut v, N));
    });
}

#[bench]
fn sort(b: &mut test::Bencher) {
    b.iter(|| {
        let mut rng = thread_rng();
        let mut v = Vec::with_capacity(LEN);
        for _ in 0..LEN {
            v.push(rng.gen_range(-RANGE, RANGE));
        }
        v.sort();
        test::black_box(&v[..N]);
    });
}

#[bench]
fn sort_unstable(b: &mut test::Bencher) {
    b.iter(|| {
        let mut rng = thread_rng();
        let mut v = Vec::with_capacity(LEN);
        for _ in 0..LEN {
            v.push(rng.gen_range(-RANGE, RANGE));
        }
        v.sort_unstable();
        test::black_box(&v[..N]);
    });
}
