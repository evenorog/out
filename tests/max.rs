#![feature(plugin)]
#![plugin(quickcheck_macros)]

extern crate out;
extern crate quickcheck;

use quickcheck::TestResult;

const N: usize = 3;

#[cfg(feature = "use_std")]
#[quickcheck]
fn max(mut v: Vec<i32>) -> TestResult {
    if v.len() < N {
        return TestResult::discard();
    }
    let mut s = v.clone();
    s.sort();
    TestResult::from_bool(&mut s[v.len() - N..] == out::max(&mut v, N))
}

#[quickcheck]
fn max_unstable(mut v: Vec<i32>) -> TestResult {
    if v.len() < N {
        return TestResult::discard();
    }
    let mut s = v.clone();
    s.sort_unstable();
    TestResult::from_bool(&mut s[v.len() - N..] == out::max_unstable(&mut v, N))
}
