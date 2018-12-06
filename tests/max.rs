#![feature(plugin)]
#![plugin(quickcheck_macros)]

use quickcheck::TestResult;

const N: usize = 3;

#[cfg(feature = "use_std")]
#[quickcheck]
fn max(mut v: Vec<(i32, i32)>) -> TestResult {
    if v.len() < N {
        return TestResult::discard();
    }
    let mut s = v.clone();
    s.sort_by(|(a, _), (b, _)| a.cmp(b));
    TestResult::from_bool(
        &mut s[v.len() - N..] == out::max_by(&mut v, N, |(a, _), (b, _)| a.cmp(b)),
    )
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
