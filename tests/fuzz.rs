mod slice {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max(mut v: Vec<i32>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort();
        s.reverse();
        let out = out::slice::max(&mut v, n);
        TestResult::from_bool(&mut s[..n] == out)
    }

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max_by_cached_key(mut v: Vec<i32>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_by_cached_key(|&a| a);
        s.reverse();
        let out = out::slice::max_by_cached_key(&mut v, n, |&a| a);
        TestResult::from_bool(&mut s[..n] == out)
    }
}

#[cfg(feature = "alloc")]
mod iter {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn max(v: Vec<i32>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort();
        s.reverse();
        let out = out::iter::max(v, n);
        TestResult::from_bool(s[..n] == out)
    }
}
