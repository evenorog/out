mod slice {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max(mut v: Vec<i32>, n: usize) -> TestResult {
        let len = v.len();
        if len < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort();
        let out = out::slice::max(&mut v, n);
        out.sort();
        TestResult::from_bool(&mut s[len - n..] == out)
    }

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max_by_cached_key(mut v: Vec<i32>, n: usize) -> TestResult {
        let len = v.len();
        if len < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_by_cached_key(|&a| a);
        let out = out::slice::max_by_cached_key(&mut v, n, |&a| a);
        out.sort();
        TestResult::from_bool(&mut s[len - n..] == out)
    }
}

#[cfg(feature = "alloc")]
mod iter {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn max(v: Vec<i32>, n: usize) -> TestResult {
        let len = v.len();
        if len < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort();
        let mut out = out::iter::max(v, n);
        out.sort();
        TestResult::from_bool(s[len - n..] == out)
    }
}
