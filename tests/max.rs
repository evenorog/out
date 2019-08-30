mod slice {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max(mut v: Vec<(i32, i32)>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_by(|(a, _), (b, _)| a.cmp(b));
        TestResult::from_bool(
            &mut s[v.len() - n..] == out::slice::max_by(&mut v, n, |(a, _), (b, _)| a.cmp(b)),
        )
    }

    #[quickcheck]
    fn max_unstable(mut v: Vec<i32>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_unstable();
        TestResult::from_bool(&mut s[v.len() - n..] == out::slice::max_unstable(&mut v, n))
    }

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max_by_cached_key(mut v: Vec<(i32, i32)>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_by_cached_key(|&(a, _)| a);
        TestResult::from_bool(
            &mut s[v.len() - n..] == out::slice::max_by_cached_key(&mut v, n, |&(a, _)| a),
        )
    }
}

mod iter {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max(v: Vec<(i32, i32)>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_by(|(a, _), (b, _)| a.cmp(b));
        TestResult::from_bool(
            s[v.len() - n..] == out::iter::max_by(v, n, |(a, _), (b, _)| a.cmp(b))[..],
        )
    }

    #[quickcheck]
    #[cfg(feature = "alloc")]
    fn max_unstable(v: Vec<i32>, n: usize) -> TestResult {
        if v.len() < n {
            return TestResult::discard();
        }
        let mut s = v.clone();
        s.sort_unstable();
        TestResult::from_bool(s[v.len() - n..] == out::iter::max_unstable(v, n)[..])
    }
}
