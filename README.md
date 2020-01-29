# out

[![Travis](https://travis-ci.com/evenorog/out.svg?branch=master)](https://travis-ci.com/evenorog/out)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides fast min and max functionality for collections.

```rust
let mut v = [-5, 4, 1, -3, 2];
let max = out::slice::max(&mut v, 3);
assert_eq!(max, [1, 2, 4]);
assert_eq!(out::slice::min(max, 2), [2, 1]);
```

This library can provide significant performance increase compared to sorting or
converting to a heap when `n` is small compared to the length of the slice or iterator.

## Benchmarks

*n = 100, len = 1_000_000:*

```
openSUSE Tumbleweed, i7-5820K @ 3.30GHz, and 16GiB RAM:

test iter::max                 ... bench:     918,253 ns/iter (+/- 99,863)
test iter::max_unstable        ... bench:     916,908 ns/iter (+/- 58,050)
test slice::max                ... bench:     698,643 ns/iter (+/- 46,373)
test slice::max_by_cached_key  ... bench:   1,516,099 ns/iter (+/- 37,853)
test slice::max_unstable       ... bench:     655,286 ns/iter (+/- 25,017)
test std::binary_heap          ... bench:   6,592,801 ns/iter (+/- 780,590)
test std::sort                 ... bench:  63,192,028 ns/iter (+/- 2,338,506)
test std::sort_by_cached_key   ... bench:  66,058,834 ns/iter (+/- 5,447,387)
test std::sort_unstable        ... bench:  30,953,024 ns/iter (+/- 1,141,696)
```

```
Windows 10 (msvc), i7-5820K @ 3.30GHz, and 16GiB RAM:

test iter::max                 ... bench:   2,650,615 ns/iter (+/- 1,427,458)
test iter::max_unstable        ... bench:   2,604,860 ns/iter (+/- 1,001,639)
test slice::max                ... bench:   2,353,487 ns/iter (+/- 1,140,791)
test slice::max_by_cached_key  ... bench:   3,317,930 ns/iter (+/- 1,115,283)
test slice::max_unstable       ... bench:   2,221,975 ns/iter (+/- 1,232,170)
test std::binary_heap          ... bench:   8,666,095 ns/iter (+/- 3,790,987)
test std::sort                 ... bench:  73,953,630 ns/iter (+/- 23,036,689)
test std::sort_by_cached_key   ... bench:  79,681,540 ns/iter (+/- 24,554,555)
test std::sort_unstable        ... bench:  35,327,180 ns/iter (+/- 8,306,700)
```

### License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
