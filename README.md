# out

[![Rust](https://github.com/evenorog/out/actions/workflows/rust.yml/badge.svg)](https://github.com/evenorog/out/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides fast min and max functionality for collections.

```rust
let mut v = [-5, 4, 1, -3, 2];
let max = out::slice::max(&mut v, 3);
assert_eq!(max, [1, 4, 2]);
assert_eq!(out::slice::min(max, 2), [2, 1]);
```

The order of the returned items is not guaranteed to be sorted.

This library can provide significant performance increase compared to sorting or
converting to a heap when `n` is small compared to the length of the slice or iterator.

## Benchmarks

*n = 100, len = 1_000_000:*

```
openSUSE Tumbleweed, i7-12700KF @ 3.61GHz, and 32GiB RAM:

test iter::max                ... bench:     623,477 ns/iter (+/- 49,526)
test iter::max_unstable       ... bench:     629,370 ns/iter (+/- 47,640)
test slice::max               ... bench:     490,442 ns/iter (+/- 31,446)
test slice::max_by_cached_key ... bench:   1,346,982 ns/iter (+/- 81,270)
test slice::max_unstable      ... bench:     487,957 ns/iter (+/- 37,561)
test std::binary_heap         ... bench:   3,520,525 ns/iter (+/- 152,789)
test std::sort                ... bench:  47,232,681 ns/iter (+/- 2,028,844)
test std::sort_by_cached_key  ... bench:  36,308,204 ns/iter (+/- 1,509,123)
test std::sort_unstable       ... bench:  18,652,609 ns/iter (+/- 935,364)
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
