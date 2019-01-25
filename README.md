<img src="https://raw.githubusercontent.com/evenorog/out/nightly/out.svg?sanitize=true" alt="out" width="100%">

[![Travis](https://travis-ci.org/evenorog/out.svg?branch=master)](https://travis-ci.org/evenorog/out)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides functionality to get the `n` largest items from a `&mut [T]`.

```rust
let mut v = [-5, 4, 1, -3, 2];
let max = out::max(&mut v, 3);
assert_eq!(max, [1, 2, 4]);
```

It's worth noting that the largest item will be the last item in the slice that is returned.
This library can provide significant performance increase compared to sorting or
converting to a heap when `n` is relatively small.
In addition, the unstable methods can be used without 
the standard library by disabling the default features.

n = `100`, len = `1_000_000`:
```
test binary_heap   ... bench:   6,599,355 ns/iter (+/- 84,674)
test max           ... bench:     669,726 ns/iter (+/- 13,595)
test max_unstable  ... bench:     635,435 ns/iter (+/- 9,683)
test sort          ... bench:  62,585,547 ns/iter (+/- 1,361,258)
test sort_unstable ... bench:  34,595,265 ns/iter (+/- 739,255)
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
