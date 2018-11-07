# out
[![Travis](https://travis-ci.org/evenorog/out.svg?branch=master)](https://travis-ci.org/evenorog/out)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides functionality to get `n` items from a `&mut [T]`.

This library can provide significant performance increase compared to sorting or 
converting to a heap when `n` is relatively small.

```
N = 100, LEN = 1_000_000, RANGE = 1_000_000:
test binary_heap   ... bench:   6,706,060 ns/iter (+/- 102,080)
test max           ... bench:     846,891 ns/iter (+/- 19,960)
test max_unstable  ... bench:     844,215 ns/iter (+/- 18,365)
test sort          ... bench:  62,280,523 ns/iter (+/- 997,028)
test sort_unstable ... bench:  34,822,256 ns/iter (+/- 3,047,204)
```

## Examples

Add this to `Cargo.toml`:

```toml
[dependencies]
out = "0.5"
```

And this to `main.rs`:

```rust
extern crate out;

fn main() {
    let mut v = [-5, 4, 1, -3, 2];
    let max = out::max(&mut v, 3);
    assert_eq!(max, [1, 2, 4]);
}
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
