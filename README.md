# out
[![Travis](https://travis-ci.org/evenorog/out.svg?branch=master)](https://travis-ci.org/evenorog/out)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides functionality to get `n` items from a `&mut [T]`.

This library can provide significant performance increase compared to sorting or 
converting to a heap when `n` is relatively small.

```
N = 100, LEN = 1_000_000, RANGE = 1_000_000:
test binary_heap   ... bench:   6,832,200 ns/iter (+/- 41,693)
test max           ... bench:     993,996 ns/iter (+/- 20,123)
test max_unstable  ... bench:     992,648 ns/iter (+/- 26,116)
test sort          ... bench:  60,826,874 ns/iter (+/- 2,721,114)
test sort_unstable ... bench:  29,974,802 ns/iter (+/- 203,214)
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
