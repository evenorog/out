# out
[![Travis](https://travis-ci.org/evenorog/out.svg?branch=master)](https://travis-ci.org/evenorog/out)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides functionality to get `n` items from a `&mut [T]`.

This library can provide significant performance increase compared to sorting the whole list
when `n` is relatively small.

```
N = 100, LEN = 1_000_000, RANGE = 1_000_000:
test max           ... bench:   5,483,288 ns/iter (+/- 231,299)
test max_unstable  ... bench:   5,462,940 ns/iter (+/- 139,545)
test sort          ... bench:  67,729,867 ns/iter (+/- 2,045,393)
test sort_unstable ... bench:  35,710,133 ns/iter (+/- 983,608)
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
    let max = out::max_unstable(&mut v, 3);
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
