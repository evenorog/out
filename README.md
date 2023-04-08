# out

[![Rust](https://github.com/evenorog/out/actions/workflows/rust.yml/badge.svg)](https://github.com/evenorog/out/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides fast min and max functionality for collections.

```rust
let mut v = [-5, 4, 1, -3, 2];
let max = out::slice::max(&mut v, 3);
assert_eq!(max, [4, 2, 1]);
assert_eq!(out::slice::min(max, 2), [1, 2]);
```

This library can provide significant performance increase compared to sorting or
converting to a heap when `n` is small compared to the length of the slice or iterator.

### License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
