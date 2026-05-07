# out

[![Rust](https://github.com/evenorog/out/actions/workflows/rust.yml/badge.svg)](https://github.com/evenorog/out/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/out.svg)](https://crates.io/crates/out)
[![Docs](https://docs.rs/out/badge.svg)](https://docs.rs/out)

Provides fast min and max functionality for collections.

```rust
let mut v = [-5, 4, 1, -3, 2];
let max = out::slice::max(&mut v, 3);
assert_eq!(max, [4, 2, 1]);
assert_eq!(v, [4, 2, 1, -5, -3]);
```

This library can provide significant performance increase compared to sorting or
converting to a heap when `n` is small compared to the length of the slice or iterator.

## How It Works

The key idea: instead of fully sorting the collection, maintain a **fixed-size min-heap** of the `n` best candidates seen so far. Each new element costs at most one comparison to discard, or O(log n) to replace the current minimum. The collection is touched exactly once.

### The three phases

**Phase 1 — Build heap: O(n)**

Fill the heap with the first `n` elements. The smallest of the current candidates sits at the root.

```
Finding the 3 largest from: [3, 1, 7, 9, 2, 8, 4]

After phase 1 (heap of first 3 elements):

        ┌───┐
        │ 1 │  ← current minimum (root)
       ╱     ╲
    ┌───┐   ┌───┐
    │ 3 │   │ 7 │
    └───┘   └───┘
```

**Phase 2 — Scan remaining elements: O((len − n) · log n)**

For each remaining element: if it is smaller than the root, discard it with a single comparison. If larger, evict the root and sift the new element to its correct heap position in O(log n).

```
  next = 9  →  9 > 1, evict 1, sift 9 down

        ┌───┐
        │ 3 │
       ╱     ╲
    ┌───┐   ┌───┐
    │ 9 │   │ 7 │
    └───┘   └───┘

  next = 2  →  2 < 3, discard (one comparison, no further work)

  next = 8  →  8 > 3, evict 3, sift 8 down

        ┌───┐
        │ 7 │
       ╱     ╲
    ┌───┐   ┌───┐
    │ 9 │   │ 8 │
    └───┘   └───┘

  next = 4  →  4 < 7, discard
```

**Phase 3 — Sort the heap: O(n · log n)**

Heap-sort the `n` winners in-place and return them as a sorted slice — no extra allocation needed.

```
  Result: [9, 8, 7]
```

### Complexity comparison

|                  | `out`             | `sort_unstable`      | `BinaryHeap`           |
|------------------|-------------------|----------------------|------------------------|
| **Time**         | O(len · log n)    | O(len · log len)     | O(len + n · log len)   |
| **Extra space**  | O(1)              | O(log len) stack     | O(len)                 |

The advantage comes entirely from **log n ≪ log len** when `n` is small. `BinaryHeap` allocates the full collection and has a larger constant due to max-heap ordering needing to be inverted for a min query.

### Approximate speedup vs. `sort_unstable`

For a shuffled `Vec<i32>` of 1 000 000 elements (theoretical, based on comparison counts):

```
 n        log₂ n   comparisons (out)   comparisons (sort)   speedup
──────────────────────────────────────────────────────────────────────
       1     0.0        ~1 000 000          ~20 000 000        ~20×
      10     3.3        ~3 300 000          ~20 000 000         ~6×
     100     6.6        ~6 600 000          ~20 000 000         ~3×
   1 000    10.0       ~10 000 000          ~20 000 000         ~2×
  10 000    13.3       ~13 300 000          ~20 000 000       ~1.5×
 100 000    16.6       ~16 600 000          ~20 000 000       ~1.2×
```

The smaller `n` is relative to `len`, the larger the gain. When `n ≥ len` the library automatically falls back to `sort_unstable`, so there is no penalty for calling it unconditionally.

### License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
