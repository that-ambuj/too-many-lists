# Too Many Linked Lists

Written in Rust&reg;

Linked Lists are a data structure that are known to be memory inefficient, unweildy(in implementation)
and impractical outside of a CS classroom but they are great for learning low-level stuff like how to manage pointers
, stack borrows, data models and how to implement your own data structures. This repo is an example of such challenges and how
we use unsafe Rust to implement stdlib's `LinkedList` from zero to production quality level.

Inspired by the infamous book [Too Many Lists](https://rust-unofficial.github.io/too-many-lists/index.html).

## Testing

Make sure that you have [rustup](https://rustup.rs) installed.

```bash
cargo test
```

To test unsafe code install the nightly toolchain with `miri`.

```bash
cargo +nightly install miri
cargo +nightly miri test
```
