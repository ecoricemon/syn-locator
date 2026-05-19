# syn-locator

[![Crates.io][crates-badge]][crates-url]
[![CI Status][ci-badge]][ci-url]
[![Codecov][codecov-badge]][codecov-url]

[crates-badge]: https://img.shields.io/crates/v/syn-locator.svg
[crates-url]: https://crates.io/crates/syn-locator
[ci-badge]: https://github.com/ecoricemon/syn-locator/actions/workflows/test.yml/badge.svg
[ci-url]: https://github.com/ecoricemon/syn-locator/actions/workflows/test.yml
[codecov-badge]: https://codecov.io/gh/ecoricemon/syn-locator/graph/badge.svg
[codecov-url]: https://app.codecov.io/gh/ecoricemon/syn-locator

syn-locator helps you find source code locations of
[syn](https://crates.io/crates/syn) nodes.

## When to use

If you read a Rust file and parse it with `syn::parse_str`,
you will lose span information. This crate finds source code locations of syntax
tree nodes by simple string comparison.

## Example

```rust
use syn_locator::*;

// Pretend this code was read from a file.
let file_path = "/path/to/file.rs";
let code = "
    struct Foo {
        a: i32,
    }
";
let syn = syn::parse_str::<syn::File>(code).unwrap();

// Locate the syntax tree.
let syn = std::pin::Pin::new(&syn);
syn.locate_as_entry(file_path, code).unwrap();

// Pick a syntax tree node.
let item_struct = match &syn.items[0] {
    syn::Item::Struct(item_struct) => item_struct,
    _ => unreachable!()
};
let field_ty = &item_struct.fields.iter().next().unwrap().ty;

// Find the location of `i32` from the syntax tree node.
assert_eq!(field_ty.location_message(), "/path/to/file.rs:3: i32");
assert!(matches!(field_ty.location(), Location {
    start: 29, // Byte offset.
    end: 32,
    ..
}));
```
