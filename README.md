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

`syn-locator` records source ranges for [`syn`](https://crates.io/crates/syn)
syntax nodes after parsing Rust source code.

This is useful when you parse a file with `syn::parse_str` or `syn::parse_file`
and later need to point diagnostics, logs, reviews, or generated messages back
to the original source text.

## Why

`syn` is excellent for parsing Rust syntax, but the syntax tree alone is not
always enough when you need user-facing locations. `syn-locator` walks a parsed
tree and reconstructs byte ranges by matching the tree's tokens against the
original source code.

Once a tree is located, you can ask any supported node for:

- its byte range in the original file
- the exact source text for that node
- a compact `path:line: source` message
- with the optional `find` feature, the first descendant node matching a type
  and source snippet

## Quick Start

```rust
use syn_locator::{locate, Locate, Location};

let path = "src/example.rs";
let code = "
struct User {
    id: u64,
}
";

let located = locate::<syn::File>(path, code).unwrap();

let syn::Item::Struct(item_struct) = &located.items[0] else {
    unreachable!()
};

let field = item_struct.fields.iter().next().unwrap();
let ty = &field.ty;

assert_eq!(located.code(ty), "u64");
assert_eq!(ty.code(located.locator()), "u64");
assert_eq!(located.location_message(ty), "src/example.rs:3: u64");

let Location { start, end } = located.location(ty);
assert_eq!(&code[start..end], "u64");
```

`Located<T>` dereferences to `T`, so you can navigate the syntax tree as if you
were holding the parsed `syn` node directly.

## Using an Already Parsed Tree

If you already have a parsed syntax tree, wrap it with `Located::new`:

```rust
use syn_locator::Located;

let code = "fn answer() -> u32 { 42 }";
let item = syn::parse_str::<syn::ItemFn>(code).unwrap();
let located = Located::new(item, "answer.rs", code).unwrap();

assert_eq!(located.code(&located.sig.ident), "answer");
assert_eq!(located.location_message(&located.sig.output), "answer.rs:1: -> u32");
```

`Located` owns both the syntax tree and its `Locator`. This matters because
locations are keyed by syntax-node address; keeping them together makes the
high-level API the safest way to use the crate.

## Finding Descendants

Enable the `find` feature when you want to search inside a located tree by node
type and source text.

```rust,ignore
use syn_locator::{Locate, Located};

let code = "fn push(values: Vec<u64>) {}";
let located = syn_locator::locate::<syn::ItemFn>("push.rs", code).unwrap();

let ty: &syn::Type = located.find("Vec<u64>").unwrap();

assert_eq!(located.code(ty), "Vec<u64>");
assert_eq!(ty.location_message(located.locator()), "push.rs:1: Vec<u64>");
```

`find` returns the first matching descendant of the requested Rust type whose
located source text exactly equals the snippet you pass in.

## API Overview

- `locate::<T>(path, code)` parses `code` as `T` and returns `Located<T>`.
- `Located::new(syntax, path, code)` records locations for an already parsed
  `syn` tree.
- `Located::syntax()` returns the parsed syntax tree.
- `Located::locator()` returns the `Locator` that stores the source and ranges.
- `Located::location(node)` returns a `Location { start, end }` byte range.
- `Located::code(node)` returns the exact original source text for a node.
- `Located::location_message(node)` returns `path:line: source`.
- `Locate` provides the same node-level methods when you have a `Locator`.
- `Find` and `Located::find` are available behind the `find` feature.

## What Is Supported

`syn-locator` implements `Locate` for the main `syn` syntax families, including
files, items, statements, expressions, patterns, types, generics, attributes,
paths, literals, fields, visibility nodes, punctuation, operators, and tokens.

In practice, the crate is aimed at source-analysis tools that parse a Rust file,
walk the `syn` tree, and need to report where a selected node came from.

## Behavior and Caveats

Locations are byte offsets into the original source string. They are not line or
column pairs; use `location_message` when a human-readable line number is enough.

The locator reconstructs positions by walking nodes in source order and matching
tokens in the original code. Comments are replaced with whitespace during token
matching so comments do not normally confuse token lookup.

Because this is reconstruction rather than compiler span data, the result is
best suited for parsed source files that still match the tree you are locating.
Do not mutate or move a syntax tree after recording locations in a separate
`Locator`; prefer `locate` or `Located::new` unless you specifically need the
low-level API.

Nested block comments are not fully handled by the comment-filtering regex.

## Testing

Run the default test suite:

```sh
cargo test
```

Run tests with descendant search enabled:

```sh
cargo test --features find
```

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE.txt](LICENSE-APACHE.txt))
- MIT license ([LICENSE-MIT.txt](LICENSE-MIT.txt))

at your option.
