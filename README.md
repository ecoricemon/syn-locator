# syn-locator

syn-locator helps you to find source code locations of
[syn](https://crates.io/crates/syn) nodes.

## When to use

If you read a rust file then parse the read string through the `syn::parse_str`,
you will lose span information. This crate finds source code locations of syntax
tree nodes by simple string comparison.

## Example

```rust
use syn_locator::*;

// Assumes that we read this code from a file.
let file_path = "/path/to/file.rs";
let code = "
    struct Foo {
        a: i32,
    }
";
let syn = syn::parse_str::<syn::File>(code).unwrap();

// Finds location of the syntax tree.
let syn = std::pin::Pin::new(&syn);
syn.locate_as_entry(file_path, code);

// Picks a syntax tree node.
let item_struct = match &syn.items[0] {
    syn::Item::Struct(item_struct) => item_struct,
    _ => unreachable!()
};
let field_ty = &item_struct.fields.iter().next().unwrap().ty;

// Let's find out 'i32' from the syntax tree node.
assert_eq!(field_ty.location_message(), "/path/to/file.rs:3: i32");
assert!(matches!(field_ty.location(), Location {
    start: 29, // Byte offset
    end: 32,
    ..
}));
```
