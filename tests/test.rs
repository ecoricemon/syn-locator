use pretty_assertions::assert_eq;
use std::{
    pin::Pin,
    sync::atomic::{AtomicU32, Ordering},
};
use syn_locator::*;

fn unique_name() -> String {
    static NUM: AtomicU32 = AtomicU32::new(0);
    let num = NUM.fetch_add(1, Ordering::Relaxed);
    num.to_string()
}

#[test]
fn test_locate() {
    test_item_fn();
    test_item_struct();
    test_item_macro();
    test_field_pat();
    test_field_value();
    test_generics();
}

fn test_item_fn() {
    let code = "
    pub(crate) fn foo(a: i32, b: f32) -> usize {
        12
    }";
    let syn = syn::parse_str::<syn::ItemFn>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    assert_eq!(syn.vis.code(), "pub(crate)");
    assert_eq!(syn.sig.code(), "fn foo(a: i32, b: f32) -> usize");
    assert_eq!(
        syn.block.code(),
        r"{
        12
    }"
    );
}

fn test_item_struct() {
    let code = "
    pub struct Foo<T: Bar> {
        a: T,
        b: i32,
    }";
    let syn = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    assert_eq!(syn.vis.code(), "pub");
    assert_eq!(syn.struct_token.code(), "struct");
    assert_eq!(syn.ident.code(), "Foo");
    assert_eq!(syn.generics.code(), "<T: Bar>");
    assert_eq!(
        syn.fields.code(),
        r"{
        a: T,
        b: i32,
    }"
    );
}

fn test_item_macro() {
    let code = "
    macro_rules! foo {
        ($id:ident) => { $id() };
    }";
    let syn = syn::parse_str::<syn::ItemMacro>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    assert_eq!(syn.ident.code(), "foo");
    assert_eq!(syn.mac.path.code(), "macro_rules");
    assert_eq!(syn.mac.bang_token.code(), "!");
    assert_eq!(
        syn.mac.delimiter.code(),
        r"{
        ($id:ident) => { $id() };
    }"
    );
}

fn test_field_pat() {
    let code = "
    let X {
        a,
        ref b,
        ref mut c,
        d: dd,
        e: ref ee,
        f: ref mut ff,
    } = x;
    ";
    let syn = syn::parse_str::<syn::Stmt>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    let local = match syn.get_ref() {
        syn::Stmt::Local(v) => v,
        _ => unreachable!(),
    };

    let pat_struct = match &local.pat {
        syn::Pat::Struct(v) => v,
        _ => unreachable!(),
    };

    // a,
    let mut i = 0;
    assert_eq!(pat_struct.fields[i].member.code(), "a");
    assert_eq!(pat_struct.fields[i].pat.code(), "a");
    i += 1;

    // ref b,
    assert_eq!(pat_struct.fields[i].member.code(), "b");
    assert_eq!(pat_struct.fields[i].pat.code(), "ref b");
    i += 1;

    // ref mut c,
    assert_eq!(pat_struct.fields[i].member.code(), "c");
    assert_eq!(pat_struct.fields[i].pat.code(), "ref mut c");
    i += 1;

    // d: dd,
    assert_eq!(pat_struct.fields[i].member.code(), "d");
    assert_eq!(pat_struct.fields[i].pat.code(), "dd");
    i += 1;

    // e: ref ee,
    assert_eq!(pat_struct.fields[i].member.code(), "e");
    assert_eq!(pat_struct.fields[i].pat.code(), "ref ee");
    i += 1;

    // f: ref mut ff,
    assert_eq!(pat_struct.fields[i].member.code(), "f");
    assert_eq!(pat_struct.fields[i].pat.code(), "ref mut ff");
}

fn test_field_value() {
    let code = "
    T {
        a,
        b: b,
        c: x + y,
    }
    ";
    let syn = syn::parse_str::<syn::ExprStruct>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    // a,
    let mut i = 0;
    assert_eq!(syn.fields[i].member.code(), "a");
    assert_eq!(syn.fields[i].expr.code(), "a");
    i += 1;

    // b: b,
    assert_eq!(syn.fields[i].member.code(), "b");
    assert_eq!(syn.fields[i].expr.code(), "b");
    i += 1;

    // c: x + y,
    assert_eq!(syn.fields[i].member.code(), "c");
    assert_eq!(syn.fields[i].expr.code(), "x + y");
}

fn test_generics() {
    let code = "
    // `syn::Generics` without where clause
    impl<T> S<T> {}

    // `syn::Generics` on `syn::ItemImpl` without trait
    impl<T: A> S<T> where T: B {}

    // `syn::Generics` on `syn::ItemImpl` with trait
    impl<T: A> Trait for S<T> where T: B {}

    // `syn::Generics` on `syn::Signature`
    fn f<T: A>() where T: B {}
    ";

    let syn = syn::parse_str::<syn::File>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    // impl<T> S<T> {}
    let mut i = 0;
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_impl.generics.code(), "<T>");
    i += 1;

    // impl<T: A> S<T> where T: B {}
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_impl.generics.code(), "<T: A> S<T> where T: B");
    assert_eq!(item_impl.generics.params.code(), "T: A");
    assert_eq!(item_impl.generics.where_clause.code(), "where T: B");
    i += 1;

    // impl<T: A> Trait for S<T> where T: B {}
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(
        item_impl.generics.code(),
        "<T: A> Trait for S<T> where T: B"
    );
    assert_eq!(item_impl.generics.params.code(), "T: A");
    assert_eq!(item_impl.generics.where_clause.code(), "where T: B");
    i += 1;

    // fn f<T: A>() where T: B {}
    let syn::Item::Fn(item_fn) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_fn.sig.generics.code(), "<T: A>() where T: B");
    assert_eq!(item_fn.sig.generics.params.code(), "T: A");
    assert_eq!(item_fn.sig.generics.where_clause.code(), "where T: B");
}

#[cfg(feature = "find")]
#[test]
fn test_find() {
    let code = "
    struct A {
        a: i32,
    }";
    let syn = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    let syn = Pin::new(&syn);
    syn.locate_as_entry(&unique_name(), code).unwrap();

    let field: &syn::Field = syn.find("a: i32").unwrap();
    assert_eq!(field.code(), "a: i32");
}
