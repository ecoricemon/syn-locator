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

fn get_init_expr_from_stmt(stmt: &syn::Stmt) -> &syn::Expr {
    if let syn::Stmt::Local(syn::Local {
        init: Some(init), ..
    }) = stmt
    {
        &init.expr
    } else {
        panic!()
    }
}

fn get_type_from_const(item_const: &syn::ItemConst) -> &syn::Type {
    &item_const.ty
}

fn get_pat_from_stmt(stmt: &syn::Stmt) -> &syn::Pat {
    if let syn::Stmt::Local(local) = stmt {
        &local.pat
    } else {
        panic!()
    }
}

fn test<T, F>(code: &str, f: F) -> Result<(), String>
where
    T: syn::parse::Parse + Locate,
    F: FnOnce(&T),
{
    enable_thread_local(true);

    let syn = syn::parse_str::<T>(code).map_err(|e| e.to_string())?;
    let syn = unsafe { Pin::new_unchecked(&syn) };
    syn.locate_as_entry(&unique_name(), code)
        .map_err(|e| e.to_string())?;

    f(syn.get_ref());

    clear();
    Ok(())
}

#[cfg(feature = "find")]
fn test_find<A, D>(ancestor_code: &str, descendant_code: &str) -> Result<(), String>
where
    A: syn::parse::Parse + FindPtr + Locate,
    D: Locate,
{
    test(&ancestor_code, |ancestor: &A| {
        let found: &D = ancestor.find(descendant_code).unwrap();
        assert_eq!(found.code(), descendant_code);
    })
}

#[test]
fn test_locate_for_item() {
    // Item::Const
    let code = "const X: i32 = 42;";
    test(code, |item: &syn::Item| {
        let syn::Item::Const(item_const) = item else {
            panic!()
        };
        assert_eq!(item_const.code(), "const X: i32 = 42;");
        assert_eq!(item_const.ident.code(), "X");
    })
    .unwrap();

    // Item::Enum
    let code = "pub enum Foo { A, B(i32) }";
    test(code, |item: &syn::Item| {
        let syn::Item::Enum(item_enum) = item else {
            panic!()
        };
        assert_eq!(item_enum.code(), "pub enum Foo { A, B(i32) }");
        assert_eq!(item_enum.vis.code(), "pub");
        assert_eq!(item_enum.ident.code(), "Foo");
    })
    .unwrap();

    // Item::ExternCrate
    let code = "extern crate std;";
    test(code, |item: &syn::Item| {
        let syn::Item::ExternCrate(item_extern_crate) = item else {
            panic!()
        };
        assert_eq!(item_extern_crate.code(), "extern crate std;");
        assert_eq!(item_extern_crate.ident.code(), "std");
    })
    .unwrap();

    // Item::Fn
    let code = "fn foo(a: i32) -> bool { true }";
    test(code, |item: &syn::Item| {
        let syn::Item::Fn(item_fn) = item else {
            panic!()
        };
        assert_eq!(item_fn.code(), "fn foo(a: i32) -> bool { true }");
        assert_eq!(item_fn.sig.code(), "fn foo(a: i32) -> bool");
    })
    .unwrap();

    // Item::ForeignMod
    let code = "extern \"C\" { fn foo(); }";
    test(code, |item: &syn::Item| {
        let syn::Item::ForeignMod(item_foreign_mod) = item else {
            panic!()
        };
        assert_eq!(item_foreign_mod.code(), "extern \"C\" { fn foo(); }");
        assert_eq!(item_foreign_mod.abi.code(), "extern \"C\"");
    })
    .unwrap();

    // Item::Impl
    let code = "impl Foo { fn bar() {} }";
    test(code, |item: &syn::Item| {
        let syn::Item::Impl(item_impl) = item else {
            panic!()
        };
        assert_eq!(item_impl.code(), "impl Foo { fn bar() {} }");
        assert_eq!(item_impl.self_ty.code(), "Foo");
    })
    .unwrap();

    // Item::Macro
    let code = "macro_rules! foo { () => {} }";
    test(code, |item: &syn::Item| {
        let syn::Item::Macro(item_macro) = item else {
            panic!()
        };
        assert_eq!(item_macro.code(), "macro_rules! foo { () => {} }");
        assert_eq!(item_macro.ident.code(), "foo");
    })
    .unwrap();

    // Item::Mod
    let code = "mod foo { fn bar() {} }";
    test(code, |item: &syn::Item| {
        let syn::Item::Mod(item_mod) = item else {
            panic!()
        };
        assert_eq!(item_mod.code(), "mod foo { fn bar() {} }");
        assert_eq!(item_mod.ident.code(), "foo");
    })
    .unwrap();

    // Item::Static
    let code = "static X: i32 = 0;";
    test(code, |item: &syn::Item| {
        let syn::Item::Static(item_static) = item else {
            panic!()
        };
        assert_eq!(item_static.code(), "static X: i32 = 0;");
        assert_eq!(item_static.ident.code(), "X");
    })
    .unwrap();

    // Item::Struct
    let code = "struct Foo { a: i32 }";
    test(code, |item: &syn::Item| {
        let syn::Item::Struct(item_st) = item else {
            panic!()
        };
        assert_eq!(item_st.code(), "struct Foo { a: i32 }");
        assert_eq!(item_st.ident.code(), "Foo");
    })
    .unwrap();

    // Item::Trait
    let code = "trait Foo { fn bar(); }";
    test(code, |item: &syn::Item| {
        let syn::Item::Trait(item_trait) = item else {
            panic!()
        };
        assert_eq!(item_trait.code(), "trait Foo { fn bar(); }");
        assert_eq!(item_trait.ident.code(), "Foo");
    })
    .unwrap();

    // Item::TraitAlias
    let code = "trait Foo = Bar + Baz;";
    test(code, |item: &syn::Item| {
        let syn::Item::TraitAlias(item_trait_alias) = item else {
            panic!()
        };
        assert_eq!(item_trait_alias.code(), "trait Foo = Bar + Baz;");
        assert_eq!(item_trait_alias.ident.code(), "Foo");
    })
    .unwrap();

    // Item::Type
    let code = "type Foo = Bar;";
    test(code, |item: &syn::Item| {
        let syn::Item::Type(item_ty) = item else {
            panic!()
        };
        assert_eq!(item_ty.code(), "type Foo = Bar;");
        assert_eq!(item_ty.ident.code(), "Foo");
    })
    .unwrap();

    // Item::Union
    let code = "union Foo { a: i32, b: f64 }";
    test(code, |item: &syn::Item| {
        let syn::Item::Union(item_union) = item else {
            panic!()
        };
        assert_eq!(item_union.code(), "union Foo { a: i32, b: f64 }");
        assert_eq!(item_union.ident.code(), "Foo");
    })
    .unwrap();

    // Item::Use
    let code = "use std::collections::HashMap;";
    test(code, |item: &syn::Item| {
        let syn::Item::Use(item_use) = item else {
            panic!()
        };
        assert_eq!(item_use.code(), "use std::collections::HashMap;");
    })
    .unwrap();
}

#[test]
fn test_locate_for_ops() {
    // Expr::Binary
    for op in [
        // Arithmetic
        "+", "-", "*", "/", "%", // Logical
        "&&", "||", // Bitwise
        "^", "&", "|", "<<", ">>", // Comparison
        "==", "<", "<=", "!=", ">=", ">", // Compound assignment
        "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "<<=", ">>=",
    ] {
        let code = format!("{{ a {op} b; }}");
        test(&code, |block: &syn::Block| {
            let syn::Stmt::Expr(syn::Expr::Binary(expr_bin), _) = &block.stmts[0] else {
                panic!("expected ExprBinary for op {op}")
            };
            assert_eq!(expr_bin.op.code(), op);
        })
        .unwrap();
    }

    // Expr::Unary
    for (op, code) in [
        ("*", "let a = *x;"),
        ("!", "let a = !x;"),
        ("-", "let a = -x;"),
    ] {
        test(code, |stmt: &syn::Stmt| {
            let syn::Expr::Unary(expr_unary) = get_init_expr_from_stmt(stmt) else {
                panic!("expected ExprUnary for op {op}")
            };
            assert_eq!(expr_unary.op.code(), op);
        })
        .unwrap();
    }
}

#[test]
fn test_locate_for_impl_item() {
    // ImplItem::Const
    let code = "impl Foo { const X: i32 = 42; }";
    test(code, |item_impl: &syn::ItemImpl| {
        let syn::ImplItem::Const(impl_const) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_const.code(), "const X: i32 = 42;");
        assert_eq!(impl_const.ident.code(), "X");
    })
    .unwrap();

    // ImplItem::Fn
    let code = "impl Foo { fn bar(&self) -> i32 { 0 } }";
    test(code, |item_impl: &syn::ItemImpl| {
        let syn::ImplItem::Fn(impl_fn) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_fn.code(), "fn bar(&self) -> i32 { 0 }");
        assert_eq!(impl_fn.sig.code(), "fn bar(&self) -> i32");
    })
    .unwrap();

    // ImplItem::Type
    let code = "impl Foo { type Bar = i32; }";
    test(code, |item_impl: &syn::ItemImpl| {
        let syn::ImplItem::Type(impl_type) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_type.code(), "type Bar = i32;");
        assert_eq!(impl_type.ident.code(), "Bar");
    })
    .unwrap();

    // ImplItem::Macro
    let code = "impl Foo { vec![1, 2, 3]; }";
    test(code, |item_impl: &syn::ItemImpl| {
        let syn::ImplItem::Macro(impl_macro) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_macro.code(), "vec![1, 2, 3];");
    })
    .unwrap();
}

#[test]
fn test_locate_for_foreign_item() {
    // ForeignItem::Fn
    let code = "extern \"C\" { fn foo(a: i32) -> i32; }";
    test(code, |item: &syn::ItemForeignMod| {
        let syn::ForeignItem::Fn(foreign_fn) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_fn.code(), "fn foo(a: i32) -> i32;");
        assert_eq!(foreign_fn.sig.code(), "fn foo(a: i32) -> i32");
    })
    .unwrap();

    // ForeignItem::Static
    let code = "extern \"C\" { static X: i32; }";
    test(code, |item: &syn::ItemForeignMod| {
        let syn::ForeignItem::Static(foreign_static) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_static.code(), "static X: i32;");
        assert_eq!(foreign_static.ident.code(), "X");
    })
    .unwrap();

    // ForeignItem::Type
    let code = "extern \"C\" { type Foo; }";
    test(code, |item: &syn::ItemForeignMod| {
        let syn::ForeignItem::Type(foreign_type) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_type.code(), "type Foo;");
        assert_eq!(foreign_type.ident.code(), "Foo");
    })
    .unwrap();

    // ForeignItem::Macro
    let code = "extern \"C\" { vec![1, 2, 3]; }";
    test(code, |item: &syn::ItemForeignMod| {
        let syn::ForeignItem::Macro(foreign_macro) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_macro.code(), "vec![1, 2, 3];");
    })
    .unwrap();
}

#[test]
fn test_locate_for_use_tree() {
    // UseTree::Path
    let code = "use std::collections::HashMap;";
    test(code, |item: &syn::ItemUse| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        assert_eq!(use_path.code(), "std::collections::HashMap");
        assert_eq!(use_path.ident.code(), "std");
    })
    .unwrap();

    // UseTree::Name
    let code = "use std;";
    test(code, |item: &syn::ItemUse| {
        let syn::UseTree::Name(use_name) = &item.tree else {
            panic!()
        };
        assert_eq!(use_name.code(), "std");
    })
    .unwrap();

    // UseTree::Rename
    let code = "use std as stdlib;";
    test(code, |item: &syn::ItemUse| {
        let syn::UseTree::Rename(use_rename) = &item.tree else {
            panic!()
        };
        assert_eq!(use_rename.code(), "std as stdlib");
    })
    .unwrap();

    // UseTree::Glob
    let code = "use std::*;";
    test(code, |item: &syn::ItemUse| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        let syn::UseTree::Glob(use_glob) = &*use_path.tree else {
            panic!()
        };
        assert_eq!(use_glob.code(), "*");
    })
    .unwrap();

    // UseTree::Group
    let code = "use std::{io, fmt};";
    test(code, |item: &syn::ItemUse| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        let syn::UseTree::Group(use_group) = &*use_path.tree else {
            panic!()
        };
        assert_eq!(use_group.code(), "{io, fmt}");
    })
    .unwrap();
}

#[test]
fn test_locate_for_type() {
    // Type::Array
    let code = "const X: [i32; 3] = [0; 3];";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Array(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "[i32; 3]");
    })
    .unwrap();

    // Type::BareFn
    let code = "const X: fn(i32) -> bool = f;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::BareFn(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "fn(i32) -> bool");
    })
    .unwrap();

    // Type::ImplTrait
    let code = "fn foo() -> impl Clone {}";
    test(code, |item: &syn::ItemFn| {
        let syn::ReturnType::Type(_, ty) = &item.sig.output else {
            panic!()
        };
        let syn::Type::ImplTrait(ty) = ty.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(), "impl Clone");
    })
    .unwrap();

    // Type::Infer
    let code = "const X: _ = 0;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Infer(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "_");
    })
    .unwrap();

    // Type::Macro
    let code = "const X: env!(\"T\") = 0;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Macro(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "env!(\"T\")");
    })
    .unwrap();

    // Type::Never
    let code = "const X: ! = panic!();";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Never(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "!");
    })
    .unwrap();

    // Type::Paren
    let code = "const X: (i32) = 0;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Paren(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "(i32)");
    })
    .unwrap();

    // Type::Path
    let code = "const X: std::vec::Vec<i32> = v;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Path(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "std::vec::Vec<i32>");
    })
    .unwrap();

    // Type::Ptr
    let code = "const X: *const i32 = p;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Ptr(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "*const i32");
    })
    .unwrap();

    // Type::Reference
    let code = "const X: &'static mut i32 = r;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Reference(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "&'static mut i32");
    })
    .unwrap();

    // Type::Slice
    let code = "const X: &[i32] = s;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Reference(ty_ref) = get_type_from_const(item) else {
            panic!()
        };
        let syn::Type::Slice(ty) = ty_ref.elem.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(), "[i32]");
    })
    .unwrap();

    // Type::TraitObject
    let code = "const X: &dyn Clone = r;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Reference(ty_ref) = get_type_from_const(item) else {
            panic!()
        };
        let syn::Type::TraitObject(ty) = ty_ref.elem.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(), "dyn Clone");
    })
    .unwrap();

    // Type::Tuple
    let code = "const X: (i32, bool) = t;";
    test(code, |item: &syn::ItemConst| {
        let syn::Type::Tuple(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(), "(i32, bool)");
    })
    .unwrap();
}

#[test]
fn test_locate_for_pat() {
    // Pat::Const
    let code = "let const { true } = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Const(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "const { true }");
    })
    .unwrap();

    // Pat::Ident
    let code = "let mut a = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Ident(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "mut a");
    })
    .unwrap();

    // Pat::Lit
    let code = "let 42 = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Lit(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "42");
    })
    .unwrap();

    // Pat::Macro
    let code = "let mac!() = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Macro(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "mac!()");
    })
    .unwrap();

    // Pat::Or
    let code = "match x { A | B => {} _ => {} }";
    test(code, |expr_match: &syn::ExprMatch| {
        let syn::Pat::Or(pat_or) = &expr_match.arms[0].pat else {
            panic!()
        };
        assert_eq!(pat_or.code(), "A | B");
    })
    .unwrap();

    // Pat::Paren
    let code = "let (a) = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Paren(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "(a)");
    })
    .unwrap();

    // Pat::Path
    let code = "if let a::B = x {}";
    test(code, |expr: &syn::Expr| {
        let syn::Expr::If(syn::ExprIf { cond, .. }) = expr else {
            panic!()
        };
        let syn::Expr::Let(expr_let) = &**cond else {
            panic!()
        };
        let syn::Pat::Path(pat_path) = &*expr_let.pat else {
            panic!()
        };
        assert_eq!(pat_path.code(), "a::B");
    })
    .unwrap();

    // Pat::Range
    let code = "let 1..=10 = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Range(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "1..=10");
    })
    .unwrap();

    // Pat::Reference
    let code = "let &a = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Reference(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "&a");
    })
    .unwrap();

    // Pat::Rest
    let code = "let (a, ..) = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Tuple(pat_tuple) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        let syn::Pat::Rest(pat) = &pat_tuple.elems[1] else {
            panic!()
        };
        assert_eq!(pat.code(), "..");
    })
    .unwrap();

    // Pat::Slice
    let code = "let [a, b] = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Slice(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "[a, b]");
    })
    .unwrap();

    // Pat::Struct
    let code = "let Foo { a, b } = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Struct(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "Foo { a, b }");
    })
    .unwrap();

    // Pat::Tuple
    let code = "let (a, b) = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Tuple(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "(a, b)");
    })
    .unwrap();

    // Pat::TupleStruct
    let code = "let Some(a) = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::TupleStruct(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "Some(a)");
    })
    .unwrap();

    // Pat::Type
    let code = "fn foo(a: i32) {}";
    test(code, |item: &syn::ItemFn| {
        let syn::FnArg::Typed(pat_type) = &item.sig.inputs[0] else {
            panic!()
        };
        assert_eq!(pat_type.code(), "a: i32");
    })
    .unwrap();

    // Pat::Wild
    let code = "let _ = x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Pat::Wild(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(), "_");
    })
    .unwrap();
}

#[test]
fn test_locate_for_attribute() {
    // Meta::Path
    let code = "#[test] fn foo() {}";
    test(code, |item: &syn::ItemFn| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(), "#[test]");
        let syn::Meta::Path(meta_path) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_path.code(), "test");
    })
    .unwrap();

    // Meta::List
    let code = "#[derive(Clone, Debug)] struct Foo;";
    test(code, |item: &syn::ItemStruct| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(), "#[derive(Clone, Debug)]");
        let syn::Meta::List(meta_list) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_list.code(), "derive(Clone, Debug)");
    })
    .unwrap();

    // Meta::NameValue
    let code = "#[path = \"foo.rs\"] mod foo {}";
    test(code, |item: &syn::ItemMod| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(), "#[path = \"foo.rs\"]");
        let syn::Meta::NameValue(meta_nv) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_nv.code(), "path = \"foo.rs\"");
    })
    .unwrap();

    // Attr inner
    let code = "#![allow(unused)] fn foo() {}";
    test(code, |file: &syn::File| {
        let attr = &file.attrs[0];
        assert_eq!(attr.code(), "#![allow(unused)]");
    })
    .unwrap();
}

#[test]
fn test_locate_for_lit() {
    for (expected, code) in [
        // Str
        ("\"hello\"", "let a = \"hello\";"),
        // ByteStr
        ("b\"hello\"", "let a = b\"hello\";"),
        // CStr
        ("c\"hello\"", "let a = c\"hello\";"),
        // Byte
        ("b'x'", "let a = b'x';"),
        // Char
        ("'x'", "let a = 'x';"),
        // Int
        ("42", "let a = 42;"),
        // Float
        ("3.14", "let a = 3.14;"),
        // Bool
        ("true", "let a = true;"),
    ] {
        test(code, |stmt: &syn::Stmt| {
            let syn::Expr::Lit(expr_lit) = get_init_expr_from_stmt(stmt) else {
                panic!("expected ExprLit for {expected}")
            };
            assert_eq!(expr_lit.lit.code(), expected);
        })
        .unwrap();
    }
}

#[test]
fn test_locate_for_expr() {
    // Expr::Array
    let code = "let a = [1, 2];";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Array(expr_arr) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_arr.code(), "[1, 2]");
    })
    .unwrap();

    // Expr::Assign
    let code = "{ let mut a; a = 1; }";
    test(code, |block: &syn::Block| {
        let syn::Stmt::Expr(syn::Expr::Assign(expr_assign), _) = &block.stmts[1] else {
            panic!()
        };
        assert_eq!(expr_assign.code(), "a = 1");
    })
    .unwrap();

    // Expr::Async
    let code = "let a = async { 0 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Async(expr_async) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_async.code(), "async { 0 }");
    })
    .unwrap();

    // Expr::Await
    let code = "async fn foo() { let fut = async { 0 }; fut.await; }";
    test(code, |item_fn: &syn::ItemFn| {
        let syn::Stmt::Expr(syn::Expr::Await(expr_await), _) = &item_fn.block.stmts[1] else {
            panic!()
        };
        assert_eq!(expr_await.code(), "fut.await");
    })
    .unwrap();

    // Expr::Binary
    let code = "let a = 1 + 2;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Binary(expr_bin) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_bin.code(), "1 + 2");
    })
    .unwrap();

    // Expr::Block
    let code = "let a = { 1 + 2 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Block(expr_blk) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_blk.code(), "{ 1 + 2 }");
    })
    .unwrap();

    // Expr::Break
    let code = "'a: loop { break 'a; }";
    test(code, |expr_loop: &syn::ExprLoop| {
        let syn::Stmt::Expr(syn::Expr::Break(expr_break), _) = &expr_loop.body.stmts[0] else {
            panic!()
        };
        assert_eq!(expr_break.code(), "break 'a");
    })
    .unwrap();

    // Expr::Call
    let code = "{ fn foo() {} let a = foo(); }";
    test(code, |expr_blk: &syn::ExprBlock| {
        let syn::Expr::Call(expr_call) = get_init_expr_from_stmt(&expr_blk.block.stmts[1]) else {
            panic!()
        };
        assert_eq!(expr_call.code(), "foo()");
    })
    .unwrap();

    // Expr::Cast
    let code = "let a = 1 as f64;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Cast(expr_cast) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_cast.code(), "1 as f64");
    })
    .unwrap();

    // Expr::Closure
    let code = "let a = |i: i32| { i };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Closure(expr_closure) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_closure.code(), "|i: i32| { i }");
    })
    .unwrap();

    // Expr::Const
    let code = "const C: i32 = const { 1 + 2 };";
    test(code, |item_const: &syn::ItemConst| {
        let syn::Expr::Const(expr_const) = &*item_const.expr else {
            panic!()
        };
        assert_eq!(expr_const.code(), "const { 1 + 2 }");
    })
    .unwrap();

    // Expr::Continue
    let code = "'a: loop { continue 'a; }";
    test(code, |expr_loop: &syn::ExprLoop| {
        let syn::Stmt::Expr(syn::Expr::Continue(expr_continue), _) = &expr_loop.body.stmts[0]
        else {
            panic!()
        };
        assert_eq!(expr_continue.code(), "continue 'a");
    })
    .unwrap();

    // Expr::Field
    let code = "let a = x.field;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Field(expr_field) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_field.code(), "x.field");
    })
    .unwrap();

    // Expr::ForLoop
    let code = "for i in 0..10 { }";
    test(code, |expr: &syn::Expr| {
        let syn::Expr::ForLoop(expr_for) = expr else {
            panic!()
        };
        assert_eq!(expr_for.code(), "for i in 0..10 { }");
    })
    .unwrap();

    // Expr::If
    let code = "let a = if true { 1 } else { 2 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::If(expr_if) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_if.code(), "if true { 1 } else { 2 }");
    })
    .unwrap();

    // Expr::Index
    let code = "let a = arr[0];";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Index(expr_index) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_index.code(), "arr[0]");
    })
    .unwrap();

    // Expr::Infer
    let code = "let a = [0; _];";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Repeat(expr_repeat) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        let syn::Expr::Infer(expr_infer) = &*expr_repeat.len else {
            panic!()
        };
        assert_eq!(expr_infer.code(), "_");
    })
    .unwrap();

    // Expr::Let
    let code = "if let Some(x) = opt { }";
    test(code, |expr_if: &syn::ExprIf| {
        let syn::Expr::Let(expr_let) = &*expr_if.cond else {
            panic!()
        };
        assert_eq!(expr_let.code(), "let Some(x) = opt");
    })
    .unwrap();

    // Expr::Lit
    let code = "let a = 42;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Lit(expr_lit) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_lit.code(), "42");
    })
    .unwrap();

    // Expr::Loop
    let code = "loop { break; }";
    test(code, |expr: &syn::Expr| {
        let syn::Expr::Loop(expr_loop) = expr else {
            panic!()
        };
        assert_eq!(expr_loop.code(), "loop { break; }");
    })
    .unwrap();

    // Expr::Macro
    let code = "let a = vec![1, 2, 3];";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Macro(expr_macro) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_macro.code(), "vec![1, 2, 3]");
    })
    .unwrap();

    // Expr::Match
    let code = "let a = match x { _ => 1 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Match(expr_match) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_match.code(), "match x { _ => 1 }");
    })
    .unwrap();

    // Expr::MethodCall
    let code = "let a = x.foo(1);";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::MethodCall(expr_mc) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_mc.code(), "x.foo(1)");
    })
    .unwrap();

    // Expr::Paren
    let code = "let a = (1);";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Paren(expr_paren) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_paren.code(), "(1)");
    })
    .unwrap();

    // Expr::Path
    let code = "let a = std::mem::drop;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Path(expr_path) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_path.code(), "std::mem::drop");
    })
    .unwrap();

    // Expr::Range
    let code = "let a = 0..10;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Range(expr_range) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_range.code(), "0..10");
    })
    .unwrap();

    // Expr::RawAddr
    let code = "let a = &raw const x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::RawAddr(expr_raw) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_raw.code(), "&raw const x");
    })
    .unwrap();

    // Expr::Reference
    let code = "let a = &x;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Reference(expr_ref) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_ref.code(), "&x");
    })
    .unwrap();

    // Expr::Repeat
    let code = "let a = [0; 5];";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Repeat(expr_repeat) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_repeat.code(), "[0; 5]");
    })
    .unwrap();

    // Expr::Return
    let code = "fn foo() -> i32 { return 1; }";
    test(code, |item_fn: &syn::ItemFn| {
        let syn::Stmt::Expr(syn::Expr::Return(expr_return), _) = &item_fn.block.stmts[0] else {
            panic!()
        };
        assert_eq!(expr_return.code(), "return 1");
    })
    .unwrap();

    // Expr::Struct
    let code = "let a = Foo { x: 1, y: 2 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Struct(expr_struct) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_struct.code(), "Foo { x: 1, y: 2 }");
    })
    .unwrap();

    // Expr::Try
    let code = "let a = x()?;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Try(expr_try) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_try.code(), "x()?");
    })
    .unwrap();

    // Expr::TryBlock
    let code = "let a = try { 1 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::TryBlock(expr_try_block) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_try_block.code(), "try { 1 }");
    })
    .unwrap();

    // Expr::Tuple
    let code = "let a = (1, 2);";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Tuple(expr_tuple) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_tuple.code(), "(1, 2)");
    })
    .unwrap();

    // Expr::Unary
    let code = "let a = !true;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Unary(expr_unary) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_unary.code(), "!true");
    })
    .unwrap();

    // Expr::Unsafe
    let code = "let a = unsafe { 1 };";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Unsafe(expr_unsafe) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_unsafe.code(), "unsafe { 1 }");
    })
    .unwrap();

    // Expr::While
    let code = "while true { break; }";
    test(code, |expr: &syn::Expr| {
        let syn::Expr::While(expr_while) = expr else {
            panic!()
        };
        assert_eq!(expr_while.code(), "while true { break; }");
    })
    .unwrap();

    // Expr::Yield
    let code = "let a = yield 1;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Yield(expr_yield) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_yield.code(), "yield 1");
    })
    .unwrap();
}

#[test]
fn test_locate_etc() {
    test_locate_location();
    test_locate_for_captured_param();
    test_locate_for_bound_lifetimes();
    test_locate_for_field_pat();
    test_locate_for_field_value();
    test_locate_for_generics();
    test_locate_for_qself();
}

fn test_locate_location() {
    let code = "1 + 2";
    test(code, |bin: &syn::ExprBinary| {
        assert_eq!(bin.op.location().start, 2);
        assert_eq!(bin.op.location().end, 3);
        let msg = bin.op.location_message();
        let start = msg.find(':').unwrap();
        assert_eq!(&msg[start..], ":1: +"); // file_path:line_number: content
    })
    .unwrap();
}

fn test_locate_for_captured_param() {
    let code = "fn f<'a, T>() -> impl Trait + use<'a, T> {}";
    test(code, |item_fn: &syn::ItemFn| {
        let syn::ReturnType::Type(_, ty) = &item_fn.sig.output else {
            panic!()
        };
        let syn::Type::ImplTrait(ty_impl_trait) = &**ty else {
            panic!()
        };
        let syn::TypeParamBound::Trait(trait_bound) = &ty_impl_trait.bounds[0] else {
            panic!()
        };
        let syn::TypeParamBound::PreciseCapture(capture) = &ty_impl_trait.bounds[1] else {
            panic!()
        };
        assert_eq!(trait_bound.code(), "Trait");
        assert_eq!(capture.code(), "use<'a, T>");
        assert_eq!(capture.params[0].code(), "'a");
        assert_eq!(capture.params[1].code(), "T");
    })
    .unwrap();
}

fn test_locate_for_bound_lifetimes() {
    let code = "fn foo<F: for<'a> Fn(&'a i32)>() {}";
    test(code, |item_fn: &syn::ItemFn| {
        let syn::GenericParam::Type(ty_param) = &item_fn.sig.generics.params[0] else {
            panic!()
        };
        let syn::TypeParamBound::Trait(trait_bound) = &ty_param.bounds[0] else {
            panic!()
        };
        let bound_lifetimes = trait_bound.lifetimes.as_ref().unwrap();
        assert_eq!(bound_lifetimes.code(), "for<'a>");
    })
    .unwrap();
}

fn test_locate_for_field_pat() {
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

fn test_locate_for_field_value() {
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

fn test_locate_for_generics() {
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

fn test_locate_for_qself() {
    let code = "let f = <i32 as std::fmt::Display>::fmt;";
    test(code, |stmt: &syn::Stmt| {
        let syn::Expr::Path(expr_path) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        let qself = expr_path.qself.as_ref().unwrap();
        assert_eq!(qself.code(), "<i32 as std::fmt::Display>");
        assert_eq!(qself.ty.code(), "i32");
    })
    .unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_item() {
    let ancestor = "mod x { const X: i32 = 42; }";
    let descendant = "const X: i32 = 42;";
    test_find::<syn::File, syn::ItemConst>(ancestor, descendant).unwrap();

    let ancestor = "mod x { pub enum Foo { A, B(i32) } }";
    let descendant = "pub enum Foo { A, B(i32) }";
    test_find::<syn::File, syn::ItemEnum>(ancestor, descendant).unwrap();

    let ancestor = "mod x { extern crate foo; }";
    let descendant = "extern crate foo;";
    test_find::<syn::File, syn::ItemExternCrate>(ancestor, descendant).unwrap();

    let ancestor = "mod x { fn foo(a: i32) -> bool { true } }";
    let descendant = "fn foo(a: i32) -> bool { true }";
    test_find::<syn::File, syn::ItemFn>(ancestor, descendant).unwrap();

    let ancestor = "mod x { extern \"C\" { fn foo(); } }";
    let descendant = "extern \"C\" { fn foo(); }";
    test_find::<syn::File, syn::ItemForeignMod>(ancestor, descendant).unwrap();

    let ancestor = "mod x { impl Foo { fn bar() {} } }";
    let descendant = "impl Foo { fn bar() {} }";
    test_find::<syn::File, syn::ItemImpl>(ancestor, descendant).unwrap();

    let ancestor = "mod x { macro_rules! foo { () => {} } }";
    let descendant = "macro_rules! foo { () => {} }";
    test_find::<syn::File, syn::ItemMacro>(ancestor, descendant).unwrap();

    let ancestor = "mod x { mod foo { fn bar() {} } }";
    let descendant = "mod foo { fn bar() {} }";
    test_find::<syn::File, syn::ItemMod>(ancestor, descendant).unwrap();

    let ancestor = "mod x { static X: i32 = 0; }";
    let descendant = "static X: i32 = 0;";
    test_find::<syn::File, syn::ItemStatic>(ancestor, descendant).unwrap();

    let ancestor = "mod x { struct Foo { a: i32 } }";
    let descendant = "struct Foo { a: i32 }";
    test_find::<syn::File, syn::ItemStruct>(ancestor, descendant).unwrap();

    let ancestor = "mod x { trait Foo { fn bar(); } }";
    let descendant = "trait Foo { fn bar(); }";
    test_find::<syn::File, syn::ItemTrait>(ancestor, descendant).unwrap();

    let ancestor = "mod x { trait Foo = Bar + Baz; }";
    let descendant = "trait Foo = Bar + Baz;";
    test_find::<syn::File, syn::ItemTraitAlias>(ancestor, descendant).unwrap();

    let ancestor = "mod x { type Foo = Bar; }";
    let descendant = "type Foo = Bar;";
    test_find::<syn::File, syn::ItemType>(ancestor, descendant).unwrap();

    let ancestor = "mod x { union Foo { a: i32, b: f64 } }";
    let descendant = "union Foo { a: i32, b: f64 }";
    test_find::<syn::File, syn::ItemUnion>(ancestor, descendant).unwrap();

    let ancestor = "mod x { use std::collections::HashMap; }";
    let descendant = "use std::collections::HashMap;";
    test_find::<syn::File, syn::ItemUse>(ancestor, descendant).unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_ops() {
    test_find::<syn::Stmt, syn::Token![+]>("let a = x + y;", "+").unwrap();
    test_find::<syn::Stmt, syn::Token![-]>("let a = x - y;", "-").unwrap();
    test_find::<syn::Stmt, syn::Token![*]>("let a = x * y;", "*").unwrap();
    test_find::<syn::Stmt, syn::Token![/]>("let a = x / y;", "/").unwrap();
    test_find::<syn::Stmt, syn::Token![%]>("let a = x % y;", "%").unwrap();
    test_find::<syn::Stmt, syn::Token![&&]>("let a = x && y;", "&&").unwrap();
    test_find::<syn::Stmt, syn::Token![||]>("let a = x || y;", "||").unwrap();
    test_find::<syn::Stmt, syn::Token![^]>("let a = x ^ y;", "^").unwrap();
    test_find::<syn::Stmt, syn::Token![&]>("let a = x & y;", "&").unwrap();
    test_find::<syn::Stmt, syn::Token![|]>("let a = x | y;", "|").unwrap();
    test_find::<syn::Stmt, syn::Token![<<]>("let a = x << y;", "<<").unwrap();
    test_find::<syn::Stmt, syn::Token![>>]>("let a = x >> y;", ">>").unwrap();
    test_find::<syn::Stmt, syn::Token![==]>("let a = x == y;", "==").unwrap();
    test_find::<syn::Stmt, syn::Token![<]>("let a = x < y;", "<").unwrap();
    test_find::<syn::Stmt, syn::Token![<=]>("let a = x <= y;", "<=").unwrap();
    test_find::<syn::Stmt, syn::Token![!=]>("let a = x != y;", "!=").unwrap();
    test_find::<syn::Stmt, syn::Token![>=]>("let a = x >= y;", ">=").unwrap();
    test_find::<syn::Stmt, syn::Token![>]>("let a = x > y;", ">").unwrap();
    test_find::<syn::Stmt, syn::Token![+=]>("a += b;", "+=").unwrap();
    test_find::<syn::Stmt, syn::Token![-=]>("a -= b;", "-=").unwrap();
    test_find::<syn::Stmt, syn::Token![*=]>("a *= b;", "*=").unwrap();
    test_find::<syn::Stmt, syn::Token![/=]>("a /= b;", "/=").unwrap();
    test_find::<syn::Stmt, syn::Token![%=]>("a %= b;", "%=").unwrap();
    test_find::<syn::Stmt, syn::Token![^=]>("a ^= b;", "^=").unwrap();
    test_find::<syn::Stmt, syn::Token![&=]>("a &= b;", "&=").unwrap();
    test_find::<syn::Stmt, syn::Token![|=]>("a |= b;", "|=").unwrap();
    test_find::<syn::Stmt, syn::Token![<<=]>("a <<= b;", "<<=").unwrap();
    test_find::<syn::Stmt, syn::Token![>>=]>("a >>= b;", ">>=").unwrap();
    test_find::<syn::Stmt, syn::Token![*]>("let a = *x;", "*").unwrap();
    test_find::<syn::Stmt, syn::Token![!]>("let a = !x;", "!").unwrap();
    test_find::<syn::Stmt, syn::Token![-]>("let a = -x;", "-").unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_type() {
    let ancestor = "mod m { const X: [i32; 3] = [0; 3]; }";
    let descendant = "[i32; 3]";
    test_find::<syn::File, syn::TypeArray>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: fn(i32) -> bool = f; }";
    let descendant = "fn(i32) -> bool";
    test_find::<syn::File, syn::TypeBareFn>(ancestor, descendant).unwrap();

    let ancestor = "mod m { fn foo() -> impl Clone {} }";
    let descendant = "impl Clone";
    test_find::<syn::File, syn::TypeImplTrait>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: _ = 0; }";
    let descendant = "_";
    test_find::<syn::File, syn::TypeInfer>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: env!(\"T\") = 0; }";
    let descendant = "env!(\"T\")";
    test_find::<syn::File, syn::TypeMacro>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: ! = panic!(); }";
    let descendant = "!";
    test_find::<syn::File, syn::TypeNever>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: (i32) = 0; }";
    let descendant = "(i32)";
    test_find::<syn::File, syn::TypeParen>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: std::vec::Vec<i32> = v; }";
    let descendant = "std::vec::Vec<i32>";
    test_find::<syn::File, syn::TypePath>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: *const i32 = p; }";
    let descendant = "*const i32";
    test_find::<syn::File, syn::TypePtr>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: &'static mut i32 = r; }";
    let descendant = "&'static mut i32";
    test_find::<syn::File, syn::TypeReference>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: &[i32] = s; }";
    let descendant = "[i32]";
    test_find::<syn::File, syn::TypeSlice>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: &dyn Clone = r; }";
    let descendant = "dyn Clone";
    test_find::<syn::File, syn::TypeTraitObject>(ancestor, descendant).unwrap();

    let ancestor = "mod m { const X: (i32, bool) = t; }";
    let descendant = "(i32, bool)";
    test_find::<syn::File, syn::TypeTuple>(ancestor, descendant).unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_pat() {
    let ancestor = "fn f() { let const { true } = x; }";
    let descendant = "const { true }";
    test_find::<syn::ItemFn, syn::PatConst>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let mut a = x; }";
    let descendant = "mut a";
    test_find::<syn::ItemFn, syn::PatIdent>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let 42 = x; }";
    let descendant = "42";
    test_find::<syn::ItemFn, syn::PatLit>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let mac!() = x; }";
    let descendant = "mac!()";
    test_find::<syn::ItemFn, syn::PatMacro>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { match x { A | B => {} _ => {} } }";
    let descendant = "A | B";
    test_find::<syn::ItemFn, syn::PatOr>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let (a) = x; }";
    let descendant = "(a)";
    test_find::<syn::ItemFn, syn::PatParen>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { if let a::B = x {} }";
    let descendant = "a::B";
    test_find::<syn::ItemFn, syn::PatPath>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let 1..=10 = x; }";
    let descendant = "1..=10";
    test_find::<syn::ItemFn, syn::PatRange>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let &a = x; }";
    let descendant = "&a";
    test_find::<syn::ItemFn, syn::PatReference>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let (a, ..) = x; }";
    let descendant = "..";
    test_find::<syn::ItemFn, syn::PatRest>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let [a, b] = x; }";
    let descendant = "[a, b]";
    test_find::<syn::ItemFn, syn::PatSlice>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let Foo { a, b } = x; }";
    let descendant = "Foo { a, b }";
    test_find::<syn::ItemFn, syn::PatStruct>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let (a, b) = x; }";
    let descendant = "(a, b)";
    test_find::<syn::ItemFn, syn::PatTuple>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let Some(a) = x; }";
    let descendant = "Some(a)";
    test_find::<syn::ItemFn, syn::PatTupleStruct>(ancestor, descendant).unwrap();

    let ancestor = "fn foo(a: i32) { let b = 0; }";
    let descendant = "a: i32";
    test_find::<syn::ItemFn, syn::PatType>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let _ = x; }";
    let descendant = "_";
    test_find::<syn::ItemFn, syn::PatWild>(ancestor, descendant).unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_expr() {
    let ancestor = "fn f() { let a = [1, 2]; }";
    let descendant = "[1, 2]";
    test_find::<syn::ItemFn, syn::ExprArray>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let mut a = 0; a = 1; }";
    let descendant = "a = 1";
    test_find::<syn::ItemFn, syn::ExprAssign>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = async { 0 }; }";
    let descendant = "async { 0 }";
    test_find::<syn::ItemFn, syn::ExprAsync>(ancestor, descendant).unwrap();

    let ancestor = "async fn f() { let fut = async { 0 }; fut.await; }";
    let descendant = "fut.await";
    test_find::<syn::ItemFn, syn::ExprAwait>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = 1 + 2; }";
    let descendant = "1 + 2";
    test_find::<syn::ItemFn, syn::ExprBinary>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = { 1 + 2 }; }";
    let descendant = "{ 1 + 2 }";
    test_find::<syn::ItemFn, syn::ExprBlock>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { 'a: loop { break 'a; } }";
    let descendant = "break 'a";
    test_find::<syn::ItemFn, syn::ExprBreak>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { foo(); }";
    let descendant = "foo()";
    test_find::<syn::ItemFn, syn::ExprCall>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = 1 as f64; }";
    let descendant = "1 as f64";
    test_find::<syn::ItemFn, syn::ExprCast>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = |i: i32| { i }; }";
    let descendant = "|i: i32| { i }";
    test_find::<syn::ItemFn, syn::ExprClosure>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = const { 1 + 2 }; }";
    let descendant = "const { 1 + 2 }";
    test_find::<syn::ItemFn, syn::ExprConst>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { 'a: loop { continue 'a; } }";
    let descendant = "continue 'a";
    test_find::<syn::ItemFn, syn::ExprContinue>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = x.field; }";
    let descendant = "x.field";
    test_find::<syn::ItemFn, syn::ExprField>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { for i in 0..10 { } }";
    let descendant = "for i in 0..10 { }";
    test_find::<syn::ItemFn, syn::ExprForLoop>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = if true { 1 } else { 2 }; }";
    let descendant = "if true { 1 } else { 2 }";
    test_find::<syn::ItemFn, syn::ExprIf>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = arr[0]; }";
    let descendant = "arr[0]";
    test_find::<syn::ItemFn, syn::ExprIndex>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = [0; _]; }";
    let descendant = "_";
    test_find::<syn::ItemFn, syn::ExprInfer>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { if let Some(x) = opt { } }";
    let descendant = "let Some(x) = opt";
    test_find::<syn::ItemFn, syn::ExprLet>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = 42; }";
    let descendant = "42";
    test_find::<syn::ItemFn, syn::ExprLit>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { loop { break; } }";
    let descendant = "loop { break; }";
    test_find::<syn::ItemFn, syn::ExprLoop>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = vec![1, 2, 3]; }";
    let descendant = "vec![1, 2, 3]";
    test_find::<syn::ItemFn, syn::ExprMacro>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = match x { _ => 1 }; }";
    let descendant = "match x { _ => 1 }";
    test_find::<syn::ItemFn, syn::ExprMatch>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = x.foo(1); }";
    let descendant = "x.foo(1)";
    test_find::<syn::ItemFn, syn::ExprMethodCall>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = (1); }";
    let descendant = "(1)";
    test_find::<syn::ItemFn, syn::ExprParen>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = std::mem::drop; }";
    let descendant = "std::mem::drop";
    test_find::<syn::ItemFn, syn::ExprPath>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = 0..10; }";
    let descendant = "0..10";
    test_find::<syn::ItemFn, syn::ExprRange>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = &raw const x; }";
    let descendant = "&raw const x";
    test_find::<syn::ItemFn, syn::ExprRawAddr>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = &x; }";
    let descendant = "&x";
    test_find::<syn::ItemFn, syn::ExprReference>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = [0; 5]; }";
    let descendant = "[0; 5]";
    test_find::<syn::ItemFn, syn::ExprRepeat>(ancestor, descendant).unwrap();

    let ancestor = "fn f() -> i32 { return 1; }";
    let descendant = "return 1";
    test_find::<syn::ItemFn, syn::ExprReturn>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = Foo { x: 1, y: 2 }; }";
    let descendant = "Foo { x: 1, y: 2 }";
    test_find::<syn::ItemFn, syn::ExprStruct>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = x()?; }";
    let descendant = "x()?";
    test_find::<syn::ItemFn, syn::ExprTry>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = try { 1 }; }";
    let descendant = "try { 1 }";
    test_find::<syn::ItemFn, syn::ExprTryBlock>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = (1, 2); }";
    let descendant = "(1, 2)";
    test_find::<syn::ItemFn, syn::ExprTuple>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = !true; }";
    let descendant = "!true";
    test_find::<syn::ItemFn, syn::ExprUnary>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = unsafe { 1 }; }";
    let descendant = "unsafe { 1 }";
    test_find::<syn::ItemFn, syn::ExprUnsafe>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { while true { break; } }";
    let descendant = "while true { break; }";
    test_find::<syn::ItemFn, syn::ExprWhile>(ancestor, descendant).unwrap();

    let ancestor = "fn f() { let a = yield 1; }";
    let descendant = "yield 1";
    test_find::<syn::ItemFn, syn::ExprYield>(ancestor, descendant).unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_for_lit() {
    let ancestor = "let a = \"hello\";";
    let descendant = "\"hello\"";
    test_find::<syn::Stmt, syn::LitStr>(ancestor, descendant).unwrap();

    let ancestor = "let a = b\"hello\";";
    let descendant = "b\"hello\"";
    test_find::<syn::Stmt, syn::LitByteStr>(ancestor, descendant).unwrap();

    let ancestor = "let a = c\"hello\";";
    let descendant = "c\"hello\"";
    test_find::<syn::Stmt, syn::LitCStr>(ancestor, descendant).unwrap();

    let ancestor = "let a = b'x';";
    let descendant = "b'x'";
    test_find::<syn::Stmt, syn::LitByte>(ancestor, descendant).unwrap();

    let ancestor = "let a = 'x';";
    let descendant = "'x'";
    test_find::<syn::Stmt, syn::LitChar>(ancestor, descendant).unwrap();

    let ancestor = "let a = 42;";
    let descendant = "42";
    test_find::<syn::Stmt, syn::LitInt>(ancestor, descendant).unwrap();

    let ancestor = "let a = 3.14;";
    let descendant = "3.14";
    test_find::<syn::Stmt, syn::LitFloat>(ancestor, descendant).unwrap();

    let ancestor = "let a = true;";
    let descendant = "true";
    test_find::<syn::Stmt, syn::LitBool>(ancestor, descendant).unwrap();
}

#[cfg(feature = "find")]
#[test]
fn test_find_etc() {
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
