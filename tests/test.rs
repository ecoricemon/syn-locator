use pretty_assertions::assert_eq;
use std::sync::atomic::{AtomicU32, Ordering};
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
    F: FnOnce(&T, &Locator),
{
    let located = locate::<T>(&unique_name(), code).map_err(|e| e.to_string())?;

    f(located.syntax(), located.locator());
    Ok(())
}

#[cfg(feature = "find")]
fn test_find<A, D>(ancestor_code: &str, descendant_code: &str) -> Result<(), String>
where
    A: syn::parse::Parse + FindPtr + Locate,
    D: Locate,
{
    test(ancestor_code, |ancestor: &A, locator| {
        let found: &D = ancestor
            .find(locator, descendant_code)
            .unwrap_or_else(|| panic!("failed to find `{descendant_code}` in `{ancestor_code}`"));
        assert_eq!(found.code(locator), descendant_code);
    })
}

#[test]
fn test_locate_for_item() {
    // Item::Const
    let code = "const X: i32 = 42;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Const(item_const) = item else {
            panic!()
        };
        assert_eq!(item_const.code(locator), "const X: i32 = 42;");
        assert_eq!(item_const.ident.code(locator), "X");
    })
    .unwrap();

    // Item::Enum
    let code = "pub enum Foo { A, B(i32) }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Enum(item_enum) = item else {
            panic!()
        };
        assert_eq!(item_enum.code(locator), "pub enum Foo { A, B(i32) }");
        assert_eq!(item_enum.vis.code(locator), "pub");
        assert_eq!(item_enum.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::ExternCrate
    let code = "extern crate std;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::ExternCrate(item_extern_crate) = item else {
            panic!()
        };
        assert_eq!(item_extern_crate.code(locator), "extern crate std;");
        assert_eq!(item_extern_crate.ident.code(locator), "std");
    })
    .unwrap();

    // Item::Fn
    let code = "fn foo(a: i32) -> bool { true }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Fn(item_fn) = item else {
            panic!()
        };
        assert_eq!(item_fn.code(locator), "fn foo(a: i32) -> bool { true }");
        assert_eq!(item_fn.sig.code(locator), "fn foo(a: i32) -> bool");
    })
    .unwrap();

    // Item::ForeignMod
    let code = "extern \"C\" { fn foo(); }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::ForeignMod(item_foreign_mod) = item else {
            panic!()
        };
        assert_eq!(item_foreign_mod.code(locator), "extern \"C\" { fn foo(); }");
        assert_eq!(item_foreign_mod.abi.code(locator), "extern \"C\"");
    })
    .unwrap();

    // Item::Impl
    let code = "impl Foo { fn bar() {} }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Impl(item_impl) = item else {
            panic!()
        };
        assert_eq!(item_impl.code(locator), "impl Foo { fn bar() {} }");
        assert_eq!(item_impl.self_ty.code(locator), "Foo");
    })
    .unwrap();

    // Item::Macro
    let code = "macro_rules! foo { () => {} }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Macro(item_macro) = item else {
            panic!()
        };
        assert_eq!(item_macro.code(locator), "macro_rules! foo { () => {} }");
        assert_eq!(item_macro.ident.code(locator), "foo");
    })
    .unwrap();

    // Item::Mod
    let code = "mod foo { fn bar() {} }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Mod(item_mod) = item else {
            panic!()
        };
        assert_eq!(item_mod.code(locator), "mod foo { fn bar() {} }");
        assert_eq!(item_mod.ident.code(locator), "foo");
    })
    .unwrap();

    // Item::Static
    let code = "static X: i32 = 0;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Static(item_static) = item else {
            panic!()
        };
        assert_eq!(item_static.code(locator), "static X: i32 = 0;");
        assert_eq!(item_static.ident.code(locator), "X");
    })
    .unwrap();

    // Item::Struct
    let code = "struct Foo { a: i32 }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Struct(item_st) = item else {
            panic!()
        };
        assert_eq!(item_st.code(locator), "struct Foo { a: i32 }");
        assert_eq!(item_st.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::Trait
    let code = "trait Foo { fn bar(); }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Trait(item_trait) = item else {
            panic!()
        };
        assert_eq!(item_trait.code(locator), "trait Foo { fn bar(); }");
        assert_eq!(item_trait.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::TraitAlias
    let code = "trait Foo = Bar + Baz;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::TraitAlias(item_trait_alias) = item else {
            panic!()
        };
        assert_eq!(item_trait_alias.code(locator), "trait Foo = Bar + Baz;");
        assert_eq!(item_trait_alias.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::Type
    let code = "type Foo = Bar;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Type(item_ty) = item else {
            panic!()
        };
        assert_eq!(item_ty.code(locator), "type Foo = Bar;");
        assert_eq!(item_ty.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::Union
    let code = "union Foo { a: i32, b: f64 }";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Union(item_union) = item else {
            panic!()
        };
        assert_eq!(item_union.code(locator), "union Foo { a: i32, b: f64 }");
        assert_eq!(item_union.ident.code(locator), "Foo");
    })
    .unwrap();

    // Item::Use
    let code = "use std::collections::HashMap;";
    test(code, |item: &syn::Item, locator| {
        let syn::Item::Use(item_use) = item else {
            panic!()
        };
        assert_eq!(item_use.code(locator), "use std::collections::HashMap;");
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
        test(&code, |block: &syn::Block, locator| {
            let syn::Stmt::Expr(syn::Expr::Binary(expr_bin), _) = &block.stmts[0] else {
                panic!("expected ExprBinary for op {op}")
            };
            assert_eq!(expr_bin.op.code(locator), op);
        })
        .unwrap();
    }

    // Expr::Unary
    for (op, code) in [
        ("*", "let a = *x;"),
        ("!", "let a = !x;"),
        ("-", "let a = -x;"),
    ] {
        test(code, |stmt: &syn::Stmt, locator| {
            let syn::Expr::Unary(expr_unary) = get_init_expr_from_stmt(stmt) else {
                panic!("expected ExprUnary for op {op}")
            };
            assert_eq!(expr_unary.op.code(locator), op);
        })
        .unwrap();
    }
}

#[test]
fn test_locate_for_impl_item() {
    // ImplItem::Const
    let code = "impl Foo { const X: i32 = 42; }";
    test(code, |item_impl: &syn::ItemImpl, locator| {
        let syn::ImplItem::Const(impl_const) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_const.code(locator), "const X: i32 = 42;");
        assert_eq!(impl_const.ident.code(locator), "X");
    })
    .unwrap();

    // ImplItem::Fn
    let code = "impl Foo { fn bar(&self) -> i32 { 0 } }";
    test(code, |item_impl: &syn::ItemImpl, locator| {
        let syn::ImplItem::Fn(impl_fn) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_fn.code(locator), "fn bar(&self) -> i32 { 0 }");
        assert_eq!(impl_fn.sig.code(locator), "fn bar(&self) -> i32");
    })
    .unwrap();

    // ImplItem::Type
    let code = "impl Foo { type Bar = i32; }";
    test(code, |item_impl: &syn::ItemImpl, locator| {
        let syn::ImplItem::Type(impl_type) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_type.code(locator), "type Bar = i32;");
        assert_eq!(impl_type.ident.code(locator), "Bar");
    })
    .unwrap();

    // ImplItem::Macro
    let code = "impl Foo { vec![1, 2, 3]; }";
    test(code, |item_impl: &syn::ItemImpl, locator| {
        let syn::ImplItem::Macro(impl_macro) = &item_impl.items[0] else {
            panic!()
        };
        assert_eq!(impl_macro.code(locator), "vec![1, 2, 3];");
    })
    .unwrap();
}

#[test]
fn test_locate_for_foreign_item() {
    // ForeignItem::Fn
    let code = "extern \"C\" { fn foo(a: i32) -> i32; }";
    test(code, |item: &syn::ItemForeignMod, locator| {
        let syn::ForeignItem::Fn(foreign_fn) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_fn.code(locator), "fn foo(a: i32) -> i32;");
        assert_eq!(foreign_fn.sig.code(locator), "fn foo(a: i32) -> i32");
    })
    .unwrap();

    // ForeignItem::Static
    let code = "extern \"C\" { static X: i32; }";
    test(code, |item: &syn::ItemForeignMod, locator| {
        let syn::ForeignItem::Static(foreign_static) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_static.code(locator), "static X: i32;");
        assert_eq!(foreign_static.ident.code(locator), "X");
    })
    .unwrap();

    // ForeignItem::Type
    let code = "extern \"C\" { type Foo; }";
    test(code, |item: &syn::ItemForeignMod, locator| {
        let syn::ForeignItem::Type(foreign_type) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_type.code(locator), "type Foo;");
        assert_eq!(foreign_type.ident.code(locator), "Foo");
    })
    .unwrap();

    // ForeignItem::Macro
    let code = "extern \"C\" { vec![1, 2, 3]; }";
    test(code, |item: &syn::ItemForeignMod, locator| {
        let syn::ForeignItem::Macro(foreign_macro) = &item.items[0] else {
            panic!()
        };
        assert_eq!(foreign_macro.code(locator), "vec![1, 2, 3];");
    })
    .unwrap();
}

#[test]
fn test_locate_for_use_tree() {
    // UseTree::Path
    let code = "use std::collections::HashMap;";
    test(code, |item: &syn::ItemUse, locator| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        assert_eq!(use_path.code(locator), "std::collections::HashMap");
        assert_eq!(use_path.ident.code(locator), "std");
    })
    .unwrap();

    // UseTree::Name
    let code = "use std;";
    test(code, |item: &syn::ItemUse, locator| {
        let syn::UseTree::Name(use_name) = &item.tree else {
            panic!()
        };
        assert_eq!(use_name.code(locator), "std");
    })
    .unwrap();

    // UseTree::Rename
    let code = "use std as stdlib;";
    test(code, |item: &syn::ItemUse, locator| {
        let syn::UseTree::Rename(use_rename) = &item.tree else {
            panic!()
        };
        assert_eq!(use_rename.code(locator), "std as stdlib");
    })
    .unwrap();

    // UseTree::Glob
    let code = "use std::*;";
    test(code, |item: &syn::ItemUse, locator| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        let syn::UseTree::Glob(use_glob) = &*use_path.tree else {
            panic!()
        };
        assert_eq!(use_glob.code(locator), "*");
    })
    .unwrap();

    // UseTree::Group
    let code = "use std::{io, fmt};";
    test(code, |item: &syn::ItemUse, locator| {
        let syn::UseTree::Path(use_path) = &item.tree else {
            panic!()
        };
        let syn::UseTree::Group(use_group) = &*use_path.tree else {
            panic!()
        };
        assert_eq!(use_group.code(locator), "{io, fmt}");
    })
    .unwrap();
}

#[test]
fn test_locate_for_type() {
    // Type::Array
    let code = "const X: [i32; 3] = [0; 3];";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Array(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "[i32; 3]");
    })
    .unwrap();

    // Type::BareFn
    let code = "const X: fn(i32) -> bool = f;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::BareFn(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "fn(i32) -> bool");
    })
    .unwrap();

    // Type::ImplTrait
    let code = "fn foo() -> impl Clone {}";
    test(code, |item: &syn::ItemFn, locator| {
        let syn::ReturnType::Type(_, ty) = &item.sig.output else {
            panic!()
        };
        let syn::Type::ImplTrait(ty) = ty.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(locator), "impl Clone");
    })
    .unwrap();

    // Type::Infer
    let code = "const X: _ = 0;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Infer(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "_");
    })
    .unwrap();

    // Type::Macro
    let code = "const X: env!(\"T\") = 0;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Macro(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "env!(\"T\")");
    })
    .unwrap();

    // Type::Never
    let code = "const X: ! = panic!();";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Never(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "!");
    })
    .unwrap();

    // Type::Paren
    let code = "const X: (i32) = 0;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Paren(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "(i32)");
    })
    .unwrap();

    // Type::Path
    let code = "const X: std::vec::Vec<i32> = v;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Path(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "std::vec::Vec<i32>");
    })
    .unwrap();

    // Type::Ptr
    let code = "const X: *const i32 = p;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Ptr(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "*const i32");
    })
    .unwrap();

    // Type::Reference
    let code = "const X: &'static mut i32 = r;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Reference(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "&'static mut i32");
    })
    .unwrap();

    // Type::Slice
    let code = "const X: &[i32] = s;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Reference(ty_ref) = get_type_from_const(item) else {
            panic!()
        };
        let syn::Type::Slice(ty) = ty_ref.elem.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(locator), "[i32]");
    })
    .unwrap();

    // Type::TraitObject
    let code = "const X: &dyn Clone = r;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Reference(ty_ref) = get_type_from_const(item) else {
            panic!()
        };
        let syn::Type::TraitObject(ty) = ty_ref.elem.as_ref() else {
            panic!()
        };
        assert_eq!(ty.code(locator), "dyn Clone");
    })
    .unwrap();

    // Type::Tuple
    let code = "const X: (i32, bool) = t;";
    test(code, |item: &syn::ItemConst, locator| {
        let syn::Type::Tuple(ty) = get_type_from_const(item) else {
            panic!()
        };
        assert_eq!(ty.code(locator), "(i32, bool)");
    })
    .unwrap();
}

#[test]
fn test_locate_for_pat() {
    // Pat::Const
    let code = "let const { true } = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Const(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "const { true }");
    })
    .unwrap();

    // Pat::Ident
    let code = "let mut a = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Ident(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "mut a");
    })
    .unwrap();

    // Pat::Lit
    let code = "let 42 = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Lit(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "42");
    })
    .unwrap();

    // Pat::Macro
    let code = "let mac!() = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Macro(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "mac!()");
    })
    .unwrap();

    // Pat::Or
    let code = "match x { A | B => {} _ => {} }";
    test(code, |expr_match: &syn::ExprMatch, locator| {
        let syn::Pat::Or(pat_or) = &expr_match.arms[0].pat else {
            panic!()
        };
        assert_eq!(pat_or.code(locator), "A | B");
    })
    .unwrap();

    // Pat::Paren
    let code = "let (a) = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Paren(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "(a)");
    })
    .unwrap();

    // Pat::Path
    let code = "if let a::B = x {}";
    test(code, |expr: &syn::Expr, locator| {
        let syn::Expr::If(syn::ExprIf { cond, .. }) = expr else {
            panic!()
        };
        let syn::Expr::Let(expr_let) = &**cond else {
            panic!()
        };
        let syn::Pat::Path(pat_path) = &*expr_let.pat else {
            panic!()
        };
        assert_eq!(pat_path.code(locator), "a::B");
    })
    .unwrap();

    // Pat::Range
    let code = "let 1..=10 = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Range(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "1..=10");
    })
    .unwrap();

    // Pat::Reference
    let code = "let &a = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Reference(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "&a");
    })
    .unwrap();

    // Pat::Rest
    let code = "let (a, ..) = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Tuple(pat_tuple) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        let syn::Pat::Rest(pat) = &pat_tuple.elems[1] else {
            panic!()
        };
        assert_eq!(pat.code(locator), "..");
    })
    .unwrap();

    // Pat::Slice
    let code = "let [a, b] = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Slice(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "[a, b]");
    })
    .unwrap();

    // Pat::Struct
    let code = "let Foo { a, b } = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Struct(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "Foo { a, b }");
    })
    .unwrap();

    // Pat::Tuple
    let code = "let (a, b) = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Tuple(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "(a, b)");
    })
    .unwrap();

    // Pat::TupleStruct
    let code = "let Some(a) = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::TupleStruct(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "Some(a)");
    })
    .unwrap();

    // Pat::Type
    let code = "fn foo(a: i32) {}";
    test(code, |item: &syn::ItemFn, locator| {
        let syn::FnArg::Typed(pat_type) = &item.sig.inputs[0] else {
            panic!()
        };
        assert_eq!(pat_type.code(locator), "a: i32");
    })
    .unwrap();

    // Pat::Wild
    let code = "let _ = x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Pat::Wild(pat) = get_pat_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(pat.code(locator), "_");
    })
    .unwrap();
}

#[test]
fn test_locate_for_attribute() {
    // Meta::Path
    let code = "#[test] fn foo() {}";
    test(code, |item: &syn::ItemFn, locator| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(locator), "#[test]");
        let syn::Meta::Path(meta_path) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_path.code(locator), "test");
    })
    .unwrap();

    // Meta::List
    let code = "#[derive(Clone, Debug)] struct Foo;";
    test(code, |item: &syn::ItemStruct, locator| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(locator), "#[derive(Clone, Debug)]");
        let syn::Meta::List(meta_list) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_list.code(locator), "derive(Clone, Debug)");
    })
    .unwrap();

    // Meta::NameValue
    let code = "#[path = \"foo.rs\"] mod foo {}";
    test(code, |item: &syn::ItemMod, locator| {
        let attr = &item.attrs[0];
        assert_eq!(attr.code(locator), "#[path = \"foo.rs\"]");
        let syn::Meta::NameValue(meta_nv) = &attr.meta else {
            panic!()
        };
        assert_eq!(meta_nv.code(locator), "path = \"foo.rs\"");
    })
    .unwrap();

    // Attr inner
    let code = "#![allow(unused)] fn foo() {}";
    test(code, |file: &syn::File, locator| {
        let attr = &file.attrs[0];
        assert_eq!(attr.code(locator), "#![allow(unused)]");
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
        test(code, |stmt: &syn::Stmt, locator| {
            let syn::Expr::Lit(expr_lit) = get_init_expr_from_stmt(stmt) else {
                panic!("expected ExprLit for {expected}")
            };
            assert_eq!(expr_lit.lit.code(locator), expected);
        })
        .unwrap();
    }
}

#[test]
fn test_locate_for_expr() {
    // Expr::Array
    let code = "let a = [1, 2];";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Array(expr_arr) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_arr.code(locator), "[1, 2]");
    })
    .unwrap();

    // Expr::Assign
    let code = "{ let mut a; a = 1; }";
    test(code, |block: &syn::Block, locator| {
        let syn::Stmt::Expr(syn::Expr::Assign(expr_assign), _) = &block.stmts[1] else {
            panic!()
        };
        assert_eq!(expr_assign.code(locator), "a = 1");
    })
    .unwrap();

    // Expr::Async
    let code = "let a = async { 0 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Async(expr_async) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_async.code(locator), "async { 0 }");
    })
    .unwrap();

    // Expr::Await
    let code = "async fn foo() { let fut = async { 0 }; fut.await; }";
    test(code, |item_fn: &syn::ItemFn, locator| {
        let syn::Stmt::Expr(syn::Expr::Await(expr_await), _) = &item_fn.block.stmts[1] else {
            panic!()
        };
        assert_eq!(expr_await.code(locator), "fut.await");
    })
    .unwrap();

    // Expr::Binary
    let code = "let a = 1 + 2;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Binary(expr_bin) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_bin.code(locator), "1 + 2");
    })
    .unwrap();

    // Expr::Block
    let code = "let a = { 1 + 2 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Block(expr_blk) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_blk.code(locator), "{ 1 + 2 }");
    })
    .unwrap();

    // Expr::Break
    let code = "'a: loop { break 'a; }";
    test(code, |expr_loop: &syn::ExprLoop, locator| {
        let syn::Stmt::Expr(syn::Expr::Break(expr_break), _) = &expr_loop.body.stmts[0] else {
            panic!()
        };
        assert_eq!(expr_break.code(locator), "break 'a");
    })
    .unwrap();

    // Expr::Call
    let code = "{ fn foo() {} let a = foo(); }";
    test(code, |expr_blk: &syn::ExprBlock, locator| {
        let syn::Expr::Call(expr_call) = get_init_expr_from_stmt(&expr_blk.block.stmts[1]) else {
            panic!()
        };
        assert_eq!(expr_call.code(locator), "foo()");
    })
    .unwrap();

    // Expr::Cast
    let code = "let a = 1 as f64;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Cast(expr_cast) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_cast.code(locator), "1 as f64");
    })
    .unwrap();

    // Expr::Closure
    let code = "let a = |i: i32| { i };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Closure(expr_closure) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_closure.code(locator), "|i: i32| { i }");
    })
    .unwrap();

    // Expr::Const
    let code = "const C: i32 = const { 1 + 2 };";
    test(code, |item_const: &syn::ItemConst, locator| {
        let syn::Expr::Const(expr_const) = &*item_const.expr else {
            panic!()
        };
        assert_eq!(expr_const.code(locator), "const { 1 + 2 }");
    })
    .unwrap();

    // Expr::Continue
    let code = "'a: loop { continue 'a; }";
    test(code, |expr_loop: &syn::ExprLoop, locator| {
        let syn::Stmt::Expr(syn::Expr::Continue(expr_continue), _) = &expr_loop.body.stmts[0]
        else {
            panic!()
        };
        assert_eq!(expr_continue.code(locator), "continue 'a");
    })
    .unwrap();

    // Expr::Field
    let code = "let a = x.field;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Field(expr_field) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_field.code(locator), "x.field");
    })
    .unwrap();

    // Expr::ForLoop
    let code = "for i in 0..10 { }";
    test(code, |expr: &syn::Expr, locator| {
        let syn::Expr::ForLoop(expr_for) = expr else {
            panic!()
        };
        assert_eq!(expr_for.code(locator), "for i in 0..10 { }");
    })
    .unwrap();

    // Expr::If
    let code = "let a = if true { 1 } else { 2 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::If(expr_if) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_if.code(locator), "if true { 1 } else { 2 }");
    })
    .unwrap();

    // Expr::Index
    let code = "let a = arr[0];";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Index(expr_index) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_index.code(locator), "arr[0]");
    })
    .unwrap();

    // Expr::Infer
    let code = "let a = [0; _];";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Repeat(expr_repeat) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        let syn::Expr::Infer(expr_infer) = &*expr_repeat.len else {
            panic!()
        };
        assert_eq!(expr_infer.code(locator), "_");
    })
    .unwrap();

    // Expr::Let
    let code = "if let Some(x) = opt { }";
    test(code, |expr_if: &syn::ExprIf, locator| {
        let syn::Expr::Let(expr_let) = &*expr_if.cond else {
            panic!()
        };
        assert_eq!(expr_let.code(locator), "let Some(x) = opt");
    })
    .unwrap();

    // Expr::Lit
    let code = "let a = 42;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Lit(expr_lit) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_lit.code(locator), "42");
    })
    .unwrap();

    // Expr::Loop
    let code = "loop { break; }";
    test(code, |expr: &syn::Expr, locator| {
        let syn::Expr::Loop(expr_loop) = expr else {
            panic!()
        };
        assert_eq!(expr_loop.code(locator), "loop { break; }");
    })
    .unwrap();

    // Expr::Macro
    let code = "let a = vec![1, 2, 3];";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Macro(expr_macro) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_macro.code(locator), "vec![1, 2, 3]");
    })
    .unwrap();

    // Expr::Match
    let code = "let a = match x { _ => 1 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Match(expr_match) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_match.code(locator), "match x { _ => 1 }");
    })
    .unwrap();

    // Expr::MethodCall
    let code = "let a = x.foo(1);";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::MethodCall(expr_mc) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_mc.code(locator), "x.foo(1)");
    })
    .unwrap();

    // Expr::Paren
    let code = "let a = (1);";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Paren(expr_paren) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_paren.code(locator), "(1)");
    })
    .unwrap();

    // Expr::Path
    let code = "let a = std::mem::drop;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Path(expr_path) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_path.code(locator), "std::mem::drop");
    })
    .unwrap();

    // Expr::Range
    let code = "let a = 0..10;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Range(expr_range) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_range.code(locator), "0..10");
    })
    .unwrap();

    // Expr::RawAddr
    let code = "let a = &raw const x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::RawAddr(expr_raw) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_raw.code(locator), "&raw const x");
    })
    .unwrap();

    // Expr::Reference
    let code = "let a = &x;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Reference(expr_ref) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_ref.code(locator), "&x");
    })
    .unwrap();

    // Expr::Repeat
    let code = "let a = [0; 5];";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Repeat(expr_repeat) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_repeat.code(locator), "[0; 5]");
    })
    .unwrap();

    // Expr::Return
    let code = "fn foo() -> i32 { return 1; }";
    test(code, |item_fn: &syn::ItemFn, locator| {
        let syn::Stmt::Expr(syn::Expr::Return(expr_return), _) = &item_fn.block.stmts[0] else {
            panic!()
        };
        assert_eq!(expr_return.code(locator), "return 1");
    })
    .unwrap();

    // Expr::Struct
    let code = "let a = Foo { x: 1, y: 2 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Struct(expr_struct) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_struct.code(locator), "Foo { x: 1, y: 2 }");
    })
    .unwrap();

    // Expr::Try
    let code = "let a = x()?;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Try(expr_try) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_try.code(locator), "x()?");
    })
    .unwrap();

    // Expr::TryBlock
    let code = "let a = try { 1 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::TryBlock(expr_try_block) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_try_block.code(locator), "try { 1 }");
    })
    .unwrap();

    // Expr::Tuple
    let code = "let a = (1, 2);";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Tuple(expr_tuple) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_tuple.code(locator), "(1, 2)");
    })
    .unwrap();

    // Expr::Unary
    let code = "let a = !true;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Unary(expr_unary) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_unary.code(locator), "!true");
    })
    .unwrap();

    // Expr::Unsafe
    let code = "let a = unsafe { 1 };";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Unsafe(expr_unsafe) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_unsafe.code(locator), "unsafe { 1 }");
    })
    .unwrap();

    // Expr::While
    let code = "while true { break; }";
    test(code, |expr: &syn::Expr, locator| {
        let syn::Expr::While(expr_while) = expr else {
            panic!()
        };
        assert_eq!(expr_while.code(locator), "while true { break; }");
    })
    .unwrap();

    // Expr::Yield
    let code = "let a = yield 1;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Yield(expr_yield) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        assert_eq!(expr_yield.code(locator), "yield 1");
    })
    .unwrap();
}

#[test]
fn test_locate_etc() {
    test_located_wrapper();
    test_locate_location();
    test_locate_for_captured_param();
    test_locate_for_bound_lifetimes();
    test_locate_for_field_pat();
    test_locate_for_field_value();
    test_locate_for_generics();
    test_locate_for_qself();
}

fn test_located_wrapper() {
    let code = "struct A { a: i32 }";
    let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    let located = Located::new(syntax, &unique_name(), code).unwrap();

    assert_eq!(located.syntax().ident, "A");
    assert_eq!(located.ident, "A");
    assert_eq!(located.code(&located.ident), "A");
    assert_eq!(located.location(&located.ident).start, 7);
    assert_eq!(located.location(&located.ident).end, 8);

    let msg = located.location_message(&located.ident);
    let start = msg.find(':').unwrap();
    assert_eq!(&msg[start..], ":1: A");

    assert_eq!(located.syntax().ident.code(located.locator()), "A");
}

fn test_locate_location() {
    let code = "1 + 2";
    test(code, |bin: &syn::ExprBinary, locator| {
        assert_eq!(bin.op.location(locator).start, 2);
        assert_eq!(bin.op.location(locator).end, 3);
        let msg = bin.op.location_message(locator);
        let start = msg.find(':').unwrap();
        assert_eq!(&msg[start..], ":1: +"); // file_path:line_number: content
    })
    .unwrap();
}

fn test_locate_for_captured_param() {
    let code = "fn f<'a, T>() -> impl Trait + use<'a, T> {}";
    test(code, |item_fn: &syn::ItemFn, locator| {
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
        assert_eq!(trait_bound.code(locator), "Trait");
        assert_eq!(capture.code(locator), "use<'a, T>");
        assert_eq!(capture.params[0].code(locator), "'a");
        assert_eq!(capture.params[1].code(locator), "T");
    })
    .unwrap();
}

fn test_locate_for_bound_lifetimes() {
    let code = "fn foo<F: for<'a> Fn(&'a i32)>() {}";
    test(code, |item_fn: &syn::ItemFn, locator| {
        let syn::GenericParam::Type(ty_param) = &item_fn.sig.generics.params[0] else {
            panic!()
        };
        let syn::TypeParamBound::Trait(trait_bound) = &ty_param.bounds[0] else {
            panic!()
        };
        let bound_lifetimes = trait_bound.lifetimes.as_ref().unwrap();
        assert_eq!(bound_lifetimes.code(locator), "for<'a>");
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
    let located = locate::<syn::Stmt>(&unique_name(), code).unwrap();
    let syn = located.syntax();
    let locator = located.locator();

    let local = match syn {
        syn::Stmt::Local(v) => v,
        _ => unreachable!(),
    };

    let pat_struct = match &local.pat {
        syn::Pat::Struct(v) => v,
        _ => unreachable!(),
    };

    // a,
    let mut i = 0;
    assert_eq!(pat_struct.fields[i].member.code(locator), "a");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "a");
    i += 1;

    // ref b,
    assert_eq!(pat_struct.fields[i].member.code(locator), "b");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "ref b");
    i += 1;

    // ref mut c,
    assert_eq!(pat_struct.fields[i].member.code(locator), "c");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "ref mut c");
    i += 1;

    // d: dd,
    assert_eq!(pat_struct.fields[i].member.code(locator), "d");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "dd");
    i += 1;

    // e: ref ee,
    assert_eq!(pat_struct.fields[i].member.code(locator), "e");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "ref ee");
    i += 1;

    // f: ref mut ff,
    assert_eq!(pat_struct.fields[i].member.code(locator), "f");
    assert_eq!(pat_struct.fields[i].pat.code(locator), "ref mut ff");
}

fn test_locate_for_field_value() {
    let code = "
    T {
        a,
        b: b,
        c: x + y,
    }
    ";
    let located = locate::<syn::ExprStruct>(&unique_name(), code).unwrap();
    let syn = located.syntax();
    let locator = located.locator();

    // a,
    let mut i = 0;
    assert_eq!(syn.fields[i].member.code(locator), "a");
    assert_eq!(syn.fields[i].expr.code(locator), "a");
    i += 1;

    // b: b,
    assert_eq!(syn.fields[i].member.code(locator), "b");
    assert_eq!(syn.fields[i].expr.code(locator), "b");
    i += 1;

    // c: x + y,
    assert_eq!(syn.fields[i].member.code(locator), "c");
    assert_eq!(syn.fields[i].expr.code(locator), "x + y");
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

    let located = locate::<syn::File>(&unique_name(), code).unwrap();
    let syn = located.syntax();
    let locator = located.locator();

    // impl<T> S<T> {}
    let mut i = 0;
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_impl.generics.code(locator), "<T>");
    i += 1;

    // impl<T: A> S<T> where T: B {}
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_impl.generics.code(locator), "<T: A> S<T> where T: B");
    assert_eq!(item_impl.generics.params.code(locator), "T: A");
    assert_eq!(item_impl.generics.where_clause.code(locator), "where T: B");
    i += 1;

    // impl<T: A> Trait for S<T> where T: B {}
    let syn::Item::Impl(item_impl) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(
        item_impl.generics.code(locator),
        "<T: A> Trait for S<T> where T: B"
    );
    assert_eq!(item_impl.generics.params.code(locator), "T: A");
    assert_eq!(item_impl.generics.where_clause.code(locator), "where T: B");
    i += 1;

    // fn f<T: A>() where T: B {}
    let syn::Item::Fn(item_fn) = &syn.items[i] else {
        unreachable!()
    };
    assert_eq!(item_fn.sig.generics.code(locator), "<T: A>() where T: B");
    assert_eq!(item_fn.sig.generics.params.code(locator), "T: A");
    assert_eq!(
        item_fn.sig.generics.where_clause.code(locator),
        "where T: B"
    );
}

fn test_locate_for_qself() {
    let code = "let f = <i32 as std::fmt::Display>::fmt;";
    test(code, |stmt: &syn::Stmt, locator| {
        let syn::Expr::Path(expr_path) = get_init_expr_from_stmt(stmt) else {
            panic!()
        };
        let qself = expr_path.qself.as_ref().unwrap();
        assert_eq!(qself.code(locator), "<i32 as std::fmt::Display>");
        assert_eq!(qself.ty.code(locator), "i32");
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
fn test_find_for_composite_variants() {
    fn assert_find_ptr<A, D>(ancestor: &A, locator: &Locator, code: &str)
    where
        A: FindPtr,
        D: 'static,
    {
        assert!(
            ancestor
                .find_ptr(locator, std::any::TypeId::of::<D>(), code)
                .is_some(),
            "failed to find `{code}` as `{}`",
            std::any::type_name::<D>()
        );
    }

    test_find::<syn::ImplItem, syn::ImplItemConst>("const X: i32 = 1;", "const X: i32 = 1;")
        .unwrap();
    test_find::<syn::ImplItem, syn::ImplItemFn>("fn f(&self, x: i32) {}", "fn f(&self, x: i32) {}")
        .unwrap();
    test_find::<syn::ImplItem, syn::ImplItemType>("type T = i32;", "type T = i32;").unwrap();
    test_find::<syn::ImplItem, syn::ImplItemMacro>("m!();", "m!();").unwrap();
    test_find::<syn::ImplItem, syn::Receiver>("fn f(&self) {}", "&self").unwrap();
    test_find::<syn::ImplItem, syn::PatType>("fn f(x: i32) {}", "x: i32").unwrap();

    test_find::<syn::ForeignItem, syn::ForeignItemFn>("fn f(x: i32);", "fn f(x: i32);").unwrap();
    test_find::<syn::ForeignItem, syn::ForeignItemStatic>("static X: i32;", "static X: i32;")
        .unwrap();
    test_find::<syn::ForeignItem, syn::ForeignItemType>("type T;", "type T;").unwrap();
    test_find::<syn::ForeignItem, syn::ForeignItemMacro>("m!();", "m!();").unwrap();

    test_find::<syn::ImplItem, syn::Token![const]>("const X: i32 = 1;", "const").unwrap();
    test_find::<syn::ImplItem, syn::Token![fn]>("fn f(&self, x: i32) {}", "fn").unwrap();
    test_find::<syn::ImplItem, syn::Token![type]>("type T = i32;", "type").unwrap();
    test_find::<syn::ImplItem, syn::Path>("m!();", "m").unwrap();
    test_find::<syn::ForeignItem, syn::Token![fn]>("fn f(x: i32);", "fn").unwrap();
    test_find::<syn::ForeignItem, syn::Token![static]>("static X: i32;", "static").unwrap();
    test_find::<syn::ForeignItem, syn::Token![type]>("type T;", "type").unwrap();
    test_find::<syn::ForeignItem, syn::Path>("m!();", "m").unwrap();

    test_find::<syn::ItemStruct, syn::FieldsUnnamed>("struct T(i32);", "(i32)").unwrap();
    test_find::<syn::ItemFn, syn::LifetimeParam>("fn f<'a>() {}", "'a").unwrap();
    test_find::<syn::ItemFn, syn::TypeParam>("fn f<T>() {}", "T").unwrap();
    test_find::<syn::ItemFn, syn::ConstParam>("fn f<const N: usize>() {}", "const N: usize")
        .unwrap();

    test_find::<syn::ItemType, syn::GenericArgument>("type T = Foo<'a>;", "'a").unwrap();
    test_find::<syn::ItemType, syn::GenericArgument>("type T = Vec<i32>;", "i32").unwrap();
    test_find::<syn::ItemType, syn::GenericArgument>("type T = Array<3>;", "3").unwrap();
    test_find::<syn::ItemType, syn::AssocType>("type T = Trait<Item = i32>;", "Item = i32")
        .unwrap();
    test_find::<syn::ItemType, syn::AssocConst>("type T = Trait<N = 3>;", "N = 3").unwrap();
    test_find::<syn::ItemType, syn::Constraint>("type T = Trait<Item: Clone>;", "Item: Clone")
        .unwrap();

    let located = locate::<syn::ItemFn>(&unique_name(), "#[test] fn f() {}").unwrap();
    assert_find_ptr::<_, syn::Path>(&located.attrs[0].meta, located.locator(), "test");

    let located =
        locate::<syn::ItemStruct>(&unique_name(), "#[derive(Clone, Debug)] struct T;").unwrap();
    assert_find_ptr::<_, syn::MetaList>(
        &located.attrs[0].meta,
        located.locator(),
        "derive(Clone, Debug)",
    );

    let located =
        locate::<syn::ItemMod>(&unique_name(), "#[path = \"foo.rs\"] mod foo {}").unwrap();
    assert_find_ptr::<_, syn::MetaNameValue>(
        &located.attrs[0].meta,
        located.locator(),
        "path = \"foo.rs\"",
    );

    let located = locate::<syn::File>(&unique_name(), "macro_rules! m { () => {} }").unwrap();
    let syn::Item::Macro(item_macro) = &located.items[0] else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::Path>(item_macro, located.locator(), "macro_rules");
    assert_find_ptr::<_, syn::Ident>(item_macro, located.locator(), "m");
    assert_find_ptr::<_, syn::token::Brace>(
        &item_macro.mac.delimiter,
        located.locator(),
        "{ () => {} }",
    );

    let located = locate::<syn::ItemFn>(&unique_name(), "fn f() { m!(); }").unwrap();
    let syn::Stmt::Macro(stmt_macro) = &located.block.stmts[0] else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::token::Paren>(&stmt_macro.mac.delimiter, located.locator(), "()");

    let located = locate::<syn::ItemFn>(&unique_name(), "fn f() { m![]; }").unwrap();
    let syn::Stmt::Macro(stmt_macro) = &located.block.stmts[0] else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::token::Bracket>(&stmt_macro.mac.delimiter, located.locator(), "[]");

    let located = locate::<syn::ItemType>(&unique_name(), "type T = dyn Fn(i32) -> bool;").unwrap();
    let syn::Type::TraitObject(trait_object) = located.ty.as_ref() else {
        unreachable!()
    };
    let syn::TypeParamBound::Trait(trait_bound) = &trait_object.bounds[0] else {
        unreachable!()
    };
    let syn::PathArguments::Parenthesized(args) = &trait_bound.path.segments[0].arguments else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::Type>(
        &trait_bound.path.segments[0].arguments,
        located.locator(),
        "i32",
    );
    assert_find_ptr::<_, syn::ReturnType>(args, located.locator(), "-> bool");

    let located = locate::<syn::ExprRange>(&unique_name(), "0..1").unwrap();
    assert_find_ptr::<_, syn::Token![..]>(&located.limits, located.locator(), "..");

    let located = locate::<syn::ExprRange>(&unique_name(), "0..=1").unwrap();
    assert_find_ptr::<_, syn::Token![..=]>(&located.limits, located.locator(), "..=");

    let located = locate::<syn::ItemFn>(
        &unique_name(),
        "fn f<'a, T>() -> impl Trait + use<'a, T> {}",
    )
    .unwrap();
    let syn::ReturnType::Type(_, ty) = &located.sig.output else {
        unreachable!()
    };
    let syn::Type::ImplTrait(ty_impl_trait) = &**ty else {
        unreachable!()
    };
    let syn::TypeParamBound::PreciseCapture(capture) = &ty_impl_trait.bounds[1] else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::Lifetime>(&capture.params[0], located.locator(), "'a");
    assert_find_ptr::<_, syn::Ident>(&capture.params[1], located.locator(), "T");

    let located = locate::<syn::ItemType>(&unique_name(), "type T = Foo<'a, i32, 3>;").unwrap();
    let syn::Type::Path(type_path) = located.ty.as_ref() else {
        unreachable!()
    };
    let syn::PathArguments::AngleBracketed(args) = &type_path.path.segments[0].arguments else {
        unreachable!()
    };
    assert_find_ptr::<_, syn::Lifetime>(&args.args[0], located.locator(), "'a");
    assert_find_ptr::<_, syn::Type>(&args.args[1], located.locator(), "i32");
    assert_find_ptr::<_, syn::Expr>(&args.args[2], located.locator(), "3");
}

#[cfg(feature = "find")]
#[test]
fn test_find_etc() {
    let code = "
    struct A {
        a: i32,
    }";
    let located = locate::<syn::ItemStruct>(&unique_name(), code).unwrap();
    let syn = located.syntax();
    let locator = located.locator();

    let field: &syn::Field = syn.find(locator, "a: i32").unwrap();
    assert_eq!(field.code(locator), "a: i32");

    let field: &syn::Field = located.find("a: i32").unwrap();
    assert_eq!(located.code(field), "a: i32");
}
