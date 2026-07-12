use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use std::fmt::Write;
use syn_locator::Located;

const NUMERIC_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "f32",
    "f64",
];

const INTEGER_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
];

const BITWISE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "bool",
];

const NEG_TYPES: &[&str] = &["i8", "i16", "i32", "i64", "i128", "isize", "f32", "f64"];

fn push_binary_operator(
    source: &mut String,
    trait_name: &str,
    method: &str,
    self_types: &[&str],
    rhs_types: Option<&[&str]>,
) {
    write!(
        source,
        "
        pub trait {trait_name}<Rhs=Self> {{
            type Output;
            fn {method}(self, rhs: Rhs) -> Self::Output;
        }}
        "
    )
    .unwrap();

    for &self_ty in self_types {
        if let Some(rhs_types) = rhs_types {
            for &rhs_ty in rhs_types {
                push_binary_impl(source, trait_name, method, self_ty, rhs_ty);
            }
        } else {
            push_binary_impl(source, trait_name, method, self_ty, self_ty);
        }
    }
}

fn push_binary_impl(
    source: &mut String,
    trait_name: &str,
    method: &str,
    output_ty: &str,
    rhs_ty: &str,
) {
    for (self_ty, rhs_ty) in [
        (output_ty.to_string(), rhs_ty.to_string()),
        (output_ty.to_string(), format!("&{rhs_ty}")),
        (format!("&{output_ty}"), rhs_ty.to_string()),
        (format!("&{output_ty}"), format!("&{rhs_ty}")),
    ] {
        write!(
            source,
            "
            impl {trait_name}<{rhs_ty}> for {self_ty} {{
                type Output = {output_ty};
                fn {method}(self, rhs: {rhs_ty}) -> {output_ty} {{}}
            }}
            "
        )
        .unwrap();
    }
}

fn push_assign_operator(source: &mut String, trait_name: &str, method: &str, types: &[&str]) {
    write!(
        source,
        "
        pub trait {trait_name}<Rhs=Self> {{
            fn {method}(&mut self, rhs: Rhs);
        }}
        "
    )
    .unwrap();

    for ty in types {
        for rhs_ty in [ty.to_string(), format!("&{ty}")] {
            write!(
                source,
                "
                impl {trait_name}<{rhs_ty}> for {ty} {{
                    fn {method}(&mut self, rhs: {rhs_ty}) {{}}
                }}
                "
            )
            .unwrap();
        }
    }
}

fn push_unary_operator(source: &mut String, trait_name: &str, method: &str, types: &[&str]) {
    write!(
        source,
        "
        pub trait {trait_name} {{
            type Output;
            fn {method}(self) -> Self::Output;
        }}
        "
    )
    .unwrap();

    for ty in types {
        for self_ty in [ty.to_string(), format!("&{ty}")] {
            write!(
                source,
                "
                impl {trait_name} for {self_ty} {{
                    type Output = {ty};
                    fn {method}(self) -> {ty} {{}}
                }}
                "
            )
            .unwrap();
        }
    }
}

fn push_operator_set(source: &mut String) {
    for (trait_name, method) in [
        ("Add", "add"),
        ("Sub", "sub"),
        ("Mul", "mul"),
        ("Div", "div"),
        ("Rem", "rem"),
    ] {
        push_binary_operator(source, trait_name, method, NUMERIC_TYPES, None);
    }
    for (trait_name, method) in [
        ("BitXor", "bitxor"),
        ("BitAnd", "bitand"),
        ("BitOr", "bitor"),
    ] {
        push_binary_operator(source, trait_name, method, BITWISE_TYPES, None);
    }
    for (trait_name, method) in [("Shl", "shl"), ("Shr", "shr")] {
        push_binary_operator(
            source,
            trait_name,
            method,
            INTEGER_TYPES,
            Some(INTEGER_TYPES),
        );
    }
    for (trait_name, method) in [
        ("AddAssign", "add_assign"),
        ("SubAssign", "sub_assign"),
        ("MulAssign", "mul_assign"),
        ("DivAssign", "div_assign"),
        ("RemAssign", "rem_assign"),
    ] {
        push_assign_operator(source, trait_name, method, NUMERIC_TYPES);
    }
    for (trait_name, method) in [
        ("BitXorAssign", "bitxor_assign"),
        ("BitAndAssign", "bitand_assign"),
        ("BitOrAssign", "bitor_assign"),
    ] {
        push_assign_operator(source, trait_name, method, BITWISE_TYPES);
    }
    push_unary_operator(source, "Not", "not", BITWISE_TYPES);
    push_unary_operator(source, "Neg", "neg", NEG_TYPES);
}

fn core_source() -> String {
    let mut source = String::with_capacity(200_000);
    source.push_str("pub mod ops {");
    push_operator_set(&mut source);
    source.push('}');
    source
}

fn core(c: &mut Criterion) {
    let source = core_source();

    // Fail before Criterion starts sampling if a generator edit accidentally makes the fixture
    // tiny or syntactically invalid.
    assert!(
        source.len() > 100_000,
        "core fixture is only {} bytes",
        source.len()
    );
    let syntax = syn::parse_file(&source).expect("core benchmark source should parse");
    assert!(syntax.items.len() == 1);

    let mut group = c.benchmark_group("core");
    group.throughput(Throughput::Bytes(source.len() as u64));

    // Measures construction performance, including parsing and location collection.
    group.bench_function("parse_and_locate", |b| {
        b.iter(|| syn_locator::locate::<syn::File>("core.rs", black_box(source.as_str())).unwrap());
    });

    // Measures construction performance from an already parsed syntax tree.
    group.bench_function("locate_only", |b| {
        b.iter_batched(
            || syntax.clone(),
            |syntax| Located::new(syntax, "core.rs", black_box(source.as_str())).unwrap(),
            BatchSize::SmallInput,
        );
    });

    group.finish();

    let located = Located::new(syntax, "core.rs", source).unwrap();
    let (location_count, _) = located.locator().benchmark_all_location_lookups();
    assert!(location_count > 200_000);

    let mut lookup_group = c.benchmark_group("core_lookup");
    lookup_group.throughput(Throughput::Elements(location_count as u64));
    // Measures lookup performance across all recorded node locations.
    lookup_group.bench_function("all_locations", |b| {
        b.iter(|| located.locator().benchmark_all_location_lookups());
    });
    lookup_group.finish();
}

criterion_group!(benches, core);
criterion_main!(benches);
