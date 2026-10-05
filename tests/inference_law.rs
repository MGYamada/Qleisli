//! Static choices stay explicit; diagnostics identify unresolved bindings.
//! Small native action checks do not establish a source-preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use qleisli::frontend::sized::{Error, OperationBinding, ParsedProgram};
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;
use std::path::Path;

fn study(name: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
        "tests/fixtures/authoring_sessions/inference-law-v030/attempt-01/{name}/main.qli"
    )))
    .unwrap()
}
fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}
fn naturals(values: &[(&str, u32)]) -> BTreeMap<String, u32> {
    values.iter().map(|(n, v)| ((*n).into(), *v)).collect()
}
fn operations(names: &[&str]) -> BTreeMap<String, OperationBinding> {
    names
        .iter()
        .map(|n| {
            (
                (*n).into(),
                OperationBinding::new("main::identity", BTreeMap::new()),
            )
        })
        .collect()
}
fn static_error(error: &Error, fragments: &[&str]) {
    assert_eq!(error.code(), "static");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().start < error.span().end);
    for fragment in fragments {
        assert!(error.message().contains(fragment), "{error}");
    }
}

#[test]
fn missing_unused_naturals_and_extras_are_named_in_deterministic_order() {
    let text = study("natural-pair");
    let program = parsed(&text);
    let missing = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    static_error(
        &missing,
        &[
            "entry main::f",
            "natural",
            "missing [m, n]",
            "unexpected []",
        ],
    );
    let a = program
        .instantiate("main::f", naturals(&[("n", 1), ("z", 2)]), BTreeMap::new())
        .unwrap_err();
    let b = program
        .instantiate("main::f", naturals(&[("z", 2), ("n", 1)]), BTreeMap::new())
        .unwrap_err();
    static_error(&a, &["missing [m]", "unexpected [z]"]);
    assert_eq!(a, b);
    assert_eq!(&text[a.span().start..a.span().end], text.trim_end());
    for ns in [
        naturals(&[("n", 1), ("m", 0)]),
        naturals(&[("m", 0), ("n", 1)]),
    ] {
        program
            .instantiate("main::f", ns, BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
    }
}

#[test]
fn operation_bindings_are_explicit_and_natural_errors_keep_priority() {
    let program = parsed(&study("operation-choice"));
    let missing = program
        .instantiate("main::f", BTreeMap::new(), operations(&["V"]))
        .unwrap_err();
    static_error(
        &missing,
        &[
            "operation",
            "entry main::f",
            "missing [U]",
            "unexpected [V]",
        ],
    );
    let wrong_category = program
        .instantiate("main::f", naturals(&[("U", 0)]), BTreeMap::new())
        .unwrap_err();
    static_error(
        &wrong_category,
        &["natural", "missing []", "unexpected [U]"],
    );
    let pair = parsed(&study("operation-pair"));
    let missing = pair
        .instantiate("main::f", BTreeMap::new(), operations(&["U"]))
        .unwrap_err();
    static_error(&missing, &["missing [V]"]);
    let extra = pair
        .instantiate("main::f", BTreeMap::new(), operations(&["U", "V", "W"]))
        .unwrap_err();
    static_error(&extra, &["missing []", "unexpected [W]"]);
}

#[test]
fn nested_provider_errors_identify_the_operation_and_resolved_provider() {
    let program = parsed(&study("provider-natural"));
    for ns in [
        BTreeMap::new(),
        naturals(&[("z", 1)]),
        naturals(&[("n", 0), ("z", 1)]),
    ] {
        let bindings =
            BTreeMap::from([("U".into(), OperationBinding::new("main::keep", ns.clone()))]);
        let error = program
            .instantiate("main::f", BTreeMap::new(), bindings)
            .unwrap_err();
        static_error(&error, &["natural", "operation U provider main::keep"]);
        if !ns.contains_key("n") {
            assert!(error.message().contains("missing [n]"));
        }
        if ns.contains_key("z") {
            assert!(error.message().contains("unexpected [z]"));
        }
    }
    program
        .instantiate(
            "main::f",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::keep", naturals(&[("n", 0)])),
            )]),
        )
        .unwrap()
        .elaborate()
        .unwrap();
}

#[test]
fn call_arity_names_ordered_static_parameters_without_guessing() {
    for (case, expected, actual) in [
        ("call-missing-natural", "[n: Nat, m: Nat]", "1"),
        ("call-extra-natural", "[n: Nat]", "2"),
        ("call-missing-operation", "[U: Op]", "0"),
        ("call-extra-operation", "[U: Op]", "2"),
    ] {
        let source = study(case);
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        static_error(
            &error,
            &["main::g", expected, &format!("received {actual}")],
        );
        let site = &source[error.span().start..error.span().end];
        assert!(site.starts_with("g[") || site == "g(q)", "{case}: {site}");
    }
    parsed(&study("call-exact-control"))
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap();
}

#[test]
fn expected_types_do_not_choose_physics_or_manufacture_access_and_effects() {
    for (source, code) in [
        ("pub unitary fn f(q:Q<Bit>)->Bit{q}", "type"),
        ("pub unitary fn f(b:Bit)->Q<Bit>{b}", "type"),
        ("pub unitary fn f(q:Q<Bit>)->Q<Bits<1>>{q}", "type"),
        (
            "pub unitary fn f[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{U(q)}",
            "access",
        ),
        (
            "use std::observe::measure_z; pub unitary fn f(q:Q<Bit>)->Bit{measure_z(q)}",
            "effect",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), code, "{error}");
    }
}

#[test]
fn explicit_identity_and_x_providers_retain_distinct_reference_actions() {
    let program = parsed(&study("operation-choice"));
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit checker"));
    // Two blocks represent a retained two-dimensional external reference.
    // Coefficients and expected X permutation are specified independently.
    let input = vec![[0.2, -0.3], [0.4, 0.1], [-0.6, 0.2], [0.3, 0.5]];
    let mut payloads = vec![];
    for (provider, flip) in [("identity", false), ("flip", true)] {
        let graph = program
            .instantiate(
                "main::f",
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new(format!("main::{provider}"), BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let checked = kernel.inspect_native(proposal.payload()).unwrap();
        let output = checked
            .execute_pure(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap()
            .amplitudes;
        for (i, row) in output.iter().enumerate() {
            let expected = input[if flip { i ^ 1 } else { i }];
            for (a, b) in row.iter().zip(expected) {
                assert!((a - b).abs() < 1e-12);
            }
        }
        payloads.push(proposal.payload().to_vec());
    }
    assert_ne!(payloads[0], payloads[1]);
}
