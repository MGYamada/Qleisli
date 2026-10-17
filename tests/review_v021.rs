//! User review of published 0.2.1, addressed in the 0.2.2 working tree.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{check_project, compile_project};
use qleisli::frontend::core::PRIMITIVES;
use qleisli::frontend::parser::{parse_documented_module, parse_module};
use qleisli::sim::{SimulationLimits, run_closed};

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn th_repetition_matches_an_independent_numerical_recurrence_and_inline_source() {
    th_repetition(&[0, 1, 16, 400, 512, 1000, 1024], 16);
}

#[test]
#[ignore = "#278 v0.3.1 stress: 1024 directly expanded TH pairs exceed the native timeout on Linux CI"]
fn large_inline_th_repetition_matches_the_same_independent_recurrence() {
    th_repetition(&[1024], 1024);
}

fn th_repetition(counts: &[usize], inline_count: usize) {
    let root = SourceRoot::new("");
    let imports = "use std::state::init0; use std::gate::t;\x20
        unitary fn ht(q:Q<Bit>)->Q<Bit>{t(h(q))}";
    for &count in counts {
        let source =
            format!("{imports} observe fn main()->Bit{{measure_z(power(ht,{count})(init0()))}}");
        root.write("main.qli", &source);
        let program = compile_project(&root.0).unwrap();
        let actual = run_closed(&program, SimulationLimits::default()).unwrap();
        let r = std::f64::consts::FRAC_1_SQRT_2;
        let (mut a, mut b) = ((1.0, 0.0), (0.0, 0.0));
        for _ in 0..count {
            let next = ((a.0 + b.0) * r, (a.1 + b.1) * r);
            let diff = ((a.0 - b.0) * r, (a.1 - b.1) * r);
            a = next;
            b = ((diff.0 - diff.1) * r, (diff.0 + diff.1) * r);
        }
        let expected = b.0 * b.0 + b.1 * b.1;
        assert!(
            (actual.get(&vec![true]).copied().unwrap_or(0.0) - expected).abs() < 1e-11,
            "count={count}: {actual:?}"
        );
        if count == inline_count {
            let inline = "let q=t(h(q));".repeat(count);
            root.write(
                "main.qli",
                &format!("{imports} observe fn main()->Bit{{let q=init0();{inline}measure_z(q)}}"),
            );
            let flat = compile_project(&root.0).unwrap();
            let result = run_closed(&flat, SimulationLimits::default()).unwrap();
            for (bits, probability) in &actual {
                assert!((result.get(bits).copied().unwrap_or(0.0) - probability).abs() < 1e-11);
            }
        }
    }
    for body in ["power(missing,0)(q)", "power(bad,0)(q)"] {
        root.write("main.qli", &format!("{imports} observe fn bad(q:Q<Bit>)->Bit{{measure_z(q)}} unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}"));
        assert!(check_project(&root.0).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution() {
    let source = "// 日本語\n/// Shared import docs.\nuse std::{state::init0,gate::{x,t,}};\nobserve fn main()->Bit{measure_z(h(init0()))}";
    let parsed = parse_documented_module(source).unwrap();
    assert_eq!(parsed.syntax.uses.len(), 3);
    for (item, docs) in parsed.syntax.uses.iter().zip(&parsed.import_docs) {
        assert_eq!(docs[0].text, " Shared import docs.");
        assert_eq!(
            &source[item.span.start..item.span.end],
            "use std::{state::init0,gate::{x,t,}};"
        );
    }
    let root = SourceRoot::new(source);
    assert_eq!(
        run_closed(
            &compile_project(&root.0).unwrap(),
            SimulationLimits::default()
        )
        .unwrap()
        .len(),
        2
    );
    for bad in [
        "use std::gate::{};",
        "use std::gate::{x,,t};",
        "use std::gate::{x t};",
        "use std::gate::{x;",
    ] {
        assert!(parse_module(bad).is_err(), "{bad}");
    }
    for bad in ["use std::gate::{x,x};", "use helper::{hidden};"] {
        root.write("main.qli", bad);
        root.write("helper.qli", "unitary fn hidden(q:Q<Bit>)->Q<Bit>{q}");
        assert!(check_project(&root.0).is_err(), "{bad}");
    }
    let deep = format!("use {}h{};", "std::{".repeat(70), "}".repeat(70));
    assert!(
        parse_module(&deep)
            .unwrap_err()
            .message
            .contains("64-level")
    );
    // Existing long ungrouped paths remain iterative, with no new depth limit.
    assert!(parse_module(&format!("use {}h;", "module::".repeat(100))).is_ok());
}

fn wide_import(prefix: &str, leaves: usize) -> String {
    let names = (0..leaves)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    format!("use {prefix}::{{{names}}};")
}

#[test]
fn grouped_imports_reject_long_prefix_amplification_before_expanding_every_leaf() {
    let prefix = vec!["m"; 1024].join("::");
    let source = wide_import(&prefix, 1024);
    assert!(source.len() < 8192);
    let error = parse_module(&source)
        .map(|_| ())
        .expect_err("amplified import must exceed the copy budget");
    assert!(
        error.message.contains("copied identifiers limit"),
        "{error}"
    );
    assert_eq!(&source[error.span.start..error.span.end], "a64");

    // Copies made inside nested groups spend the same budget.
    let nested = source
        .replacen("::{", "::{inner::{", 1)
        .replacen("};", "}};", 1);
    let error = parse_module(&nested)
        .map(|_| ())
        .expect_err("nested imports must share the copy budget");
    assert!(
        error.message.contains("copied identifiers limit"),
        "{error}"
    );
    assert_eq!(&nested[error.span.start..error.span.end], "a62");
}

#[test]
fn grouped_import_copy_budget_is_shared_across_use_items_and_reset_per_module() {
    let prefix = vec!["m"; 256].join("::");
    let group = wide_import(&prefix, 128);
    let at_limit = group.repeat(2);
    assert_eq!(parse_module(&at_limit).unwrap().uses.len(), 256);

    let over_limit = format!("{at_limit}use {prefix}::{{last}};");
    let error = parse_module(&over_limit)
        .map(|_| ())
        .expect_err("separate use items must share the copy budget");
    assert!(
        error.message.contains("copied identifiers limit"),
        "{error}"
    );
    assert_eq!(&over_limit[error.span.start..error.span.end], "last");
    assert_eq!(parse_module(&group).unwrap().uses.len(), 128);
}

#[test]
fn grouped_imports_bound_copied_name_bytes_as_well_as_identifier_count() {
    let prefix = "m".repeat(4096);
    let at_limit = wide_import(&prefix, 256);
    assert_eq!(parse_module(&at_limit).unwrap().uses.len(), 256);

    let over_limit = wide_import(&prefix, 257);
    let error = parse_module(&over_limit)
        .map(|_| ())
        .expect_err("long names must exceed the byte budget");
    assert!(error.message.contains("copied name bytes limit"), "{error}");
    assert_eq!(&over_limit[error.span.start..error.span.end], "a256");
}

#[test]
fn ungrouped_imports_do_not_spend_the_group_expansion_budget() {
    let source = format!("use {}leaf;", "m::".repeat(65_537));
    let parsed = parse_module(&source).unwrap();
    assert_eq!(parsed.uses.len(), 1);
    assert_eq!(parsed.uses[0].path.len(), 65_538);
}

#[test]
fn grouped_import_documentation_checks_copied_bytes_before_cloning() {
    let comment = format!("///{}\n", "m".repeat(1024));
    let at_limit = format!("{comment}{}", wide_import("m", 1025));
    let documented = parse_documented_module(&at_limit).unwrap();
    assert_eq!(documented.import_docs.len(), 1025);
    assert!(documented.import_docs.iter().all(|docs| docs.len() == 1));

    let over_limit = format!("{comment}{}", wide_import("m", 1026));
    let error = parse_documented_module(&over_limit)
        .map(|_| ())
        .expect_err("grouped documentation must exceed the byte budget");
    assert!(
        error.message.contains("copied comment bytes limit"),
        "{error}"
    );
    assert_eq!(error.span.start, 0);

    // Documentation copies across separate use items are cumulative as well.
    let over_limit = format!("{at_limit}{comment}{}", wide_import("m", 2));
    let error = parse_documented_module(&over_limit)
        .map(|_| ())
        .expect_err("separate use items must share the documentation copy budget");
    assert!(
        error.message.contains("copied comment bytes limit"),
        "{error}"
    );
    assert_eq!(error.span.start, at_limit.len());
}

#[test]
fn grouped_import_documentation_bounds_empty_comment_copies() {
    let group = wide_import("m", 3);
    let at_limit = format!("{}{group}", "///\n".repeat(32_768));
    let documented = parse_documented_module(&at_limit).unwrap();
    assert!(
        documented
            .import_docs
            .iter()
            .all(|docs| docs.len() == 32_768)
    );

    let over_limit = format!("{}{group}", "///\n".repeat(32_769));
    let error = parse_documented_module(&over_limit)
        .map(|_| ())
        .expect_err("empty comments must still spend the copy count budget");
    assert!(error.message.contains("comment copies limit"), "{error}");
    assert_eq!(error.span.start, 4 * 32_768);
}

#[test]
fn grouped_import_markdown_renders_each_source_item_once() {
    let group = wide_import("m", 1024);
    let source =
        format!("/// Shared group docs.\n{group}\n/// Separate group docs.\nuse n::{{x,y}};");
    let rendered = qleisli::frontend::documentation::render_markdown(&source).unwrap();
    assert_eq!(rendered.matches("## Import\n").count(), 2);
    assert_eq!(rendered.matches(&group).count(), 1);
    assert_eq!(rendered.matches("Shared group docs.").count(), 1);
    assert_eq!(rendered.matches("Separate group docs.").count(), 1);
    assert!(rendered.len() < source.len() + 512);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn every_language_primitive_matches_the_existing_source_signature() {
    use PrimitiveId::*;
    use qleisli::frontend::core::{PrimitiveId, primitive};
    // Independent small concrete ports cover both dynamic and fixed contracts;
    // the catalog supplies no source authority to these ordinary declarations.
    let cases = [
        (H, "unitary", 0, 1, "q:Q<Bit>", "Q<Bit>", "h(q)"),
        (
            Phase,
            "unitary",
            2,
            1,
            "q:Q<Bit>",
            "Q<Bit>",
            "phase[1,2](q)",
        ),
        (
            GlobalPhaseEighth,
            "unitary",
            0,
            1,
            "q:Q<(Bit,Unit)>",
            "Q<(Bit,Unit)>",
            "global_phase_eighth(q)",
        ),
        (Unit, "unitary", 0, 1, "v:Unit", "Q<Unit>", "unit(v)"),
        (Finish, "unitary", 0, 1, "q:Q<Unit>", "Unit", "finish(q)"),
        (
            Split,
            "unitary",
            0,
            1,
            "q:Q<(Bit,Unit)>",
            "(Q<Bit>,Q<Unit>)",
            "split(q)",
        ),
        (
            Join,
            "unitary",
            0,
            2,
            "a:Q<Bit>,b:Q<Unit>",
            "Q<(Bit,Unit)>",
            "join(a,b)",
        ),
        (MeasureZ, "observe", 0, 1, "q:Q<Bit>", "Bit", "measure_z(q)"),
        (
            Discard,
            "observe",
            0,
            1,
            "q:Q<(Bit,Unit)>",
            "Unit",
            "discard(q)",
        ),
        (
            TakeBit,
            "unitary",
            2,
            1,
            "q:Q<Bits<1>>",
            "(Q<Bit>,Q<Bits<0>>)",
            "take_bit[1,0](q)",
        ),
        (
            PutBit,
            "unitary",
            2,
            2,
            "a:Q<Bit>,z:Q<Bits<0>>",
            "Q<Bits<1>>",
            "put_bit[1,0](a,z)",
        ),
        (EmptyBits, "unitary", 0, 0, "", "Bits<0>", "empty_bits()"),
        (
            PrependBit,
            "unitary",
            1,
            2,
            "b:Bit,z:Bits<0>",
            "Bits<1>",
            "prepend_bit[0](b,z)",
        ),
    ];
    let root = SourceRoot::new("");
    assert_eq!(PRIMITIVES.len(), cases.len());
    assert_eq!(PrimitiveId::ALL.len(), cases.len());
    let mut visited = std::collections::BTreeSet::new();
    for (id, kind, natural_arity, arity, parameters, output, body) in cases {
        assert!(visited.insert(id));
        let descriptor = primitive(id);
        assert_eq!(descriptor.id, id);
        assert_eq!(descriptor.name(), id.spelling());
        assert_eq!(descriptor.natural_arity(), natural_arity);
        assert_eq!(descriptor.arity(), arity);
        assert_eq!(format!("{:?}", descriptor.kind()).to_lowercase(), kind);
        let basis_a = if matches!(id, GlobalPhaseEighth | Discard) {
            "(Bit,Unit)"
        } else {
            "Bit"
        };
        let signature = descriptor
            .signature
            .replace("Q<A>", &format!("Q<{basis_a}>"))
            .replace("(A,B)", "(Bit,Unit)")
            .replace("Q<B>", "Q<Unit>")
            .replace("n-1", "0")
            .replace("n+1", "1")
            .replace(
                "Bits<n>",
                if id == PrependBit {
                    "Bits<0>"
                } else {
                    "Bits<1>"
                },
            )
            .replace(' ', "");
        let input_types = parameters
            .split(',')
            .filter(|field| !field.is_empty())
            .map(|field| field.split_once(':').map_or(field, |(_, ty)| ty))
            .collect::<Vec<_>>()
            .join(",");
        assert_eq!(signature, format!("({input_types})->{output}"));

        root.write(
            "main.qli",
            &format!("{kind} fn f({parameters})->{output}{{{body}}}"),
        );
        check_project(&root.0).unwrap_or_else(|e| panic!("{}: {e}", id.spelling()));
    }
    assert!(
        PRIMITIVES
            .iter()
            .all(|descriptor| visited.contains(&descriptor.id))
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn raw_equality_retains_proof_identity_and_effect_diagnostics_use_narrower() {
    let root = SourceRoot::new(
        "use std::state::init0;\x20
        unitary fn id(q:Q<Bit>)->Q<Bit>{q}
        observe fn main()->Bit{measure_z(apply_contract(id,id,init0()))}",
    );
    let first = compile_project(&root.0).unwrap();
    let second = compile_project(&root.0).unwrap();
    assert_eq!(first.program(), &first.program().clone());
    assert_ne!(first.program(), second.program());
    let mut wrong = first.program().clone();
    wrong.declared_effect = qleisli::ir::Effect::Unitary;
    let error = common::accept(wrong).unwrap_err();
    assert_eq!(error.code, "invalid_ir");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn toffoli_flat_pattern_remains_a_located_compatibility_error_with_a_nested_repair() {
    let source = common::current_source_text(
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/review_v021/toffoli_flat/main.qli",
    );
    let root = SourceRoot::new(&source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(
        error.code,
        qleisli::frontend::compile::ErrorCode::TypeMismatch
    );
    assert_eq!(&source[error.span.start..error.span.end], "(a,b,c)");
    let repaired = source
        .replace("->(Q<Bit>,Q<Bit>,Q<Bit>)", "->((Q<Bit>,Q<Bit>),Q<Bit>)")
        .replace("let (a,b,c)", "let ((a,b),c)")
        .replace("    (a,b,c)", "    ((a,b),c)");
    root.write("main.qli", &repaired);
    check_project(&root.0).unwrap();
}
