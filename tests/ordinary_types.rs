//! Independent bounded checks for the canonical ordinary type/literal cutover.
//! Runtime observations are not a general source-preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ElaboratedProgram, ParsedProgram, SourceType};
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

macro_rules! source {
    ($name:literal) => {
        include_str!(concat!(
            "fixtures/frontend_v030/ordinary-types-independent/sources/",
            $name,
            "/main.qli"
        ))
    };
}

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

fn elaborate(source: &str) -> ElaboratedProgram {
    parsed(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn kernel() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("select the built native kernel"))
}

fn view(ty: &SourceType) -> String {
    if ty.kind() == "tuple" {
        assert_eq!(ty.width(), None);
        assert!(!ty.is_quantum());
        format!(
            "({})",
            ty.fields().iter().map(view).collect::<Vec<_>>().join(",")
        )
    } else {
        assert!(ty.fields().is_empty());
        format!("{}:{}:{}", ty.kind(), ty.width().unwrap(), ty.is_quantum())
    }
}

#[test]
fn finite_bit_values_copy_drop_call_and_use_zero_one_literals() {
    for source in [
        source!("bit-copy"),
        source!("bit-drop"),
        source!("bit-zero"),
        source!("bit-one"),
        source!("bit-call"),
        source!("bit-boolean-keywords"),
    ] {
        check_project(&SourceRoot::new(source).0).unwrap();
    }
}

#[test]
fn finite_boolean_actions_match_an_independent_truth_result() {
    let checked =
        compile_project(&SourceRoot::new(source!("canonical-actions-keywords")).0).unwrap();
    let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
    assert_eq!(
        distribution,
        BTreeMap::from([(vec![true, true, false], 1.0)])
    );
    // The program exercises a copy, both Bit numerals, not/xor/and, a call and a branch.
    assert!(checked.raw().quantum_inputs.is_empty());
    assert!(checked.raw().quantum_outputs.is_empty());
    assert_eq!(checked.raw().classical_outputs.len(), 3);
}

#[test]
fn finite_measurement_and_feedforward_keep_their_correlated_action() {
    let checked = compile_project(&SourceRoot::new(source!("canonical-feedback")).0).unwrap();
    let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 2);
    for bits in [vec![false, false], vec![true, true]] {
        assert!((distribution[&bits] - 0.5).abs() < 1e-12);
    }
}

#[test]
fn source_bearing_native_evidence_retains_the_actual_canonical_source() {
    let source = source!("canonical-retained-source");
    let checked = compile_project(&SourceRoot::new(source).0).unwrap();
    let evidence = checked
        .raw()
        .operations
        .iter()
        .flat_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => steps
                .iter()
                .filter_map(|step| match &step.action {
                    CircuitAction::Contract { evidence, .. } => Some(evidence),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect::<Vec<_>>();
    assert_eq!(evidence.len(), 1);
    assert!(
        evidence[0]
            .identity()
            .sources
            .iter()
            .any(|(module, text)| module == "main" && text == source)
    );
    let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
    assert_eq!(distribution, BTreeMap::from([(vec![true], 1.0)]));
}

#[test]
fn obsolete_spellings_and_other_bit_numerals_are_rejected_by_common_syntax() {
    for source in [
        source!("obsolete-cbit"),
        source!("obsolete-cbits"),
        source!("obsolete-false"),
        source!("obsolete-true"),
        source!("obsolete-unit-type"),
        source!("bit-two"),
    ] {
        let error = parse_module(source).unwrap_err();
        assert!(
            error.span.start < error.span.end && error.span.end <= source.len(),
            "{error:?}"
        );
        assert!(!error.message.is_empty());
    }
    // The literal cutover does not reinterpret explicit static naturals as Bit.
    parsed("pub unitary fn f[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { if static n < 2 { q } else { q } }")
        .instantiate("main::f", BTreeMap::from([("n".into(), 2)]), BTreeMap::new())
        .unwrap().elaborate().unwrap();
}

#[test]
fn finite_quantum_and_ordinary_values_never_coerce_at_return_call_or_guard() {
    for source in [
        source!("quantum-to-bit"),
        source!("bit-to-quantum"),
        source!("ordinary-quantum-call"),
        source!("quantum-guard"),
        "pub unitary fn f(q: Q<Unit>) -> Unit { q }",
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{source}: {error}");
    }
    assert!(parse_module(source!("quantum-nested")).is_err());
}

#[test]
fn sized_exact_type_errors_are_distinct_from_profile_rejections() {
    for source in [
        source!("quantum-to-bit"),
        source!("bit-to-quantum"),
        source!("ordinary-quantum-call"),
        source!("unit-vs-bits-zero"),
        source!("bit-vs-bits-one"),
        source!("quantum-bit-vs-bits-one"),
        source!("unused-mismatch"),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "type", "{source}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().end <= source.len());
    }
}

#[test]
fn public_type_view_retains_exact_ordinary_quantum_and_tuple_constructors() {
    let graph = elaborate(source!("accessors"));
    let root = &graph.definitions()[graph.root()];
    assert_eq!(
        root.inputs()
            .iter()
            .map(|v| view(v.ty()))
            .collect::<Vec<_>>(),
        [
            "bit:1:false",
            "bits:1:false",
            "bits:0:false",
            "unit:0:false",
            "bit:1:true",
            "bits:1:true",
            "bits:0:true"
        ]
    );
    assert_eq!(
        view(root.output().ty()),
        "((bit:1:false,bits:1:false),(bits:0:false,unit:0:false),(bit:1:true,bits:1:true,bits:0:true))"
    );
    assert_ne!(root.inputs()[0].ty(), root.inputs()[1].ty());
    assert_ne!(root.inputs()[2].ty(), root.inputs()[3].ty());
    assert_ne!(root.inputs()[0].ty(), root.inputs()[4].ty());
    assert_ne!(root.inputs()[4].ty(), root.inputs()[5].ty());
    assert!(root.inputs()[3].identity().is_none());
    assert!(root.inputs()[6].identity().is_some());
    assert_eq!(
        root.inputs()[6].identity(),
        root.output().fields()[2].fields()[2].identity()
    );
}

#[test]
fn sized_symbolic_sizes_preserve_ordinary_bits_after_small_substitution() {
    let program = parsed(source!("symbolic-word"));
    for n in [0, 2] {
        let graph = program
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let root = &graph.definitions()[graph.root()];
        assert_eq!(root.inputs()[0].ty(), root.output().ty());
        assert_eq!(root.output().ty().kind(), "bits");
        assert_eq!(root.output().ty().width(), Some(n + 1));
        assert!(!root.output().ty().is_quantum());
    }
}

#[test]
fn sized_unit_copy_has_no_owner_and_really_lowers_to_zero_value_ports() {
    let graph = elaborate(source!("unit-copy"));
    let root = &graph.definitions()[graph.root()];
    assert_eq!(view(root.inputs()[0].ty()), "unit:0:false");
    assert_eq!(view(root.output().ty()), "(unit:0:false,unit:0:false)");
    assert!(root.inputs()[0].identity().is_none());
    assert!(
        root.output()
            .fields()
            .iter()
            .all(|v| v.identity().is_none())
    );
    let proposal = graph.lower().unwrap();
    assert!(!proposal.is_instrument());
    let checked = kernel()
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = [[0.3, 0.2], [-0.4, 0.1]];
    let actual = checked
        .execute_pure(
            &input,
            2,
            ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    assert_eq!(actual.amplitudes, input);
}

#[test]
fn sized_unit_patterns_consume_only_actual_unit_values() {
    let proposal = elaborate(source!("unit-pattern-consume")).lower().unwrap();
    kernel()
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let graph =
        elaborate("pub unitary fn f(q: Q<Bit>) -> Q<Bit> { let (((),q),()) = (((),q),()); q }");
    assert_eq!(
        graph.definitions()[graph.root()].output().ty().kind(),
        "bit"
    );
    for source in [
        "pub unitary fn f(q: Q<Bits<0>>) -> Unit { let () = q; () }",
        "pub unitary fn f(b: Bits<0>) -> Unit { let () = b; () }",
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "type", "{error}");
    }
}

#[test]
fn unit_returning_quantum_consumption_survives_lowering_and_source_event_checks() {
    let proposal = elaborate(source!("unit-drain-readout")).lower().unwrap();
    let checked = kernel()
        .check_instrument_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let validation = proposal
        .validate_initialization_moves_native(&checked)
        .unwrap();
    assert_eq!(validation.events(), 4);
    assert_eq!(
        proposal
            .source_events()
            .iter()
            .map(|e| e.kind())
            .collect::<Vec<_>>(),
        ["pure", "observe", "empty_bits", "prepend_bit"]
    );
    let consumed = &proposal.source_events()[0];
    let before = consumed.input_frame().collect::<Vec<_>>();
    let after = consumed.output_frame().collect::<Vec<_>>();
    assert_eq!(before.len(), 2);
    assert_eq!(after.len(), 1);
    let empty_owner = before
        .iter()
        .find(|p| p.axes().is_empty())
        .expect("retain the zero-axis owner until its consume operation");
    assert!(!empty_owner.is_bit());
    assert!(after.iter().all(|p| p.owner() != empty_owner.owner()));
    let input = [[0.3, 0.2], [-0.4, 0.1], [0.0, 0.7], [0.5, -0.2]];
    let output = checked
        .execute_instrument(
            &input,
            2,
            ExecutionLimits {
                max_amplitudes: 64,
                max_steps: 1000,
            },
        )
        .unwrap();
    assert_eq!(
        output.branches,
        vec![vec![input[0], input[2]], vec![input[1], input[3]]]
    );
}

#[test]
fn quantum_zero_axis_owners_still_cannot_be_copied_or_dropped() {
    for source in [
        source!("quantum-zero-copy"),
        source!("quantum-zero-drop"),
        source!("quantum-copy"),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "ownership", "{source}: {error}");
    }
}

#[test]
fn existing_execution_profile_limits_remain_explicit() {
    let finite = check_project(&SourceRoot::new(source!("ordinary-word")).0).unwrap_err();
    assert_eq!(finite.code, ErrorCode::Unsupported);
    for source in [source!("bit-copy"), source!("ordinary-word")] {
        let error = elaborate(source).lower().unwrap_err();
        assert_eq!(error.code(), "unsupported");
        assert!(
            error.message().contains("classical entry values"),
            "{error}"
        );
    }
    let program = elaborate(source!("bit-zero"));
    program.lower_raw().unwrap();
    assert_eq!(program.lower().unwrap_err().code(), "unsupported");
    // Runtime if is valid original source but remains outside the selected
    // concrete projection, even with supported ordinary Boolean operands.
    let source = source!("bit-boolean-keywords");
    let program = parsed(source);
    assert_eq!(program.source("main"), Some(source));
    assert_eq!(program.syntax("main"), Some(&parse_module(source).unwrap()));
    let error = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert_eq!(error.module(), Some("main"));
    assert_eq!(
        error.message(),
        "sized preparation profile: unsupported runtime expression"
    );
    assert_eq!(
        &source[error.span().start..error.span().end],
        "if a { not b } else { a xor b }"
    );
    let program = elaborate(source!("quantum-unit"));
    program.lower().unwrap();
    // Raw lowering now supports this exact zero-width quantum interface.
    // Physical width zero must still retain the source's logical Unit owner.
    let proposal = program.lower_raw().unwrap();
    let native = qleisli::interchange::native::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("select the built native kernel"),
    );
    let checked = native.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&checked).unwrap();
    let raw = checked.raw();
    assert_eq!(raw.quantum_inputs.len(), 1);
    assert!(raw.quantum_inputs[0].wires.is_empty());
    assert_eq!(raw.quantum_inputs[0].shape.bits, 0);
    assert_eq!(raw.quantum_outputs, vec![raw.quantum_inputs[0].token]);
    assert_eq!(
        checked.root_interface(),
        Some(&qleisli::interchange::RootInterface {
            input: qleisli::contract::BasisType::Unit,
            output: qleisli::contract::BasisType::Unit,
        })
    );
    let error = elaborate(source!("unit-forget-readout"))
        .lower()
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(
        error.message().contains("retain every observation"),
        "{error}"
    );
}
