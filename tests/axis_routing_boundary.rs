//! Physical gate versus structural axis-map contracts and routing comparisons.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact};
use qleisli::contract::meaning::FiniteMeaning;
use qleisli::contract::{
    BasisType, ContractError, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity,
};
use qleisli::frontend::compile::{ParsedProgram, compile_project};
use qleisli::interchange::native::{AcceptedProgram, Kernel};
use qleisli::ir::{
    BasisShape, CircuitAction, Effect, QuantumPort, RawOp, RawProgram, TokenId, WireId,
};
use std::collections::BTreeMap;

fn source(body: &str) -> String {
    format!(
        "use std::gate::cnot; use std::state::init0;
         use std::gate::swap;use std::structure::permute_axes;
         pub unitary fn probe(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{let(a,b)=split(q);{body}}}"
    )
}

fn selected_at(text: &str, entry: &str) -> AcceptedProgram {
    let program = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), text.into())]),
    )
    .unwrap()
    .instantiate(entry, BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap();
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    let proposal = program
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

fn selected(text: &str) -> AcceptedProgram {
    selected_at(text, "main::probe")
}

fn checked_permutation(text: &str, basis: BasisType, map: Vec<u16>) -> AcceptedProgram {
    let entry = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), text.into())]),
    )
    .unwrap()
    .instantiate("main::probe", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap();
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let proposal = entry.lower_raw_with_kernel(&kernel, &mut budget).unwrap();
    let meaning = FiniteMeaning::permutation(basis, map).unwrap();
    proposal
        .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn register_swap_preserves_wire_frames_and_axis_permutations_compose_without_gates() {
    for width in 0..=3 {
        let source = format!(
            "use std::gate::swap_registers;\n\
             pub unitary fn probe(q:Q<(Bits<{width}>,Bits<{width}>)>)->Q<(Bits<{width}>,Bits<{width}>)>{{\
             let (a,b)=split(q); let (a,b)=swap_registers[{width}](a,b); join(a,b)}}"
        );
        let mask = (1 << width) - 1;
        let map = (0..1 << (2 * width))
            .map(|label| ((label & mask) << width) | (label >> width))
            .collect();
        let bits = BasisType::Bits(width);
        let checked = checked_permutation(&source, BasisType::pair(bits.clone(), bits), map);
        assert_eq!(checked.output_ports().len(), 1);
        assert_eq!(
            checked.output_ports()[0].wires,
            checked.raw().quantum_inputs[0].wires
        );
        assert_eq!(
            checked
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::ApplyUnitary { .. }))
                .count(),
            3 * usize::try_from(width).unwrap()
        );
    }

    let source = "use std::structure::transpose_axes;\n\
                  pub unitary fn probe(q:Q<Bits<3>>)->Q<Bits<3>>{\
                  transpose_axes[3,0,1](transpose_axes[3,1,2](q))}";
    let checked = checked_permutation(source, BasisType::Bits(3), vec![0, 2, 4, 6, 1, 3, 5, 7]);
    let input = &checked.raw().quantum_inputs[0].wires;
    assert_eq!(
        checked.output_ports()[0].wires,
        [input[2], input[0], input[1]]
    );
    assert!(
        checked
            .raw()
            .operations
            .iter()
            .all(|op| matches!(op, RawOp::Split { .. } | RawOp::Join { .. }))
    );

    for invalid in ["3,1,1", "3,2,1", "3,0,3"] {
        let source = format!(
            "use std::structure::transpose_axes; pub unitary fn probe(q:Q<Bits<3>>)->Q<Bits<3>>{{transpose_axes[{invalid}](q)}}"
        );
        let parsed = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source)]),
        );
        let error = parsed
            .and_then(|program| {
                program.instantiate("main::probe", BTreeMap::new(), BTreeMap::new())
            })
            .and_then(|entry| entry.elaborate())
            .err()
            .expect("invalid axis pair");
        assert!(error.to_string().contains("natural premise"), "{error}");
    }
}

fn finite(text: &str) -> (AcceptedProgram, String) {
    // The project entry is closed. Retain its open provider through the normal
    // function-evidence path. Self-comparison here is only producer consistency;
    // the separate independent_swap equation below decides the tested meaning.
    let closed = format!(
        "{text}pub observe fn main()->(Bit,Bit){{
         let q=apply_contract(probe,probe,join(init0(),init0()));
         let(a,b)=split(q);(measure_z(a),measure_z(b))}}"
    );
    let accepted = compile_project(&SourceRoot::new(&closed).0).unwrap();
    let implementation = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| {
            if let RawOp::ApplyUnitary { steps, .. } = op {
                steps.iter().find_map(|step| {
                    if let CircuitAction::Contract { evidence, .. } = &step.action {
                        Some(evidence.implementation().clone())
                    } else {
                        None
                    }
                })
            } else {
                None
            }
        })
        .expect("retained actual provider");
    let program = Kernel::selected(qleisli::edition::Edition::E2026)
        .unwrap()
        .accept_raw(implementation)
        .unwrap();
    (program, closed)
}

fn independent_swap() -> RawProgram {
    // Independently fixed little-endian equation |a,b> -> |b,a>, phase +1.
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0), WireId(1)],
            shape: BasisShape { bits: 2 },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::LiftBasis {
            input: TokenId(0),
            output: TokenId(1),
            output_wires: vec![WireId(0), WireId(1)],
            table: vec![0, 2, 1, 3],
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn compare(program: &AcceptedProgram, text: &str) -> Result<FunctionEvidence, ContractError> {
    FunctionEvidence::check(
        qleisli::edition::Edition::E2026,
        BasisType::pair(BasisType::Bit, BasisType::Bit),
        program.raw().clone(),
        independent_swap(),
        FunctionIdentity {
            implementation: "main::probe".into(),
            specification: "independent |a,b> -> |b,a>, phase +1".into(),
            sources: vec![("main".into(), text.into())],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn physical_swap_and_structural_routing_keep_distinct_wires_and_actual_work() {
    for (body, cnots, controlled_actions, reversed) in [
        (
            "let(a,b)=cnot(a,b);let(b,a)=cnot(b,a);let(a,b)=cnot(a,b);join(a,b)",
            0,
            3,
            false,
        ),
        ("join(b,a)", 0, 0, true),
        ("let(a,b)=swap(a,b);join(a,b)", 0, 3, false),
        ("permute_axes(join(a,b))", 0, 0, true),
    ] {
        let text = source(body);
        for (program, original_source) in [finite(&text), (selected(&text), text.clone())] {
            let input: Vec<_> = program
                .raw()
                .quantum_inputs
                .iter()
                .flat_map(|p| &p.wires)
                .copied()
                .collect();
            let output: Vec<_> = program
                .output_ports()
                .iter()
                .flat_map(|p| &p.wires)
                .copied()
                .collect();
            let expected: Vec<_> = if reversed {
                input.iter().rev().copied().collect()
            } else {
                input
            };
            assert_eq!(output, expected, "{text}");
            assert_eq!(
                program
                    .raw()
                    .operations
                    .iter()
                    .filter(|op| matches!(op, RawOp::Cnot { .. }))
                    .count(),
                cnots
            );
            assert_eq!(
                program
                    .raw()
                    .operations
                    .iter()
                    .filter(|op| matches!(op, RawOp::ApplyUnitary { .. }))
                    .count(),
                controlled_actions
            );
            // Ordinary CNOT retains controlled-X work in each ApplyUnitary.
            // Check the actual steps/receipts, including full phase and local
            // control/target order, rather than counting arbitrary pure actions.
            for operation in &program.raw().operations {
                let RawOp::ApplyUnitary { steps, .. } = operation else {
                    continue;
                };
                let matrix = qleisli::contract::Circuit::new(
                    BasisType::pair(BasisType::Bit, BasisType::Bit),
                    steps.clone(),
                )
                .unwrap()
                .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
                assert_eq!((matrix.rows(), matrix.cols()), (4, 4));
                for column in 0..4 {
                    let image = if column & 1 == 1 { column ^ 2 } else { column };
                    for row in 0..4 {
                        let expected = if row == image {
                            Exact::one()
                        } else {
                            Exact::zero()
                        };
                        assert_eq!(matrix.entries()[row * 4 + column], expected);
                    }
                }
            }
            assert!(program.raw().operations.iter().all(|op| matches!(
                op,
                RawOp::Split { .. }
                    | RawOp::Join { .. }
                    | RawOp::Cnot { .. }
                    | RawOp::ApplyUnitary { .. }
            )));
            // Nested ordinary gate receipts retain the entire original project
            // snapshot, including the finite entry wrapper. Bind that same
            // source here; the swap equation itself stays independently fixed.
            let evidence = compare(&program, &original_source).unwrap();
            // Check every exact complex coefficient, not probabilities or an
            // inverse round trip. Equality is under the stated output ordering.
            for row in 0..4 {
                for column in 0..4 {
                    let expected = if row == [0, 2, 1, 3][column] {
                        Exact::one()
                    } else {
                        Exact::zero()
                    };
                    assert_eq!(evidence.meaning().entries()[row * 4 + column], expected);
                }
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_std_gate_calls_preserve_explicit_access_and_ordered_outcomes() {
    use qleisli::sim::{SimulationLimits, run_closed};
    for body in [
        "let(a,b)=(init0(),x(init0()));swap(excl a,excl b);(measure_z(a),measure_z(b))",
        "let q=join(init0(),x(init0()));permute_axes(excl q);let(a,b)=split(q);(measure_z(a),measure_z(b))",
    ] {
        let text = format!(
            "use std::gate::swap;use std::structure::permute_axes;use std::state::init0; use std::gate::x;
             pub observe fn main()->(Bit,Bit){{{body}}}"
        );
        for program in [
            compile_project(&SourceRoot::new(&text).0).unwrap(),
            selected_at(&text, "main::main"),
        ] {
            let result = run_closed(&program, SimulationLimits::default()).unwrap();
            for (outcome, probability) in &result {
                let expected = if *outcome == vec![true, false] {
                    1.0
                } else {
                    0.0
                };
                assert!((probability - expected).abs() < 1e-12, "{result:?}");
            }
            assert!((result.get(&vec![true, false]).copied().unwrap_or(0.0) - 1.0).abs() < 1e-12);
            assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_valid_missing_or_wrong_swap_work_fails_the_independent_equation() {
    for body in ["join(a,b)", "let(a,b)=cnot(a,b);join(a,b)"] {
        let text = source(body);
        for (program, original_source) in [finite(&text), (selected(&text), text.clone())] {
            assert_eq!(
                compare(&program, &original_source).unwrap_err(),
                ContractError::EquationMismatch
            );
        }
    }
}
