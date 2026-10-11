//! Provisional two-Bit std::gate contracts and bounded routing comparisons.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact};
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
        "use std::quantum::{{split,join,cnot,init0}};use std::observe::measure_z;
         use std::gate::{{swap,permute_axes}};
         pub unitary fn probe(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{let(a,b)=split(q);{body}}}"
    )
}

fn selected_at(text: &str, entry: &str) -> AcceptedProgram {
    let program = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .unwrap()
        .instantiate(entry, BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
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

fn finite(text: &str) -> AcceptedProgram {
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
    Kernel::selected()
        .unwrap()
        .accept_raw(implementation)
        .unwrap()
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

#[test]
fn physical_swap_and_structural_routing_keep_distinct_wires_and_actual_work() {
    for (body, gates, reversed) in [
        (
            "let(a,b)=cnot(a,b);let(b,a)=cnot(b,a);let(a,b)=cnot(a,b);join(a,b)",
            3,
            false,
        ),
        ("join(b,a)", 0, true),
        ("let(a,b)=swap(a,b);join(a,b)", 3, false),
        ("permute_axes(join(a,b))", 0, true),
    ] {
        let text = source(body);
        let finite = finite(&text);
        let selected = selected(&text);
        for program in [&finite, &selected] {
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
                gates
            );
            assert!(program.raw().operations.iter().all(|op| matches!(
                op,
                RawOp::Split { .. } | RawOp::Join { .. } | RawOp::Cnot { .. }
            )));
            let evidence = compare(program, &text).unwrap();
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

#[test]
fn ordinary_std_gate_calls_preserve_explicit_access_and_ordered_outcomes() {
    use qleisli::sim::{SimulationLimits, run_closed};
    for body in [
        "let(a,b)=(init0(),x(init0()));swap(excl a,excl b);(measure_z(a),measure_z(b))",
        "let q=join(init0(),x(init0()));permute_axes(excl q);let(a,b)=split(q);(measure_z(a),measure_z(b))",
    ] {
        let text = format!(
            "use std::gate::{{swap,permute_axes}};use std::quantum::{{init0,x,join,split}};
             use std::observe::measure_z;pub observe fn main()->(Bit,Bit){{{body}}}"
        );
        for program in [
            compile_project(&SourceRoot::new(&text).0).unwrap(),
            selected_at(&text, "main::main"),
        ] {
            let result = run_closed(&program, SimulationLimits::default()).unwrap();
            assert_eq!(result.len(), 1);
            assert_eq!(result[&vec![true, false]], 1.0);
        }
    }
}

#[test]
fn native_valid_missing_or_wrong_swap_work_fails_the_independent_equation() {
    for body in ["join(a,b)", "let(a,b)=cnot(a,b);join(a,b)"] {
        let text = source(body);
        for program in [finite(&text), selected(&text)] {
            assert_eq!(
                compare(&program, &text).unwrap_err(),
                ContractError::EquationMismatch
            );
        }
    }
}
