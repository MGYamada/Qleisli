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

const REGISTER_SWAP_SOURCE: &str = include_str!(
    "fixtures/authoring_sessions/register-axis-routing-v030/attempt-01/swap_registers.qli"
);

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
            "{REGISTER_SWAP_SOURCE}\n\
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
            .expect_err("invalid axis pair");
        assert!(error.to_string().contains("natural premise"), "{error}");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_register_fold_matches_each_raw_iteration() {
    use qleisli::edition::Edition;
    use qleisli::interchange::qmatch::v5;

    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for (width, call) in [(0, "swap_registers[0]"), (2, "keep_registers[2]")] {
        let register_swap = if width == 0 { REGISTER_SWAP_SOURCE } else { "" };
        let source = format!(
            "{register_swap}
             unitary fn keep_registers[const n:Nat](a:Q<Bits<n>>,b:Q<Bits<n>>)
                                                    ->(Q<Bits<n>>,Q<Bits<n>>){{
                 qfor static i in 0..n carry (a,b)=(a,b) {{
                     let (x,a)=take_bit[n,i](a);
                     let (y,b)=take_bit[n,i](b);
                     yield (put_bit[n,i](x,a),put_bit[n,i](y,b));
                 }}
             }}
             pub unitary fn probe(q:Q<((Unit,Bits<{width}>),Bits<{width}>)>)
                                  ->Q<((Unit,Bits<{width}>),Bits<{width}>)>{{
                 let (pair,b)=split(q);
                 let (s,a)=split(pair);
                 let (s,a)=qmatch(s,a){{0=>{{a}}}};
                 let (a,b)={call}(a,b);
                 join(join(s,a),b)
             }}"
        );
        let selected = ParsedProgram::parse(
            Edition::E2026,
            BTreeMap::from([("main".into(), source.clone())]),
        )
        .unwrap()
        .instantiate_runtime_with_types(
            "main::probe",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel)
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        let program = selected.program();
        assert!(program.qmatch_source_checked());
        assert_eq!(
            program.output_ports()[0].wires,
            program.raw().quantum_inputs[0].wires
        );
        kernel.check_program(program).unwrap();

        let bits = BasisType::Bits(u32::try_from(width).unwrap());
        let basis = BasisType::pair(BasisType::pair(BasisType::Unit, bits.clone()), bits);
        let physical = u8::try_from(2 * width).unwrap();
        let table = (0..1 << physical).collect();
        FunctionEvidence::check(
            Edition::E2026,
            basis,
            program.raw().clone(),
            independent_basis_map(physical, table),
            FunctionIdentity {
                implementation: "main::probe".into(),
                specification: "independent register identity at exact phase +1".into(),
                sources: vec![("main".into(), source.clone())],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();

        let mut request = v5::Request::decode(program.request().unwrap()).unwrap();
        let offset = u32::try_from(source.find(call).unwrap()).unwrap();
        let fold = request
            .context
            .calls
            .iter_mut()
            .find(|call| call.position.offset == offset)
            .unwrap()
            .body
            .static_intervals
            .first_mut()
            .expect("the qfor must have an explicit partition");
        assert_eq!(fold.children.len(), 4 * width);
        if width == 0 {
            assert_eq!(fold.parent.count, 0);
            continue;
        }
        assert_eq!(fold.children[0].offset, fold.children[4].offset);
        assert_ne!(fold.children[0].start, fold.children[4].start);
        fold.children.swap(0, 4);
        let error = kernel
            .check_qmatch_source_v5(program.artifact(), &request.encode().unwrap())
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
        assert!(
            error.message.contains("Lean native checker rejected"),
            "{error}"
        );
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
    independent_basis_map(2, vec![0, 2, 1, 3])
}

fn independent_basis_map(bits: u8, table: Vec<u16>) -> RawProgram {
    let wires: Vec<_> = (0..u32::from(bits)).map(WireId).collect();
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: wires.clone(),
            shape: BasisShape { bits },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::LiftBasis {
            input: TokenId(0),
            output: TokenId(1),
            output_wires: wires,
            table,
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
