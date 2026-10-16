//! Independently requested exact equations for ordinary derived gate source.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::frontend::compile::compile_project;
use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
use qleisli::interchange::native::Proposal;
use qleisli::interchange::{RootInterface, Version};
use qleisli::ir::{BasisShape, CircuitAction, QuantumPort, RawOp, RawProgram};

fn actual(body: &str, width: usize) -> (RawProgram, BasisType) {
    let (ty, basis, result, close) = match width {
        1 => (
            "Bit",
            BasisType::Bit,
            "Bit",
            "measure_z(apply_contract(probe,probe,init0()))",
        ),
        2 => (
            "(Bit,Bit)",
            BasisType::pair(BasisType::Bit, BasisType::Bit),
            "(Bit,Bit)",
            "let q=apply_contract(probe,probe,join(init0(),init0()));let(a,b)=split(q);(measure_z(a),measure_z(b))",
        ),
        3 => (
            "(Bit,(Bit,Bit))",
            BasisType::pair(
                BasisType::Bit,
                BasisType::pair(BasisType::Bit, BasisType::Bit),
            ),
            "(Bit,(Bit,Bit))",
            "let q=apply_contract(probe,probe,join(init0(),join(init0(),init0())));let(a,q)=split(q);let(b,c)=split(q);(measure_z(a),(measure_z(b),measure_z(c)))",
        ),
        _ => panic!("only small independently specified interfaces"),
    };
    let source = format!(
        "use std::gate::{{t,s,sdg,tdg,z,x,cnot,toffoli,id,controlled_phase}};
         use std::transform::{{qft2,qft3}};
         use std::quantum::{{init0,split,join,phase_eighth}};
         use std::observe::measure_z;
         unitary fn probe(q:Q<{ty}>)->Q<{ty}>{{{body}}}
         pub observe fn main()->{result}{{{close}}}"
    );
    let accepted = compile_project(&SourceRoot::new(&source).0).unwrap();
    let receipt = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| {
            let RawOp::ApplyUnitary { steps, .. } = op else {
                return None;
            };
            steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. }
                    if evidence.identity().implementation == "main::probe" =>
                {
                    Some(evidence)
                }
                _ => None,
            })
        })
        .expect("actual ordinary provider body, not its self-comparison as oracle");
    assert!(
        receipt
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "std::gate"
                && text == include_str!("../stdlib/src/gate.qli"))
    );
    (receipt.implementation().clone(), basis)
}

fn request(
    raw: &RawProgram,
    basis: &BasisType,
    expected: &Matrix,
) -> Result<(), qleisli::interchange::Error> {
    let order: Vec<_> = (0..basis.bits().unwrap()).collect();
    request_ordered(raw, basis, expected, &order)
}

fn request_ordered(
    raw: &RawProgram,
    basis: &BasisType,
    expected: &Matrix,
    output_order: &[usize],
) -> Result<(), qleisli::interchange::Error> {
    let [input] = raw.quantum_inputs.as_slice() else {
        panic!("one exact Q owner")
    };
    let [output] = raw.quantum_outputs.as_slice() else {
        panic!("one exact returned Q owner")
    };
    let boundary = UnitaryBoundary::new(
        basis.clone(),
        input.clone(),
        QuantumPort {
            token: *output,
            // The required wire map comes from the source contract, independently
            // of the candidate. Fixed Fourier includes reversal; other gates
            // promise the same ordered wires.
            wires: output_order
                .iter()
                .map(|&index| input.wires[index])
                .collect(),
            shape: BasisShape {
                bits: basis.bits().unwrap() as u8,
            },
        },
    )
    .unwrap();
    let interface = RootInterface {
        input: basis.clone(),
        output: basis.clone(),
    };
    let proposal = Proposal::from_raw(raw, Some(&interface), Version::V2, None).unwrap();
    check_unitary(
        proposal.artifact(),
        &boundary,
        expected,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .map(|_| ())
}

fn diagonal(phases: &[u8]) -> Matrix {
    let n = phases.len();
    Matrix::new(
        n,
        n,
        (0..n * n)
            .map(|i| {
                if i / n == i % n {
                    Exact::phase(i32::from(phases[i / n]))
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap()
}

fn assert_no_workspace(raw: &RawProgram) {
    fn steps(steps: &[qleisli::ir::CircuitStep]) {
        for step in steps {
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                assert_no_workspace(evidence.implementation());
            }
        }
    }
    fn operations(ops: &[RawOp], input_wires: &[qleisli::ir::WireId]) {
        for op in ops {
            match op {
                RawOp::Init0 { .. } | RawOp::Reset { .. } => {
                    panic!("derived T introduces a physical wire")
                }
                RawOp::ApplyUnitary { steps: body, .. } => steps(body),
                RawOp::CertifiedCompute {
                    ancilla_wires,
                    use_steps,
                    logical_steps,
                    ..
                } => {
                    assert!(ancilla_wires.is_empty());
                    steps(use_steps);
                    steps(logical_steps);
                }
                RawOp::ComputeUseUncompute { ancilla_wires, .. } => {
                    assert!(ancilla_wires.is_empty());
                }
                RawOp::LiftBasis { output_wires, .. } => {
                    assert!(output_wires.iter().all(|wire| input_wires.contains(wire)));
                }
                RawOp::ClassicalBranch {
                    then_ops, else_ops, ..
                } => {
                    operations(then_ops, input_wires);
                    operations(else_ops, input_wires);
                }
                _ => {}
            }
        }
    }
    let input_wires: Vec<_> = raw
        .quantum_inputs
        .iter()
        .flat_map(|port| port.wires.iter().copied())
        .collect();
    operations(&raw.operations, &input_wires);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_phase_and_pauli_gates_satisfy_independent_exact_equations() {
    for (gate, phase) in [("t", 1), ("s", 2), ("sdg", 6), ("tdg", 7), ("z", 4)] {
        let (raw, basis) = actual(&format!("{gate}(q)"), 1);
        request(&raw, &basis, &diagonal(&[0, phase])).unwrap();
        assert!(request(&raw, &basis, &Matrix::identity(2).unwrap()).is_err());
        if gate == "t" {
            assert_eq!(raw.quantum_inputs[0].wires.len(), 1);
            assert_no_workspace(&raw);
        }
    }
    let (raw, basis) = actual("x(q)", 1);
    let expected = Matrix::new(
        2,
        2,
        vec![Exact::zero(), Exact::one(), Exact::one(), Exact::zero()],
    )
    .unwrap();
    request(&raw, &basis, &expected).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn derived_t_keeps_phase_under_adjoint_reference_and_nested_control() {
    for (body, width, phases) in [
        ("adjoint(t)(q)", 1, vec![0, 7]),
        ("let(r,q)=split(q);join(r,t(q))", 2, vec![0, 0, 1, 1]),
        (
            "let(c,q)=split(q);let(c,q)=controlled(t)(c,q);join(c,q)",
            2,
            vec![0, 0, 0, 1],
        ),
        (
            "let(c,q)=split(q);let(c,q)=controlled(controlled(t))(c,q);join(c,q)",
            3,
            vec![0, 0, 0, 0, 0, 0, 0, 1],
        ),
    ] {
        let (raw, basis) = actual(body, width);
        request(&raw, &basis, &diagonal(&phases)).unwrap();
        assert!(request(&raw, &basis, &Matrix::identity(phases.len()).unwrap()).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn a_global_scalar_on_bit_is_unitary_but_is_not_t() {
    let (raw, basis) = actual("phase_eighth(q)", 1);
    request(&raw, &basis, &diagonal(&[1, 1])).unwrap();
    let failure = request(&raw, &basis, &diagonal(&[0, 1])).unwrap_err();
    assert_eq!(failure.code, "contract");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_controlled_flips_have_independent_exact_permutations() {
    for (body, width, permutation) in [
        (
            "let(a,b)=split(q);let(a,b)=cnot(a,b);join(a,b)",
            2,
            vec![0, 3, 2, 1],
        ),
        (
            "let(a,q)=split(q);let(b,c)=split(q);let((a,b),c)=toffoli(a,b,c);join(a,join(b,c))",
            3,
            vec![0, 1, 2, 7, 4, 5, 6, 3],
        ),
    ] {
        let (raw, basis) = actual(body, width);
        let dimension = permutation.len();
        let expected = Matrix::new(
            dimension,
            dimension,
            (0..dimension * dimension)
                .map(|i| {
                    if i / dimension == permutation[i % dimension] {
                        Exact::one()
                    } else {
                        Exact::zero()
                    }
                })
                .collect(),
        )
        .unwrap();
        request(&raw, &basis, &expected).unwrap();
        assert!(request(&raw, &basis, &Matrix::identity(dimension).unwrap()).is_err());
        assert_no_workspace(&raw);
    }
    let (raw, basis) = actual("id[type(Bit)](q)", 1);
    request(&raw, &basis, &Matrix::identity(2).unwrap()).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_controlled_phase_has_independent_exact_phase_and_axis_equations() {
    for (body, width, phases) in [
        (
            "let(a,b)=split(q);let(a,b)=controlled_phase[1,3](a,b);join(a,b)",
            2,
            vec![0, 0, 0, 1],
        ),
        (
            "let(a,b)=split(q);let(a,b)=controlled_phase[0,0](a,b);join(a,b)",
            2,
            vec![0, 0, 0, 0],
        ),
        (
            "let(r,q)=split(q);let(a,b)=split(q);let(a,b)=controlled_phase[1,3](a,b);join(r,join(a,b))",
            3,
            vec![0, 0, 0, 0, 0, 0, 1, 1],
        ),
    ] {
        let (raw, basis) = actual(body, width);
        request(&raw, &basis, &diagonal(&phases)).unwrap();
        assert_no_workspace(&raw);
        let wrong = diagonal(&vec![1; phases.len()]);
        assert!(request(&raw, &basis, &wrong).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn bundled_fixed_fourier_keeps_positive_exact_coefficients_after_gate_migration() {
    // Existing fixed 2/3-bit contracts only; no general Fourier family.
    for (body, width, scale) in [
        ("qft2(q)", 2, Exact::new([1, 0, 0, 0], 1).unwrap()),
        (
            "let(a,q)=split(q);let(b,c)=split(q);let q=qft3(join(join(a,b),c));let(q,c)=split(q);let(a,b)=split(q);join(a,join(b,c))",
            3,
            Exact::new([0, 1, 0, 0], 2).unwrap(),
        ),
    ] {
        let (raw, basis) = actual(body, width);
        let dimension = 1usize << width;
        let coefficients = |negative| {
            (0..dimension * dimension)
                .map(|index| {
                    let exponent =
                        (8 * (index / dimension) * (index % dimension) / dimension) as i32;
                    scale
                        .mul(Exact::phase(if negative { -exponent } else { exponent }))
                        .unwrap()
                })
                .collect()
        };
        let expected = Matrix::new(dimension, dimension, coefficients(false)).unwrap();
        let reversed: Vec<_> = (0..width).rev().collect();
        request_ordered(&raw, &basis, &expected, &reversed).unwrap();
        let inverse = Matrix::new(dimension, dimension, coefficients(true)).unwrap();
        assert!(request_ordered(&raw, &basis, &inverse, &reversed).is_err());
        assert_no_workspace(&raw);
    }
}
