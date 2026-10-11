//! The target adapter reuses existing sealed evidence and verifier rules.
mod common;
use common::accept;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::meaning::{FiniteMeaning, MeaningEvidence};
use qleisli::contract::{
    BasisType, CheckedContract, Circuit, Contract, ContractError, DEFAULT_EXACT_WORK, Encoding,
    FunctionIdentity,
};
use qleisli::ir::{BitControl, CircuitAction, CircuitStep, RawOp};

fn budget() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}
fn identity() -> FunctionIdentity {
    FunctionIdentity {
        implementation: "provider".into(),
        specification: "fixed target".into(),
        sources: vec![("provider".into(), "immutable source".into())],
    }
}

#[test]
fn complete_target_columns_include_unit_nested_trees_and_low_bit_control() {
    for basis in [
        BasisType::Unit,
        BasisType::Bit,
        BasisType::pair(
            BasisType::Unit,
            BasisType::pair(BasisType::Bit, BasisType::Bit),
        ),
    ] {
        let d = 1 << basis.bits().unwrap();
        let phases: Vec<_> = (0..d).map(|i| (i % 8) as u8).collect();
        let target = FiniteMeaning::phase(basis.clone(), phases.clone()).unwrap();
        let actual = target.matrix(&mut budget()).unwrap();
        for row in 0..d {
            for (col, phase) in phases.iter().enumerate() {
                assert_eq!(
                    actual.get(row, col),
                    Some(if row == col {
                        Exact::phase(i32::from(*phase))
                    } else {
                        Exact::zero()
                    })
                );
            }
        }
        let permutation: Vec<_> = (0..d as u16).rev().collect();
        let target = FiniteMeaning::permutation(basis, permutation.clone()).unwrap();
        let actual = target.matrix(&mut budget()).unwrap();
        for row in 0..d {
            for (col, output) in permutation.iter().enumerate() {
                assert_eq!(
                    actual.get(row, col),
                    Some(if row == usize::from(*output) {
                        Exact::one()
                    } else {
                        Exact::zero()
                    })
                );
            }
        }
    }
    let pair = BasisType::pair(BasisType::Bit, BasisType::Bit);
    let low = FiniteMeaning::permutation(pair.clone(), vec![0, 3, 2, 1]).unwrap();
    let high = FiniteMeaning::permutation(pair, vec![0, 1, 3, 2]).unwrap();
    assert_eq!(
        MeaningEvidence::check(high.target_ir().unwrap(), low, identity(), &mut budget())
            .unwrap_err(),
        ContractError::EquationMismatch
    );
}

#[test]
fn retained_target_rejects_stale_source_raw_axes_phase_and_exact_tree() {
    let target = FiniteMeaning::phase(BasisType::Bit, vec![0, 4]).unwrap();
    let raw = target.target_ir().unwrap();
    let evidence =
        MeaningEvidence::check(raw.clone(), target.clone(), identity(), &mut budget()).unwrap();
    evidence.check_binding(&raw, &target, &identity()).unwrap();
    let mut changed = identity();
    changed.sources[0].1.push('!');
    assert_eq!(
        evidence.check_binding(&raw, &target, &changed),
        Err(ContractError::EvidenceMismatch)
    );
    let minus = FiniteMeaning::phase(BasisType::Bit, vec![4, 0]).unwrap();
    assert_eq!(
        evidence.check_binding(&raw, &minus, &identity()),
        Err(ContractError::EvidenceMismatch)
    );
    let tree =
        FiniteMeaning::phase(BasisType::pair(BasisType::Bit, BasisType::Unit), vec![0, 4]).unwrap();
    assert_eq!(
        evidence.check_binding(&raw, &tree, &identity()),
        Err(ContractError::EvidenceMismatch)
    );
    let mut changed = raw.clone();
    changed.operations.clear();
    changed.quantum_outputs[0] = raw.quantum_inputs[0].token;
    assert_eq!(
        evidence.check_binding(&changed, &target, &identity()),
        Err(ContractError::EvidenceMismatch)
    );
    // Old consumers accept the receipt directly; adversarial attachment still
    // goes through their exact axis/control/evidence checks.
    let mut attached = raw;
    let RawOp::ApplyUnitary { steps, .. } = &mut attached.operations[0] else {
        panic!()
    };
    *steps = vec![CircuitStep {
        controls: vec![],
        action: CircuitAction::Contract {
            indices: vec![0],
            evidence: evidence.receipt(),
            adjoint: false,
        },
    }];
    accept(attached.clone()).unwrap();
    let RawOp::ApplyUnitary { steps, .. } = &mut attached.operations[0] else {
        panic!()
    };
    let CircuitAction::Contract { indices, .. } = &mut steps[0].action else {
        panic!()
    };
    indices[0] = 1;
    assert!(accept(attached).is_err());
    assert_eq!(
        evidence.receipt().meaning(),
        &target.matrix(&mut budget()).unwrap()
    );
}

#[test]
fn malformed_meanings_and_budget_exhaustion_cannot_issue_receipts() {
    assert!(FiniteMeaning::permutation(BasisType::Bit, vec![0, 0]).is_err());
    assert!(FiniteMeaning::permutation(BasisType::Bit, vec![0, 2]).is_err());
    assert!(FiniteMeaning::phase(BasisType::Bit, vec![0]).is_err());
    assert!(FiniteMeaning::phase(BasisType::Bit, vec![0, 8]).is_err());
    let target = FiniteMeaning::permutation(BasisType::Unit, vec![0]).unwrap();
    assert_eq!(
        target.matrix(&mut budget()).unwrap(),
        Matrix::identity(1).unwrap()
    );
    assert!(
        MeaningEvidence::check(
            target.target_ir().unwrap(),
            target,
            identity(),
            &mut Budget::new(0)
        )
        .is_err()
    );
}

#[test]
fn bits_receipts_preserve_atomic_identity_and_reject_false_phase() {
    for width in 0..=2 {
        let basis = BasisType::Bits(width);
        let dimension = 1usize << width;
        // A nontrivial scalar phase remains observable under later control,
        // including the zero-wire owner. It cannot be discarded as identity.
        let target = FiniteMeaning::phase(basis.clone(), vec![1; dimension]).unwrap();
        let raw = target.target_ir().unwrap();
        let evidence =
            MeaningEvidence::check(raw.clone(), target.clone(), identity(), &mut budget()).unwrap();
        evidence.check_binding(&raw, &target, &identity()).unwrap();
        let false_target = FiniteMeaning::phase(basis, vec![0; dimension]).unwrap();
        assert_eq!(
            MeaningEvidence::check(raw, false_target, identity(), &mut budget()).unwrap_err(),
            ContractError::EquationMismatch,
        );
    }
    for (atomic, same_width_tree) in [
        (BasisType::Bits(0), BasisType::Unit),
        (BasisType::Bits(1), BasisType::Bit),
        (
            BasisType::Bits(2),
            BasisType::pair(BasisType::Bit, BasisType::Bit),
        ),
        (
            BasisType::pair(BasisType::Bits(1), BasisType::Unit),
            BasisType::pair(BasisType::Unit, BasisType::Bits(1)),
        ),
    ] {
        let dimension = 1usize << atomic.bits().unwrap();
        assert_eq!(atomic.bits().unwrap(), same_width_tree.bits().unwrap());
        let target = FiniteMeaning::phase(atomic, vec![1; dimension]).unwrap();
        let raw = target.target_ir().unwrap();
        let evidence =
            MeaningEvidence::check(raw.clone(), target.clone(), identity(), &mut budget()).unwrap();
        let substituted = FiniteMeaning::phase(same_width_tree, vec![1; dimension]).unwrap();
        // This alternative is itself valid, but cannot substitute its basis
        // identity for the original immutable target of an accepted receipt.
        MeaningEvidence::check(
            substituted.target_ir().unwrap(),
            substituted.clone(),
            identity(),
            &mut budget(),
        )
        .unwrap();
        assert_eq!(
            evidence.check_binding(&raw, &substituted, &identity()),
            Err(ContractError::EvidenceMismatch),
        );
    }
}

#[test]
fn controlled_bits_zero_phase_is_an_exact_relative_phase() {
    let scalar = FiniteMeaning::phase(BasisType::Bits(0), vec![1]).unwrap();
    let evidence = MeaningEvidence::check(
        scalar.target_ir().unwrap(),
        scalar,
        identity(),
        &mut budget(),
    )
    .unwrap();
    for when_one in [false, true] {
        let circuit = Circuit::new(
            BasisType::Bits(1),
            vec![CircuitStep {
                controls: vec![BitControl { index: 0, when_one }],
                action: CircuitAction::Contract {
                    indices: vec![],
                    evidence: evidence.receipt(),
                    adjoint: false,
                },
            }],
        )
        .unwrap();
        // Independently specified columns: control exposes the scalar phase
        // on exactly one basis state, even though its target owns no wires.
        let entries = (0..2)
            .flat_map(|row| {
                (0..2).map(move |col| {
                    if row != col {
                        Exact::zero()
                    } else if (col == 1) == when_one {
                        Exact::phase(1)
                    } else {
                        Exact::one()
                    }
                })
            })
            .collect();
        let expected = Matrix::new(2, 2, entries).unwrap();
        let encoding = Encoding::identity(BasisType::Bits(1)).unwrap();
        let contract = Contract::new(
            encoding.clone(),
            encoding.clone(),
            expected.clone(),
            &mut budget(),
        )
        .unwrap();
        CheckedContract::check(circuit.clone(), contract, &mut budget()).unwrap();
        let false_identity = Contract::new(
            encoding.clone(),
            encoding,
            Matrix::identity(2).unwrap(),
            &mut budget(),
        )
        .unwrap();
        assert_eq!(
            CheckedContract::check(circuit, false_identity, &mut budget()).unwrap_err(),
            ContractError::EquationMismatch,
        );
    }
}
