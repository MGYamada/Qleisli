//! The target adapter reuses existing sealed evidence and verifier rules.
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::meaning::{FiniteMeaning, MeaningEvidence};
use qleisli::contract::{BasisType, ContractError, DEFAULT_EXACT_WORK, FunctionIdentity};
use qleisli::ir::{CircuitAction, CircuitStep, RawOp};
use qleisli::verify;

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
    verify(attached.clone()).unwrap();
    let RawOp::ApplyUnitary { steps, .. } = &mut attached.operations[0] else {
        panic!()
    };
    let CircuitAction::Contract { indices, .. } = &mut steps[0].action else {
        panic!()
    };
    indices[0] = 1;
    assert!(verify(attached).is_err());
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
