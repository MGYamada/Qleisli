//! Exact finite contract checks against independently specified operators.

use qleisli_core::contract::exact::{Budget, Exact, ExactError, Matrix};
use qleisli_core::contract::{
    BasisType, CheckedContract, Circuit, Contract, ContractError, DEFAULT_EXACT_WORK, Encoding,
    MAX_CONTRACT_STEPS, check_computed,
};
use qleisli_core::ir::{
    BasisShape, BitControl, CircuitAction, CircuitStep, Effect, QuantumPort, RawOp, RawProgram,
    TokenId, WireId,
};
use qleisli_core::verify;

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}

fn pair() -> BasisType {
    BasisType::pair(BasisType::Bit, BasisType::Bit)
}

fn matrix(rows: usize, cols: usize, entry: impl Fn(usize, usize) -> Exact) -> Matrix {
    let mut entries = Vec::with_capacity(rows * cols);
    for row in 0..rows {
        for col in 0..cols {
            entries.push(entry(row, col));
        }
    }
    Matrix::new(rows, cols, entries).unwrap()
}

fn diagonal(phases: &[i32]) -> Matrix {
    matrix(phases.len(), phases.len(), |row, col| {
        if row == col {
            Exact::phase(phases[col])
        } else {
            Exact::zero()
        }
    })
}

fn flip() -> Matrix {
    matrix(2, 2, |row, col| Exact::integer(i128::from(row != col)))
}

fn hadamard() -> Matrix {
    matrix(2, 2, |row, col| {
        if row == 1 && col == 1 {
            Exact::inv_sqrt2().neg().unwrap()
        } else {
            Exact::inv_sqrt2()
        }
    })
}

fn monomial(indices: &[usize], permutation: &[u16], phases: &[u8]) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: indices.to_vec(),
            permutation: permutation.to_vec(),
            phases: phases.to_vec(),
        },
    }
}

fn x(axis: usize) -> CircuitStep {
    monomial(&[axis], &[1, 0], &[0, 0])
}

fn phase(axis: usize, exponent: u8) -> CircuitStep {
    monomial(&[axis], &[0, 1], &[0, exponent])
}

fn h(axis: usize) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Hadamard { target: axis },
    }
}

fn meaning(basis: BasisType, logical: Matrix) -> Contract {
    let encoding = Encoding::identity(basis).unwrap();
    Contract::new(encoding.clone(), encoding, logical, &mut work()).unwrap()
}

fn certify(basis: BasisType, steps: Vec<CircuitStep>, logical: Matrix) -> CheckedContract {
    CheckedContract::check(
        Circuit::new(basis.clone(), steps).unwrap(),
        meaning(basis, logical),
        &mut work(),
    )
    .unwrap()
}

fn copy_encoding() -> Encoding {
    // E|0> = |00>, E|1> = |11>, with the data bit in the low position.
    Encoding::new(
        BasisType::Bit,
        pair(),
        matrix(4, 2, |row, col| Exact::integer(i128::from(row == 3 * col))),
        &mut work(),
    )
    .unwrap()
}

#[test]
fn primitive_evidence_preserves_exact_phase() {
    let t = certify(BasisType::Bit, vec![phase(0, 1)], diagonal(&[0, 1]));
    assert_eq!(t.contract().logical(), &diagonal(&[0, 1]));
    let global_minus = Circuit::new(BasisType::Bit, vec![monomial(&[], &[0], &[4])]).unwrap();
    assert_eq!(
        CheckedContract::check(
            global_minus,
            meaning(BasisType::Bit, Matrix::identity(2).unwrap()),
            &mut work()
        )
        .unwrap_err(),
        ContractError::EquationMismatch
    );
}

#[test]
fn computed_phase_hh_and_simultaneous_x_use_the_same_equation() {
    // f(a,b) = a and not b exposes axis and predicate changes.
    check_computed(
        2,
        &[0, 1, 0, 0],
        &[phase(2, 4)],
        &[monomial(&[0, 1], &[0, 1, 2, 3], &[0, 4, 0, 0])],
    )
    .unwrap();
    check_computed(1, &[0, 1], &[h(1), h(1)], &[]).unwrap();
    check_computed(1, &[0, 1], &[x(0), x(1)], &[x(0)]).unwrap();
}

#[test]
fn computed_contract_rejects_auxiliary_leakage_wrong_meaning_and_predicate() {
    assert_eq!(
        check_computed(1, &[0, 1], &[x(1)], &[]),
        Err(ContractError::EquationMismatch)
    );
    assert_eq!(
        check_computed(1, &[0, 1], &[x(0), x(1)], &[]),
        Err(ContractError::EquationMismatch)
    );
    assert_eq!(
        check_computed(
            2,
            &[0, 0, 1, 0],
            &[phase(2, 4)],
            &[monomial(&[0, 1], &[0, 1, 2, 3], &[0, 4, 0, 0])]
        ),
        Err(ContractError::EquationMismatch)
    );
    assert_eq!(
        check_computed(
            2,
            &[0, 1, 0, 0],
            &[phase(2, 4)],
            &[monomial(&[1, 0], &[0, 1, 2, 3], &[0, 4, 0, 0])]
        ),
        Err(ContractError::EquationMismatch)
    );
    assert_eq!(
        check_computed(1, &[0, 1], &[phase(1, 4)], &[phase(0, 1)]),
        Err(ContractError::EquationMismatch)
    );
}

#[test]
fn encodings_and_logical_maps_must_be_isometric() {
    let repeated_columns = matrix(2, 2, |row, _| Exact::integer(i128::from(row == 0)));
    assert_eq!(
        Encoding::new(
            BasisType::Bit,
            BasisType::Bit,
            repeated_columns.clone(),
            &mut work()
        )
        .unwrap_err(),
        ContractError::NotIsometric
    );
    let encoding = Encoding::identity(BasisType::Bit).unwrap();
    assert_eq!(
        Contract::new(encoding.clone(), encoding, repeated_columns, &mut work()).unwrap_err(),
        ContractError::NotIsometric
    );
    assert!(matches!(
        Encoding::new(BasisType::Unit, BasisType::Bit, flip(), &mut work()),
        Err(ContractError::Type(_))
    ));
}

#[test]
fn entry_requires_exact_coordinates_even_for_the_same_image() {
    let identity = Encoding::identity(BasisType::Bit).unwrap();
    let shifted = Encoding::new(BasisType::Bit, BasisType::Bit, flip(), &mut work()).unwrap();
    let phased = Encoding::new(
        BasisType::Bit,
        BasisType::Bit,
        diagonal(&[4, 4]),
        &mut work(),
    )
    .unwrap();
    let theorem = CheckedContract::identity(identity.clone()).unwrap();
    assert_eq!(theorem.check_entry(Some(&identity)).unwrap(), &identity);
    assert_eq!(
        theorem.check_entry(None),
        Err(ContractError::EvidenceMismatch)
    );
    for other in [shifted, phased] {
        assert_eq!(
            theorem.check_entry(Some(&other)),
            Err(ContractError::EvidenceMismatch)
        );
        assert!(matches!(
            theorem.then(&CheckedContract::identity(other).unwrap(), &mut work()),
            Err(ContractError::Type(_))
        ));
    }
}

#[test]
fn exact_basis_tree_is_not_erased_by_equal_dimensions() {
    let bit_unit = BasisType::pair(BasisType::Bit, BasisType::Unit);
    let theorem = certify(BasisType::Bit, vec![x(0)], flip());
    let other = Encoding::identity(bit_unit.clone()).unwrap();
    assert_eq!(
        theorem.check_entry(Some(&other)),
        Err(ContractError::EvidenceMismatch)
    );
    assert!(matches!(
        theorem.then(&CheckedContract::identity(other).unwrap(), &mut work()),
        Err(ContractError::Type(_))
    ));
    assert!(matches!(
        CheckedContract::check(
            Circuit::new(bit_unit, vec![x(0)]).unwrap(),
            theorem.contract().clone(),
            &mut work()
        ),
        Err(ContractError::Type(_))
    ));
}

#[test]
fn sequential_proofs_use_application_order() {
    let first = certify(BasisType::Bit, vec![h(0)], hadamard());
    let next = certify(BasisType::Bit, vec![phase(0, 1)], diagonal(&[0, 1]));
    let composed = first.then(&next, &mut work()).unwrap();
    // T H: the second output row gets the phase, not the second input column.
    let expected = matrix(2, 2, |row, col| {
        hadamard()
            .get(row, col)
            .unwrap()
            .mul(Exact::phase(row as i32))
            .unwrap()
    });
    assert_eq!(composed.contract().logical(), &expected);
    assert_eq!(composed.circuit().matrix(&mut work()).unwrap(), expected);
    assert_eq!(composed.circuit().steps(), &[h(0), phase(0, 1)]);
}

#[test]
fn tensor_proofs_keep_low_order_axes_and_allow_a_correlated_reference() {
    let e = copy_encoding();
    let encoded_phase = CheckedContract::check(
        Circuit::new(pair(), vec![phase(1, 1)]).unwrap(),
        Contract::new(e.clone(), e, diagonal(&[0, 1]), &mut work()).unwrap(),
        &mut work(),
    )
    .unwrap();
    let reference = CheckedContract::identity(Encoding::identity(BasisType::Bit).unwrap()).unwrap();
    let theorem = encoded_phase.tensor(&reference, &mut work()).unwrap();
    assert_eq!(theorem.contract().logical(), &diagonal(&[0, 1, 0, 1]));
    let bell = matrix(4, 1, |row, _| {
        if row == 0 || row == 3 {
            Exact::inv_sqrt2()
        } else {
            Exact::zero()
        }
    });
    let encoded = theorem
        .contract()
        .input()
        .map()
        .compose(&bell, &mut work())
        .unwrap();
    let actual = theorem
        .circuit()
        .matrix(&mut work())
        .unwrap()
        .compose(&encoded, &mut work())
        .unwrap();
    let expected = matrix(8, 1, |row, _| match row {
        0 => Exact::inv_sqrt2(),
        7 => Exact::inv_sqrt2().mul(Exact::phase(1)).unwrap(),
        _ => Exact::zero(),
    });
    assert_eq!(actual, expected);
}

#[test]
fn adjoint_reverses_permutation_with_input_indexed_phases() {
    let step = monomial(&[0], &[1, 0], &[1, 3]);
    let logical = matrix(2, 2, |row, col| {
        if row != col {
            Exact::phase(if col == 0 { 1 } else { 3 })
        } else {
            Exact::zero()
        }
    });
    let theorem = certify(BasisType::Bit, vec![step], logical);
    let inverse = theorem.adjoint(&mut work()).unwrap();
    let expected = matrix(2, 2, |row, col| {
        if row != col {
            Exact::phase(if col == 0 { -3 } else { -1 })
        } else {
            Exact::zero()
        }
    });
    assert_eq!(inverse.contract().logical(), &expected);
    assert_eq!(inverse.circuit().matrix(&mut work()).unwrap(), expected);
    let identity = theorem.then(&inverse, &mut work()).unwrap();
    assert_eq!(identity.contract().logical(), &Matrix::identity(2).unwrap());
}

#[test]
fn non_surjective_logical_isometry_cannot_be_adjointed_or_controlled() {
    let zero = matrix(2, 1, |row, _| Exact::integer(i128::from(row == 0)));
    let input = Encoding::new(BasisType::Unit, BasisType::Bit, zero.clone(), &mut work()).unwrap();
    let output = Encoding::identity(BasisType::Bit).unwrap();
    let theorem = CheckedContract::check(
        Circuit::new(BasisType::Bit, vec![]).unwrap(),
        Contract::new(input, output, zero, &mut work()).unwrap(),
        &mut work(),
    )
    .unwrap();
    assert!(matches!(
        theorem.adjoint(&mut work()),
        Err(ContractError::Type(_))
    ));
    assert!(matches!(
        theorem.controlled(&mut work()),
        Err(ContractError::Type(_))
    ));
}

#[test]
fn controlled_encoded_phase_preserves_the_identity_arm() {
    let e = copy_encoding();
    let theorem = CheckedContract::check(
        Circuit::new(pair(), vec![phase(1, 1)]).unwrap(),
        Contract::new(e.clone(), e, diagonal(&[0, 1]), &mut work()).unwrap(),
        &mut work(),
    )
    .unwrap()
    .controlled(&mut work())
    .unwrap();
    assert_eq!(theorem.contract().logical(), &diagonal(&[0, 0, 0, 1]));
    assert_eq!(
        theorem.contract().input().map(),
        &matrix(8, 4, |row, col| Exact::integer(i128::from(
            row == (col & 1) + 6 * (col >> 1)
        )))
    );
    assert_eq!(
        theorem.circuit().matrix(&mut work()).unwrap(),
        diagonal(&[0, 0, 0, 0, 0, 1, 0, 1])
    );
}

#[test]
fn changed_encoding_blocks_control_even_when_the_logical_map_is_square() {
    let input = Encoding::identity(BasisType::Bit).unwrap();
    let output = Encoding::new(BasisType::Bit, BasisType::Bit, flip(), &mut work()).unwrap();
    let theorem = CheckedContract::check(
        Circuit::new(BasisType::Bit, vec![x(0)]).unwrap(),
        Contract::new(input, output, Matrix::identity(2).unwrap(), &mut work()).unwrap(),
        &mut work(),
    )
    .unwrap();
    assert!(matches!(
        theorem.controlled(&mut work()),
        Err(ContractError::Type(_))
    ));
    assert!(theorem.adjoint(&mut work()).is_ok());
}

#[test]
fn unit_has_scalar_phase_and_a_distinct_owned_type() {
    let scalar = certify(
        BasisType::Unit,
        vec![monomial(&[], &[0], &[4])],
        diagonal(&[4]),
    );
    let controlled = scalar.controlled(&mut work()).unwrap();
    assert_eq!(controlled.contract().logical(), &diagonal(&[0, 4]));
    assert_eq!(
        controlled.circuit().matrix(&mut work()).unwrap(),
        diagonal(&[0, 4])
    );
    assert_eq!(
        controlled.circuit().basis(),
        &BasisType::pair(BasisType::Bit, BasisType::Unit)
    );
    check_computed(0, &[1], &[phase(0, 4)], &[monomial(&[], &[0], &[4])]).unwrap();
    assert_eq!(
        check_computed(0, &[1], &[phase(0, 4)], &[]),
        Err(ContractError::EquationMismatch)
    );
}

#[test]
fn evidence_is_bound_to_full_circuit_and_contract() {
    let theorem = certify(BasisType::Bit, vec![x(0)], flip());
    theorem
        .check_binding(theorem.circuit(), theorem.contract())
        .unwrap();
    let equivalent_but_changed = Circuit::new(BasisType::Bit, vec![x(0), h(0), h(0)]).unwrap();
    assert_eq!(
        theorem.check_binding(&equivalent_but_changed, theorem.contract()),
        Err(ContractError::EvidenceMismatch)
    );
    assert_eq!(
        theorem.check_binding(
            theorem.circuit(),
            &meaning(BasisType::Bit, diagonal(&[0, 4]))
        ),
        Err(ContractError::EvidenceMismatch)
    );
}

#[test]
fn malformed_circuits_never_become_checked_evidence() {
    let mut overlapping = x(0);
    overlapping.controls.push(BitControl {
        index: 0,
        when_one: true,
    });
    let mut duplicate_controls = h(0);
    duplicate_controls.controls = vec![
        BitControl {
            index: 1,
            when_one: true,
        },
        BitControl {
            index: 1,
            when_one: false,
        },
    ];
    for step in [
        h(2),
        overlapping,
        duplicate_controls,
        monomial(&[0, 0], &[0, 1, 2, 3], &[0, 0, 0, 0]),
        monomial(&[0], &[0, 0], &[0, 0]),
        monomial(&[0], &[0, 2], &[0, 0]),
        monomial(&[0], &[0], &[0]),
        monomial(&[0], &[0, 1], &[0]),
        monomial(&[0], &[0, 1], &[0, 8]),
    ] {
        assert!(Circuit::new(pair(), vec![step]).is_err());
    }
}

#[test]
fn capacity_and_shared_work_exhaustion_fail_closed() {
    assert!(matches!(
        Circuit::new(BasisType::Bit, vec![h(0); MAX_CONTRACT_STEPS + 1]),
        Err(ContractError::Limit(_))
    ));
    let mut too_deep = BasisType::Unit;
    for _ in 0..34 {
        too_deep = BasisType::pair(BasisType::Unit, too_deep);
    }
    assert!(matches!(too_deep.bits(), Err(ContractError::Limit(_))));
    let mut too_wide = BasisType::Bit;
    for _ in 0..6 {
        too_wide = BasisType::pair(BasisType::Bit, too_wide);
    }
    assert!(matches!(too_wide.bits(), Err(ContractError::Limit(_))));
    let theorem = certify(BasisType::Bit, vec![h(0)], hadamard());
    assert_eq!(
        theorem.then(&theorem, &mut Budget::new(0)).unwrap_err(),
        ContractError::Arithmetic(ExactError::WorkLimit)
    );
    assert_eq!(
        CheckedContract::check(
            theorem.circuit().clone(),
            theorem.contract().clone(),
            &mut Budget::new(0)
        )
        .unwrap_err(),
        ContractError::Arithmetic(ExactError::WorkLimit)
    );
    assert!(matches!(
        check_computed(6, &[], &[], &[]),
        Err(ContractError::Limit(_))
    ));
    assert!(matches!(
        check_computed(1, &[0], &[], &[]),
        Err(ContractError::Type(_))
    ));
    assert!(matches!(
        check_computed(1, &[0, 2], &[], &[]),
        Err(ContractError::Type(_))
    ));
}

#[test]
fn rejected_deep_type_is_destroyed_without_recursive_stack_growth() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut tree = BasisType::Unit;
            for _ in 0..100_000 {
                tree = BasisType::pair(BasisType::Unit, tree);
            }
            assert!(matches!(
                Circuit::new(tree, vec![]),
                Err(ContractError::Limit(_))
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}

fn certified_program(
    bits: u8,
    function: Vec<u16>,
    use_steps: Vec<CircuitStep>,
    logical_steps: Vec<CircuitStep>,
) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: (0..u32::from(bits)).map(WireId).collect(),
            shape: BasisShape { bits },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::CertifiedCompute {
            source: TokenId(0),
            source_out: TokenId(1),
            ancilla_wires: vec![WireId(u32::from(bits))],
            function,
            use_steps,
            logical_steps,
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

#[test]
fn raw_ir_rechecks_actual_predicate_body_and_logical_evidence() {
    let good = certified_program(1, vec![0, 1], vec![x(0), x(1)], vec![x(0)]);
    verify(good.clone()).unwrap();
    let mut changed_body = good.clone();
    if let RawOp::CertifiedCompute { use_steps, .. } = &mut changed_body.operations[0] {
        *use_steps = vec![x(1)];
    }
    assert!(
        verify(changed_body)
            .unwrap_err()
            .message
            .contains("semantic contract")
    );
    let mut changed_meaning = good.clone();
    if let RawOp::CertifiedCompute { logical_steps, .. } = &mut changed_meaning.operations[0] {
        logical_steps.clear();
    }
    assert!(
        verify(changed_meaning)
            .unwrap_err()
            .message
            .contains("semantic contract")
    );
    let mut changed_predicate = good;
    if let RawOp::CertifiedCompute { function, .. } = &mut changed_predicate.operations[0] {
        *function = vec![0, 0];
    }
    assert!(
        verify(changed_predicate)
            .unwrap_err()
            .message
            .contains("semantic contract")
    );
}

#[test]
fn raw_ir_contract_diagnostic_identifies_an_exact_counterexample() {
    let leakage = certified_program(1, vec![0, 1], vec![x(1)], vec![]);
    let error = verify(leakage).unwrap_err();
    assert!(
        error
            .message
            .contains("input column 0, output row 0 (zero-based)")
    );
    assert!(error.message.contains("actual 0, expected 1"));

    let phase_error = certified_program(1, vec![0, 1], vec![phase(1, 1)], vec![phase(0, 4)]);
    let error = verify(phase_error).unwrap_err();
    assert!(
        error
            .message
            .contains("input column 1, output row 3 (zero-based)")
    );
    assert!(
        error
            .message
            .contains("actual (1/2^1)*sqrt(2) + (1/2^1)*i*sqrt(2), expected -1")
    );
}

#[test]
fn raw_ir_retains_zero_width_ownership_and_fresh_auxiliary_wires() {
    let good = certified_program(0, vec![0], vec![h(0), h(0)], vec![]);
    verify(good.clone()).unwrap();
    let mut lost_owner = good.clone();
    lost_owner.quantum_outputs.clear();
    assert!(
        verify(lost_owner)
            .unwrap_err()
            .message
            .contains("ownership")
    );
    let mut duplicated_owner = good.clone();
    duplicated_owner.quantum_outputs.push(TokenId(1));
    assert!(
        verify(duplicated_owner)
            .unwrap_err()
            .message
            .contains("twice")
    );
    let mut reused_source = good;
    reused_source.operations.push(RawOp::ApplyUnitary {
        input: TokenId(0),
        output: TokenId(2),
        steps: vec![],
    });
    assert!(verify(reused_source).is_err());
    let mut reused_wire = certified_program(1, vec![0, 1], vec![], vec![]);
    if let RawOp::CertifiedCompute { ancilla_wires, .. } = &mut reused_wire.operations[0] {
        *ancilla_wires = vec![WireId(0)];
    }
    assert!(verify(reused_wire).is_err());
    let mut missing_wire = certified_program(1, vec![0, 1], vec![], vec![]);
    if let RawOp::CertifiedCompute { ancilla_wires, .. } = &mut missing_wire.operations[0] {
        ancilla_wires.clear();
    }
    assert!(verify(missing_wire).is_err());
}
