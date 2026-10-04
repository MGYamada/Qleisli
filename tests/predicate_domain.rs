//! Independent finite predicate-domain checks; no general preservation claim.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::meaning::FiniteMeaning;
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::{BasisShape, Effect, QuantumPort, RawOp, RawProgram, WireId};
use qleisli::sim::{SimulationLimits, run_closed};
use std::path::Path;

fn source(case: &str) -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/predicate-domain-independent");
    let repaired = root.join("repaired").join(case).join("main.qli");
    std::fs::read_to_string(if repaired.exists() {
        repaired
    } else {
        root.join("sources").join(case).join("main.qli")
    })
    .unwrap()
}

fn tree(name: &str) -> BasisType {
    match name {
        "flat" => BasisType::Tuple(vec![BasisType::Bit; 3]),
        "left" => BasisType::pair(
            BasisType::pair(BasisType::Bit, BasisType::Bit),
            BasisType::Bit,
        ),
        "right" => BasisType::pair(
            BasisType::Bit,
            BasisType::pair(BasisType::Bit, BasisType::Bit),
        ),
        "pair" => BasisType::pair(BasisType::Bit, BasisType::Bit),
        _ => panic!("unknown test tree"),
    }
}

fn table_and_open_operation(source: &str, width: usize) -> (Vec<u16>, RawProgram) {
    let project = SourceRoot::new(source);
    let closed = compile_project(&project.0).unwrap();
    let operation = closed
        .program()
        .operations
        .iter()
        .find(|operation| {
            matches!(
                operation,
                RawOp::ComputeUseUncompute { .. } | RawOp::CertifiedCompute { .. }
            )
        })
        .expect("generated predicate operation")
        .clone();
    let (input, output, table) = match &operation {
        RawOp::ComputeUseUncompute {
            source,
            source_out,
            function,
            ..
        }
        | RawOp::CertifiedCompute {
            source,
            source_out,
            function,
            ..
        } => (*source, *source_out, function.clone()),
        _ => unreachable!(),
    };
    // Extract one generated operation into an untrusted open test proposal.
    // A fresh native function check below must validate this new boundary.
    let raw = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: input,
            wires: (0..width as u32).map(WireId).collect(),
            shape: BasisShape { bits: width as u8 },
        }],
        classical_inputs: vec![],
        operations: vec![operation],
        quantum_outputs: vec![output],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    (table, raw)
}

fn assert_complete_action(matrix: &Matrix, truth: &[u16]) {
    assert_eq!((matrix.rows(), matrix.cols()), (truth.len(), truth.len()));
    for row in 0..truth.len() {
        for (column, bit) in truth.iter().enumerate() {
            assert_eq!(
                matrix.get(row, column).unwrap(),
                if row == column {
                    Exact::phase(i32::from(*bit))
                } else {
                    Exact::zero()
                }
            );
        }
    }
    // Independently extend the actual exact action to two reference slices.
    // Unnormalized, unequal complex coefficients avoid a separability promise
    // and retain scalar phase. This is a bounded test of the extracted action.
    for reference in 0..2_i128 {
        let input = (0..truth.len())
            .map(|index| {
                let index = index as i128;
                Exact::new([index - 3, reference + 1, 2 - index, reference], 3).unwrap()
            })
            .collect::<Vec<_>>();
        for (row, bit) in truth.iter().enumerate() {
            let actual = input
                .iter()
                .enumerate()
                .fold(Exact::zero(), |sum, (column, value)| {
                    sum.add(matrix.get(row, column).unwrap().mul(*value).unwrap())
                        .unwrap()
                });
            assert_eq!(
                actual,
                Exact::phase(i32::from(*bit)).mul(input[row]).unwrap()
            );
        }
    }
}

fn check_action(case: &str, signature: BasisType, truth: &[u16]) {
    let source = source(case);
    let (table, actual) = table_and_open_operation(&source, signature.bits().unwrap());
    assert_eq!(
        table, truth,
        "{case}: complete low-axis-first predicate table"
    );
    let target = FiniteMeaning::phase(
        signature.clone(),
        truth.iter().map(|bit| *bit as u8).collect(),
    )
    .unwrap();
    let evidence = FunctionEvidence::check(
        signature,
        actual,
        target.target_ir().unwrap(),
        FunctionIdentity {
            implementation: case.into(),
            specification: "independent Boolean formula, diagonal zeta_8^f".into(),
            sources: vec![("main".into(), source)],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_complete_action(evidence.meaning(), truth);
}

#[test]
fn exact_flat_left_and_right_domains_preserve_ordered_tables_and_complex_actions() {
    // f(a,b,c) = (a AND NOT b) XOR c; a has weight 1, b 2, c 4.
    let truth = [0, 1, 0, 0, 1, 0, 1, 1];
    for shape in ["flat", "left", "right"] {
        for form in ["restricted", "certified"] {
            check_action(&format!("{form}-{shape}"), tree(shape), &truth);
        }
    }
}

#[test]
fn noninjective_and_and_constant_predicates_remain_legal_in_both_forms() {
    for form in ["restricted", "certified"] {
        check_action(&format!("and-{form}"), tree("pair"), &[0, 0, 0, 1]);
        check_action(&format!("constant-{form}"), tree("pair"), &[1, 1, 1, 1]);
    }
}

#[test]
fn equal_width_tree_substitution_rejects_at_each_predicate_use() {
    for form in ["restricted", "certified", "meaning"] {
        for actual in ["flat", "left", "right"] {
            for declared in ["flat", "left", "right"] {
                if actual == declared {
                    continue;
                }
                let text = source(&format!("wrong-{form}-{actual}-as-{declared}"));
                let project = SourceRoot::new(&text);
                let error = check_project(&project.0).unwrap_err();
                assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
                assert_eq!(
                    &text[error.span.start..error.span.end],
                    if form == "meaning" {
                        "labels"
                    } else {
                        "predicate"
                    },
                    "{error}"
                );
                if form == "certified" {
                    assert!(error.span.start > text.find("unitary fn mark").unwrap());
                }
            }
        }
    }
}

#[test]
fn nullary_and_multiple_parameters_are_not_implicitly_packed_for_computed_use() {
    for case in [
        "legacy-restricted-three",
        "legacy-certified-three",
        "nullary-restricted",
        "nullary-certified",
        "nullary-meaning",
    ] {
        let text = source(case);
        let error = check_project(&SourceRoot::new(&text).0).unwrap_err();
        assert_eq!(
            error.code,
            if case == "nullary-meaning" {
                ErrorCode::TypeMismatch
            } else {
                ErrorCode::Arity
            },
            "{case}: {error}"
        );
        assert!(matches!(
            &text[error.span.start..error.span.end],
            "predicate" | "yes" | "exponent"
        ));
        if case == "legacy-certified-three" {
            assert!(error.span.start > text.find("unitary fn mark").unwrap());
        }
    }
}

#[test]
fn ordinary_call_arity_and_meaning_output_tree_keep_their_own_contracts() {
    // Successful predicate programs above call the same ordinary 3-argument
    // helper from a unary pattern. No call packing or helper rewrite is needed.
    for form in ["restricted", "certified"] {
        let text = source(&format!("ordinary-{form}-packed"));
        let error = check_project(&SourceRoot::new(&text).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Arity, "{error}");
    }
    for case in ["ordinary-nullary-packed", "ordinary-unit-omitted"] {
        let text = source(case);
        let error = check_project(&SourceRoot::new(&text).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Arity, "{error}");
    }
    for shape in ["flat", "left", "right"] {
        let text = source(&format!("meaning-{shape}"));
        check_project(&SourceRoot::new(&text).0).unwrap();
        // The exponent interface is still exactly (Bit,(Bit,Bit)), not a flat
        // three-bit result. This edit changes type and expression together.
        let wrong = text.replace("->(Bit,(Bit,Bit)){(a,(b,c))}", "->(Bit,Bit,Bit){(a,b,c)}");
        let error = check_project(&SourceRoot::new(&wrong).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
    }
}

#[test]
fn zero_width_does_not_identify_unit_with_a_pair_of_units() {
    for form in ["restricted", "certified", "meaning"] {
        let text = source(&format!("zero-width-wrong-{form}"));
        let error = check_project(&SourceRoot::new(&text).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
        assert_eq!(&text[error.span.start..error.span.end], "wrong");
        if form == "certified" {
            assert!(error.span.start > text.find("unitary fn mark").unwrap());
        }
    }
}

#[test]
fn explicit_unit_keeps_controlled_eighth_phase_and_ordinary_nullary_helper_calls() {
    let p_one = (1.0 - std::f64::consts::FRAC_1_SQRT_2) / 2.0;
    for form in ["restricted", "certified", "meaning"] {
        let text = source(&format!("unit-{form}"));
        let program = compile_project(&SourceRoot::new(&text).0).unwrap();
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert!(
            (result[&vec![true]] - p_one).abs() < 1e-12,
            "{form}: {result:?}"
        );
        assert!(
            (result[&vec![false]] - (1.0 - p_one)).abs() < 1e-12,
            "{form}: {result:?}"
        );
    }
}
