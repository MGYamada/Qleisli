//! Bounded exact equations for the frozen #29 access/consume-return pairs.
//! These are finite source/receipt regressions, not general source or resource proofs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::frontend::compile::compile_project;
use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
use qleisli::interchange::native::Proposal;
use qleisli::interchange::{RootInterface, Version};
use qleisli::ir::{CircuitAction, Effect, QuantumPort, RawOp, RawProgram};

macro_rules! source {
    ($name:literal) => {
        include_str!(concat!(
            "fixtures/authoring_sessions/access-algorithms-v030/attempt-01/",
            $name,
            "/main.qli"
        ))
    };
}

#[derive(Clone, Copy, Debug)]
enum Algorithm {
    AddK,
    Equals,
    Grover,
    QpePrefix,
    Walk,
}

impl Algorithm {
    fn sources(self) -> [&'static str; 2] {
        match self {
            Self::AddK => [source!("add_k-access"), source!("add_k-explicit")],
            Self::Equals => [source!("equals-access"), source!("equals-explicit")],
            Self::Grover => [source!("grover-access"), source!("grover-explicit")],
            Self::QpePrefix => [source!("qpe_prefix-access"), source!("qpe_prefix-explicit")],
            Self::Walk => [source!("walk-access"), source!("walk-explicit")],
        }
    }

    fn basis(self) -> BasisType {
        let pair = BasisType::pair(BasisType::Bit, BasisType::Bit);
        if matches!(self, Self::Grover) {
            pair
        } else {
            BasisType::pair(pair, BasisType::Bit)
        }
    }

    // Fixed equations from the first context. No proposal, gate list, receipt
    // matrix or access/explicit comparison supplies these coefficients.
    fn expected(self) -> Matrix {
        let dimension = 1usize << self.basis().bits().unwrap();
        let half = Exact::new([1, 0, 0, 0], 1).unwrap();
        let root_half = Exact::new([0, 1, 0, 0], 1).unwrap();
        Matrix::new(
            dimension,
            dimension,
            (0..dimension * dimension)
                .map(|index| {
                    let row = index / dimension;
                    let col = index % dimension;
                    match self {
                        // |x,r> -> |x+3 mod 4,r>, with untouched reference.
                        Self::AddK => {
                            if row == ((((col & 3) + 3) % 4) | (col & 4)) {
                                Exact::one()
                            } else {
                                Exact::zero()
                            }
                        }
                        // |a,b,t> -> |a,b,t xor [a=b]>, for either flag input.
                        Self::Equals => {
                            let flag = if col & 1 == (col >> 1) & 1 { 4 } else { 0 };
                            if row == col ^ flag {
                                Exact::one()
                            } else {
                                Exact::zero()
                            }
                        }
                        // (2|s><s|-I) O_11: the marked INPUT column changes sign.
                        Self::Grover => {
                            if (row == col) != (col == 3) {
                                half.neg().unwrap()
                            } else {
                                half
                            }
                        }
                        // |a,b,t> -> sum_(c,d) (-1)^(ac+bd) i^(t(c+2d))
                        //                         |c,d,t>/2. No QFT is included.
                        Self::QpePrefix => {
                            if row & 4 != col & 4 {
                                return Exact::zero();
                            }
                            let sign = (col & 1) * (row & 1) + ((col >> 1) & 1) * ((row >> 1) & 1);
                            let phase = ((col >> 2) & 1) * ((row & 1) + 2 * ((row >> 1) & 1));
                            half.mul(Exact::phase((4 * sign + 2 * phase) as i32))
                                .unwrap()
                        }
                        // |c,p,r> -> sum_d (-1)^(cd)|d,p xor d,r>/sqrt(2).
                        Self::Walk => {
                            if row & 4 != col & 4
                                || ((row >> 1) & 1) != (((col >> 1) & 1) ^ (row & 1))
                            {
                                Exact::zero()
                            } else if (col & 1) * (row & 1) == 1 {
                                root_half.neg().unwrap()
                            } else {
                                root_half
                            }
                        }
                    }
                })
                .collect(),
        )
        .unwrap()
    }

    // Curated, valid-source semantic counterexamples, not repairs to history.
    fn counterexample(self, original: &str) -> String {
        let (before, after) = match self {
            Self::AddK => (
                "let (low,high) = cnot(low,high);\n    join(x(low),high)",
                "let low = x(low);\n    let (low,high) = cnot(low,high);\n    join(low,high)",
            ),
            Self::Equals => ("let flag = x(flag);", "let flag = flag;"),
            Self::Grover => (
                "mark(excl q);\n    reflect_uniform2(excl q);",
                "reflect_uniform2(excl q);\n    mark(excl q);",
            ),
            Self::QpePrefix => (
                "controlled_power[1](ctrl low,excl target);\n    controlled_power[2](ctrl high,excl target);",
                "controlled_power[2](ctrl low,excl target);\n    controlled_power[1](ctrl high,excl target);",
            ),
            Self::Walk => (
                "h(excl coin);\n    shift(ctrl coin,excl position);",
                "shift(ctrl coin,excl position);\n    h(excl coin);",
            ),
        };
        assert_eq!(original.matches(before).count(), 1, "{self:?}");
        original.replacen(before, after, 1)
    }
}

fn actual(algorithm: Algorithm, original: &str) -> RawProgram {
    let (result, body) = if matches!(algorithm, Algorithm::Grover) {
        (
            "(Bit,Bit)",
            "let q=apply_contract(probe,probe,join(init0(),init0()));
             let(a,b)=split(q);(measure_z(a),measure_z(b))",
        )
    } else {
        (
            "((Bit,Bit),Bit)",
            "let q=apply_contract(probe,probe,join(join(init0(),init0()),init0()));
             let(pair,c)=split(q);let(a,b)=split(pair);
             ((measure_z(a),measure_z(b)),measure_z(c))",
        )
    };
    let wrapper = format!(
        "use study::probe;use std::state::init0;
         pub observe fn main()->{result}{{{body}}}"
    );
    let root = SourceRoot::new(&wrapper);
    root.write("study.qli", original);
    let accepted = compile_project(&root.0)
        .unwrap_or_else(|error| panic!("{algorithm:?} provider failed before oracle: {error}"));
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
                    if evidence.identity().implementation == "study::probe" =>
                {
                    Some(evidence)
                }
                _ => None,
            })
        })
        .expect("actual study::probe provider, not self-comparison as an oracle");
    assert!(
        receipt
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "study" && text == original),
        "{algorithm:?}: the complete original source must bind the receipt"
    );
    let raw = receipt.implementation().clone();
    assert_eq!(raw.declared_effect, Effect::Unitary);
    assert!(raw.classical_inputs.is_empty() && raw.classical_outputs.is_empty());
    raw
}

fn request(
    raw: &RawProgram,
    basis: &BasisType,
    expected: &Matrix,
) -> Result<(), qleisli::interchange::Error> {
    let [input] = raw.quantum_inputs.as_slice() else {
        panic!("one complete input owner")
    };
    let [output] = raw.quantum_outputs.as_slice() else {
        panic!("one complete returned owner")
    };
    // These source contracts retain their ORIGINAL wire order. Do not extract
    // an output map from the candidate and thereby bless a routing error.
    let boundary = UnitaryBoundary::new(
        basis.clone(),
        input.clone(),
        QuantumPort {
            token: *output,
            wires: input.wires.clone(),
            shape: input.shape,
        },
    )
    .unwrap();
    let interface = RootInterface {
        input: basis.clone(),
        output: basis.clone(),
    };
    let proposal = Proposal::from_raw(raw, Some(&interface), Version::V2, None).unwrap();
    check_unitary(
        qleisli::edition::Edition::E2026,
        proposal.artifact(),
        &boundary,
        expected,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .map(|_| ())
}

fn incorrect_requests(expected: &Matrix) -> [Matrix; 2] {
    let dim = expected.rows();
    let phase = Matrix::new(
        dim,
        dim,
        expected
            .entries()
            .iter()
            .map(|x| x.neg().unwrap())
            .collect(),
    )
    .unwrap();
    let axes = Matrix::new(
        dim,
        dim,
        (0..dim * dim)
            .map(|index| {
                let row = index / dim;
                let swapped = (row & !3) | ((row & 1) << 1) | ((row >> 1) & 1);
                expected.entries()[swapped * dim + index % dim]
            })
            .collect(),
    )
    .unwrap();
    [phase, axes]
}

fn semantic_rejection(error: qleisli::interchange::Error, context: &str) {
    // Native transport preserves the separate limit/kernel/format/invalid_ir
    // categories. A local type error or unsupported/capacity refusal is no pass.
    assert_eq!(error.code, "contract", "{context}: {error}");
    assert_eq!(
        error.message, "Lean native checker rejected the artifact/request; no fallback",
        "{context}: {error}"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn access_and_explicit_algorithms_obey_independent_exact_equations() {
    for algorithm in [
        Algorithm::AddK,
        Algorithm::Equals,
        Algorithm::Grover,
        Algorithm::QpePrefix,
        Algorithm::Walk,
    ] {
        let basis = algorithm.basis();
        assert!(basis.bits().unwrap() <= 3);
        let expected = algorithm.expected();
        let [access, explicit] = algorithm.sources();
        for (variant, source) in [("access", access), ("explicit", explicit)] {
            let raw = actual(algorithm, source);
            request(&raw, &basis, &expected)
                .unwrap_or_else(|error| panic!("{algorithm:?} {variant}: {error}"));
            if variant == "access" {
                // Both wrong requests are full unitary matrices with the SAME
                // exact type. Require a contract mismatch, not a shape error.
                for (fault, wrong) in ["global phase", "ordered axes"]
                    .into_iter()
                    .zip(incorrect_requests(&expected))
                {
                    let error = request(&raw, &basis, &wrong).unwrap_err();
                    semantic_rejection(error, &format!("{algorithm:?} {fault}"));
                }
            }
        }
        // Compilation first establishes that each altered body remains a valid
        // unitary source/artifact. Only the independent requested equation must
        // then fail; a parser, ownership or missing-native failure is no pass.
        let changed = algorithm.counterexample(access);
        assert_ne!(changed, access);
        let raw = actual(algorithm, &changed);
        let error = request(&raw, &basis, &expected).unwrap_err();
        semantic_rejection(error, &format!("{algorithm:?} changed action"));
    }
}
