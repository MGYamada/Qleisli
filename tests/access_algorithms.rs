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

// Selected roots keep the same original computed scope and fresh native checks.
mod selected_grover_computed_api {
    use super::common::SourceRoot;
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
    use qleisli::edition::Edition;
    use qleisli::frontend::compile::ParsedProgram;
    use qleisli::frontend::project::{ModuleOrigin, Project};
    use qleisli::interchange::carrier::Atom as Basis;
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
    use qleisli::interchange::native::{Kernel, Proposal};
    use qleisli::interchange::runtime_root::{Atom, Storage};
    use qleisli::interchange::{RootInterface, Version};
    use qleisli::ir::{
        Effect, ProtectedBit, ProtectedRegion, ProtectedUse, QuantumPort, RawOp, RawProgram,
        SingleGate,
    };

    const ACCESS: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/authoring_sessions/access-algorithms-v030/attempt-01/grover-access/main.qli"
    ));
    const EXPLICIT: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/authoring_sessions/access-algorithms-v030/attempt-01/grover-explicit/main.qli"
    ));

    #[test]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn selected_computed_cli_checks_open_roots_and_runs_closed_roots() {
        for original in [ACCESS, EXPLICIT] {
            let root = SourceRoot::new(original);
            for (action, entry, expected_scope) in [
                ("check", "probe", "finite-runtime-root-v2"),
                ("run", "main", "finite-ordinary-root-v2"),
            ] {
                let output = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"))
                    .args([action, "--format=json", "--ir-profile=raw"])
                    .arg(format!("--entry=main::{entry}"))
                    .arg(format!(
                        "--module=main={}",
                        root.0.join("main.qli").display()
                    ))
                    .arg(format!(
                        "--lean-kernel={}",
                        std::path::PathBuf::from(std::env::var_os("QLEISLI_KERNEL").unwrap())
                            .display()
                    ))
                    .output()
                    .unwrap();
                assert!(output.status.success(), "{output:?}");
                assert!(output.stderr.is_empty(), "{output:?}");
                let text = String::from_utf8(output.stdout).unwrap();
                for expected in [
                    format!("\"command\":\"{action}\""),
                    format!("\"scope\":\"{expected_scope}\""),
                    "\"outcome\":\"ok\"".into(),
                    "\"request_checked\":true".into(),
                    "\"source_preservation_verified\":false".into(),
                    "\"source_meaning_verified\":false".into(),
                ] {
                    assert!(text.contains(&expected), "missing {expected}: {text}");
                }
                if action == "run" {
                    assert!(
                        text.contains(
                            "\"distribution\":[{\"bits\":[true,true],\"probability\":1}]"
                        ),
                        "{text}"
                    );
                }
            }
        }
    }

    // Ordered basis index = a + 2*b. This oracle is fixed independently of
    // either compiled source: G = (2|s><s| - I) O_marked, |s> = (1,1,1,1)/2.
    fn grover(marked: usize) -> Matrix {
        let half = Exact::new([1, 0, 0, 0], 1).unwrap();
        Matrix::new(
            4,
            4,
            (0..16)
                .map(|index| {
                    let (row, col) = (index / 4, index % 4);
                    if (row == col) != (col == marked) {
                        half.neg().unwrap()
                    } else {
                        half
                    }
                })
                .collect(),
        )
        .unwrap()
    }

    fn exact_request(
        raw: &RawProgram,
        basis: BasisType,
        expected: &Matrix,
    ) -> Result<(), qleisli::interchange::Error> {
        let [input] = raw.quantum_inputs.as_slice() else {
            panic!("one input owner")
        };
        let [output] = raw.quantum_outputs.as_slice() else {
            panic!("one output owner")
        };
        // Fix the source's ORIGINAL wire order, never infer a desired map from
        // the candidate output. The output token alone is an SSA identifier.
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
        let proposal = Proposal::from_raw(
            raw,
            Some(&RootInterface {
                input: basis.clone(),
                output: basis,
            }),
            Version::V2,
            None,
        )
        .unwrap();
        check_unitary(
            Edition::E2026,
            proposal.artifact(),
            &boundary,
            expected,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .map(|_| ())
    }

    fn semantic_refusal(result: Result<(), qleisli::interchange::Error>) {
        let error = result.expect_err("incorrect exact action must be refused");
        // A capacity, unsupported, decode, interface or process failure is not
        // evidence that the independently fixed meaning was compared.
        assert_eq!(error.code, "contract", "{error:?}");
        assert_eq!(
            error.message,
            "Lean native checker rejected the artifact/request; no fallback"
        );
    }

    #[test]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn selected_grover_preserves_computed_scope_and_fixed_exact_action() {
        let kernel = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native test gate"),
            Edition::E2026,
        );
        let expected = grover(3);
        let pair = BasisType::pair(BasisType::Bit, BasisType::Bit);
        let negative_phase = Matrix::new(
            4,
            4,
            expected
                .entries()
                .iter()
                .map(|x| x.neg().unwrap())
                .collect(),
        )
        .unwrap();
        let z = Matrix::new(
            2,
            2,
            vec![
                Exact::one(),
                Exact::zero(),
                Exact::zero(),
                Exact::one().neg().unwrap(),
            ],
        )
        .unwrap();

        for (label, original) in [("access", ACCESS), ("explicit", EXPLICIT)] {
            // Keep the complete first source, including its observe main, unchanged.
            // This selected API experiment adds no source wrapper or replacement AST.
            let root = SourceRoot::new(original);
            let project =
                Project::load(&root.0).unwrap_or_else(|error| panic!("{label}: load: {error:?}"));
            let parsed = ParsedProgram::parse(
                project.edition(),
                project
                    .modules
                    .iter()
                    .filter(|(_, module)| module.origin == ModuleOrigin::Local)
                    .map(|(name, module)| (name.clone(), module.source.clone()))
                    .collect(),
            )
            .unwrap_or_else(|error| panic!("{label}: parse: {error:?}"));
            // ParsedProgram itself inserts checked bundled modules. Passing those
            // modules again as local inputs would create duplicate definitions.
            assert_eq!(parsed.source("main"), Some(original));
            for entry in [
                "std::reflection::reflect_uniform2",
                "main::probe",
                "main::main",
            ] {
                assert!(parsed.requires_typed_runtime_transport(entry).unwrap());
            }
            // Dormant computed declarations do not redirect unrelated roots.
            assert!(
                !parsed
                    .requires_typed_runtime_transport("std::gate::x")
                    .unwrap()
            );
            let instance = parsed
                .instantiate_runtime_with_types(
                    "main::probe",
                    Default::default(),
                    Default::default(),
                    Default::default(),
                )
                .unwrap_or_else(|error| panic!("{label}: instantiate: {error:?}"));
            let selected = instance
                .compile_runtime_with_kernel(&kernel)
                .unwrap_or_else(|error| panic!("{label}: selected runtime: {error:?}"));
            assert_eq!(selected.source().program().source("main"), Some(original));
            assert_eq!(selected.runtime_parameters(), 1);
            let accepted = selected.program();
            let request = accepted.runtime_result().expect("full typed runtime root");
            let atoms = vec![
                Atom::Quantum,
                Atom::Finite(Basis::Pair),
                Atom::Finite(Basis::Bit),
                Atom::Finite(Basis::Bit),
            ];
            assert_eq!(request.module, "main");
            assert_eq!(request.declaration, "probe");
            assert_eq!(request.parameters, vec![atoms.clone()]);
            assert_eq!(request.result, atoms);
            assert_eq!(request.public_effect, Effect::Unitary);

            let raw = accepted.raw();
            let [input] = raw.quantum_inputs.as_slice() else {
                panic!("two-bit owner")
            };
            let [output] = raw.quantum_outputs.as_slice() else {
                panic!("returned owner")
            };
            assert_eq!(input.shape.bits, 2);
            assert_eq!(input.wires.len(), 2);
            assert!(raw.classical_inputs.is_empty() && raw.classical_outputs.is_empty());
            assert_eq!(raw.declared_effect, Effect::Unitary);
            let [Storage::Quantum(stored_input)] = request.input_storage[0].as_slice() else {
                panic!("single input quantum storage")
            };
            let [Storage::Quantum(stored_output)] = request.storage.as_slice() else {
                panic!("single output quantum storage")
            };
            assert_eq!(stored_input.port, *input);
            assert_eq!(stored_output.port.token, *output);
            assert_eq!(stored_output.port.wires, input.wires);
            assert_eq!(stored_output.port.shape, input.shape);
            assert_eq!(
                stored_input.basis,
                vec![Basis::Pair, Basis::Bit, Basis::Bit]
            );
            assert_eq!(stored_output.basis, stored_input.basis);

            let scopes: Vec<_> = raw
                .operations
                .iter()
                .filter_map(|op| {
                    if let RawOp::ComputeUseUncompute {
                        targets,
                        ancilla_wires,
                        function,
                        use_ops,
                        ..
                    } = op
                    {
                        Some((targets, ancilla_wires, function, use_ops))
                    } else {
                        None
                    }
                })
                .collect();
            assert_eq!(
                scopes.len(),
                1,
                "{label}: actual computed scope must remain"
            );
            let (targets, ancilla, function, use_ops) = scopes[0];
            assert!(targets.is_empty());
            assert_eq!(ancilla.len(), 1);
            assert!(!input.wires.contains(&ancilla[0]));
            assert_eq!(function.as_slice(), [0, 1, 1, 1]); // nonzero2
            assert_eq!(
                use_ops.as_slice(),
                [ProtectedUse::ProtectedGate {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Ancilla,
                        index: 0
                    },
                    gate: SingleGate::Z,
                }]
            );

            // A local Z normalization receipt is not a proof of whole Grover
            // lowering, uncomputation or resource preservation. Check its actual
            // sources and both retained fragment actions separately.
            let equations: Vec<_> = accepted
                .source_computed_normalizations()
                .iter()
                .filter(|equation| {
                    equation
                        .names()
                        .0
                        .starts_with("std::reflection::reflect_uniform2::with_computed[")
                })
                .collect();
            assert_eq!(equations.len(), 1, "{label}: local source equation");
            let equation = equations[0];
            assert!(equation.names().1.ends_with("::diagonal[0,4]"));
            for module in ["std::reflection", "std::gate"] {
                let source = &project.module(module).unwrap().source;
                assert!(
                    equation
                        .sources()
                        .iter()
                        .any(|(name, bytes)| name == module && bytes == source)
                );
            }
            for leaf in [equation.implementation(), equation.specification()] {
                assert_eq!(leaf.boundary().signature(), &BasisType::Bit);
                assert_eq!(leaf.meaning(), &z);
                exact_request(leaf.program().raw(), BasisType::Bit, &z).unwrap();
            }
            // Recheck the retained typed root, then independently compare the
            // actual complete two-bit artifact with the fixed mathematical G.
            let checked_again = kernel.check_program(accepted).unwrap();
            assert_eq!(checked_again.program().runtime_result(), Some(request));
            exact_request(raw, pair.clone(), &expected)
                .unwrap_or_else(|error| panic!("{label}: exact Grover: {error:?}"));
            semantic_refusal(exact_request(raw, pair.clone(), &negative_phase));
            semantic_refusal(exact_request(raw, pair.clone(), &grover(0)));

            // Same valid total-table shape, but a wrong computed predicate:
            // change nonzero2(00) from 0 to 1. No original source is changed.
            let mut wrong_predicate = raw.clone();
            let function = wrong_predicate
                .operations
                .iter_mut()
                .find_map(|op| {
                    if let RawOp::ComputeUseUncompute { function, .. } = op {
                        Some(function)
                    } else {
                        None
                    }
                })
                .unwrap();
            function[0] = 1;
            semantic_refusal(exact_request(&wrong_predicate, pair.clone(), &expected));
        }
    }
}
