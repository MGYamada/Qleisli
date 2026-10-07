//! Executable source corpus: algorithms live in .qli, expectations live here.
//! Exhaustive finite simulation is a regression oracle, not a general proof.
mod common;

use common::{SourceRoot, current_namespace_fixture};
use qleisli::frontend::ast::StaticParamKind;
use qleisli::frontend::compile::{check_project_diagnostic, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

type Distribution = BTreeMap<Vec<bool>, f64>;
const STATES: &[&str] = &["zero", "one", "plus", "minus", "y_plus", "y_minus", "magic"];
const REJECTED: &[(&str, &str)] = &[
    ("basis_type_parameter", "parse"),
    // Shared syntax represents Nat; the finite lowering profile still rejects it.
    ("static_nat", "unsupported"),
    ("meaning_pair_predicate", "type_mismatch"),
    ("product_association", "type_mismatch"),
    ("sealed_provider", "type_mismatch"),
    ("missing_import", "unknown_name"),
    ("spent_owner", "ownership"),
    ("aliased_owner", "ownership"),
    ("dropped_owner", "ownership"),
    ("missing_adjoint", "capability"),
    ("controlled_is_not_apply", "capability"),
    ("auxiliary_hh", "unsupported"),
];

fn fixture(name: &str) -> String {
    fs::read_to_string(current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/qli_authoring")
            .join(format!("{name}.qli")),
    ))
    .unwrap()
}

// #25 retains historical authoring bytes. Explicit predicate and namespace
// translations are selected from recorded copies; neither is auto-repaired.
fn current_predicate_fixture(name: &str) -> String {
    fs::read_to_string(current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/predicate-domain/current/qli_authoring")
            .join(format!("{name}.qli")),
    ))
    .unwrap()
}

fn project(example: &str) -> SourceRoot {
    let root = SourceRoot::new("");
    for entry in fs::read_dir(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(example),
    )
    .unwrap()
    {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "qli") {
            fs::copy(&path, root.0.join(path.file_name().unwrap())).unwrap();
        }
    }
    root
}

fn execute(root: &SourceRoot) -> Distribution {
    let program = compile_project(&root.0).unwrap_or_else(|e| panic!("{e}"));
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    result
}

fn run(root: &SourceRoot, name: &str) -> Distribution {
    root.write("main.qli", &fixture(name));
    execute(root)
}

fn distribution(actual: &Distribution, expected: &[(Vec<bool>, f64)]) {
    let expected: Distribution = expected.iter().cloned().collect();
    // Check the union, including unexpected outcomes and tiny numerical zeros.
    for bits in actual.keys().chain(expected.keys()) {
        let a = actual.get(bits).copied().unwrap_or_default();
        let e = expected.get(bits).copied().unwrap_or_default();
        assert!(
            (a - e).abs() < 1e-12,
            "{bits:?}: {a}, expected {e}; {actual:?}"
        );
    }
}

fn message_distribution(tail: &[bool]) -> Vec<(Vec<bool>, f64)> {
    (0..4)
        .map(|m| {
            let mut bits = vec![m & 1 != 0, m & 2 != 0];
            bits.extend_from_slice(tail);
            (bits, 0.25)
        })
        .collect()
}

#[test]
fn inline_and_modular_teleportation_agree_on_every_classical_message() {
    let root = project("protocols");
    let expected = message_distribution(&[true]);
    distribution(&execute(&root), &expected);
    distribution(
        &run(&root, "protocols/teleport_inline_equivalent"),
        &expected,
    );
}

#[test]
fn teleportation_recovers_seven_states_and_an_entangled_reference() {
    let root = project("protocols");
    for state in STATES {
        distribution(
            &run(&root, &format!("protocols/teleport_{state}")),
            &message_distribution(&[false]),
        );
    }
    distribution(
        &run(&root, "protocols/teleport_reference"),
        &message_distribution(&[false, false]),
    );
}

#[test]
fn protocol_y_minus_has_the_full_independent_operator_phase() {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, Circuit, DEFAULT_EXACT_WORK};
    use qleisli::ir::RawOp;

    let root = project("protocols");
    // This whole-space equation is independent of preparing a state and then
    // undoing it with the same provider: S†H = [[s,s],[-i*s,i*s]]. It fixes
    // both columns and the complete phase, including under external reference.
    let s = Exact::inv_sqrt2();
    let expected = Matrix::new(
        2,
        2,
        vec![
            s,
            s,
            Exact::new([0, 0, 0, -1], 1).unwrap(),
            Exact::new([0, 0, 0, 1], 1).unwrap(),
        ],
    )
    .unwrap();
    root.write(
        "phase_fault.qli",
        "use states::y_minus; use std::quantum::phase_eighth;\n\
         pub unitary fn shifted(q:Q<Bit>)->Q<Bit>{phase_eighth(y_minus(q))}\n",
    );
    for provider in ["y_minus", "y_plus", "shifted"] {
        root.write(
            "main.qli",
            &format!(
                "use states::{{y_minus,y_plus}}; use phase_fault::shifted;\n\
                 use std::quantum::init0; use std::observe::measure_z;\n\
                 unitary fn use_op[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){{U(q)}}\n\
                 observe fn main()->Bit{{measure_z(use_op[{provider}](init0()))}}\n"
            ),
        );
        let accepted = compile_project(&root.0).unwrap();
        let applications: Vec<_> = accepted
            .raw()
            .operations
            .iter()
            .filter_map(|op| match op {
                RawOp::ApplyUnitary { steps, .. } => Some(steps.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(applications.len(), 1, "{provider}");
        let actual = Circuit::new(BasisType::Bit, applications[0].clone())
            .unwrap()
            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        // Both fault controls are native-valid unitaries. Admission alone
        // supplies no claim that either matches the intended y_minus meaning.
        assert_eq!(actual == expected, provider == "y_minus", "{provider}");
    }
}

#[test]
fn bell_components_support_dense_coding_and_entanglement_swapping() {
    let root = project("protocols");
    distribution(
        &run(&root, "protocols/dense_coding"),
        &[(
            vec![false, false, false, true, true, false, true, true],
            1.0,
        )],
    );
    distribution(
        &run(&root, "protocols/swapping_reference"),
        &message_distribution(&[false, false]),
    );
}

#[test]
fn phase_estimation_reuses_one_body_for_all_eighth_roots_and_x_eigenstates() {
    let root = project("operation_algorithms");
    distribution(&execute(&root), &[(vec![true, false, false, true], 1.0)]);
    for k in 0..8 {
        distribution(
            &run(&root, &format!("algorithms/phase3_t{k}")),
            &[(vec![k & 1 != 0, k & 2 != 0, k & 4 != 0, true], 1.0)],
        );
    }
    for (state, last_phase_bit) in [("plus", false), ("minus", true)] {
        distribution(
            &run(&root, &format!("algorithms/phase3_x_{state}")),
            &[(vec![false, false, last_phase_bit, false], 1.0)],
        );
    }
}

#[test]
fn canonical_control_migration_keeps_fixed_qpe_phase_and_reference_outcomes() {
    let root = project("operation_algorithms");
    root.write(
        "estimation.qli",
        &fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join(
                "tests/fixtures/authoring_sessions/canonical-control-migration-v030/attempt-01/estimation.qli",
            ),
        )
        .unwrap(),
    );
    distribution(&execute(&root), &[(vec![true, false, false, true], 1.0)]);
    distribution(
        &run(&root, "algorithms/phase3_identity_reference"),
        &[(vec![false; 5], 1.0)],
    );
    distribution(
        &run(&root, "algorithms/phase3_correlated"),
        &[
            (vec![false; 5], 0.5),
            (vec![true, false, false, true, true], 0.5),
        ],
    );
}

#[test]
fn phase_estimation_matches_off_grid_probabilities_and_reference_instruments() {
    let root = project("operation_algorithms");
    let expected: Vec<_> = (0..4)
        .map(|y| {
            let delta = std::f64::consts::TAU * (1.0 / 8.0 - f64::from(y) / 4.0);
            let real: f64 = (0..4).map(|r| (f64::from(r) * delta).cos()).sum();
            let imag: f64 = (0..4).map(|r| (f64::from(r) * delta).sin()).sum();
            (
                vec![y & 1 != 0, y & 2 != 0, true],
                (real * real + imag * imag) / 16.0,
            )
        })
        .collect();
    distribution(&run(&root, "algorithms/phase2_between_bins"), &expected);
    distribution(
        &run(&root, "algorithms/phase3_identity_reference"),
        &[(vec![false; 5], 1.0)],
    );
    distribution(
        &run(&root, "algorithms/phase3_correlated"),
        &[
            (vec![false; 5], 0.5),
            (vec![true, false, false, true, true], 0.5),
        ],
    );
}

#[test]
fn amplification_handles_all_marked_labels_and_detects_overshoot() {
    let root = project("operation_algorithms");
    for mark in ["00", "10", "01", "11"] {
        distribution(
            &run(&root, &format!("algorithms/search_{mark}")),
            &[(mark.bytes().map(|b| b == b'1').collect(), 1.0)],
        );
    }
    distribution(
        &run(&root, "algorithms/search_overshoot"),
        &message_distribution(&[]),
    );
}

#[test]
fn hadamard_tests_preserve_the_target_and_measure_both_overlap_components() {
    let root = project("operation_algorithms");
    let zero = (1.0 + std::f64::consts::FRAC_1_SQRT_2) / 2.0;
    for part in ["real", "imaginary"] {
        distribution(
            &run(&root, &format!("algorithms/overlap_{part}")),
            &[(vec![false, true], zero), (vec![true, true], 1.0 - zero)],
        );
        let inverse_zero = if part == "real" { zero } else { 1.0 - zero };
        distribution(
            &run(&root, &format!("algorithms/overlap_{part}_inverse")),
            &[
                (vec![false, true], inverse_zero),
                (vec![true, true], 1.0 - inverse_zero),
            ],
        );
    }
}

#[test]
fn type_correct_protocol_faults_are_detected_by_branch_sensitive_oracles() {
    let root = project("protocols");
    for fault in ["missing_phase", "swapped_message"] {
        root.write(
            "teleportation.qli",
            &fixture(&format!("faults/teleport_{fault}")),
        );
        // |0> misses an omitted phase correction, whereas |-> detects it.
        if fault == "missing_phase" {
            distribution(
                &run(&root, "protocols/teleport_zero"),
                &message_distribution(&[false]),
            );
        }
        let expected: Vec<_> = (0..4)
            .map(|m| {
                let phase = m & 1 != 0;
                let parity = m & 2 != 0;
                let failure = if fault == "missing_phase" {
                    phase
                } else {
                    phase ^ parity
                };
                (vec![phase, parity, failure], 0.25)
            })
            .collect();
        distribution(&run(&root, "protocols/teleport_minus"), &expected);
    }
}

#[test]
fn type_correct_forward_qft_fault_negates_the_phase_label() {
    let root = project("operation_algorithms");
    root.write("estimation.qli", &fixture("faults/phase3_forward_qft"));
    distribution(
        &run(&root, "algorithms/phase3_t1"),
        &[(vec![true, true, true, true], 1.0)],
    );
}

#[test]
fn authoring_limitations_and_useful_guardrails_have_source_reproductions() {
    for &(name, code) in REJECTED {
        let source = fixture(&format!("rejected/{name}"));
        let root = SourceRoot::new(&source);
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, code, "{name}: {error:?}");
        let location = error.primary.expect("source fixture must have a location");
        assert_eq!(
            location.path,
            root.0.join("main.qli").canonicalize().unwrap()
        );
        assert!(source.get(location.span.start..location.span.end).is_some());
        if name == "static_nat" {
            // Preserve the source limitation without requiring a second parser.
            let module = parse_module(&source).unwrap();
            let parameter = &module.decls[0].static_params[0];
            assert_eq!(parameter.kind, StaticParamKind::Natural);
            assert_eq!(parameter.name.text, "n");
            assert_eq!(location.span, parameter.name.span);
            assert_eq!((location.line, location.column), (1, 25));
            assert_eq!(&source[location.span.start..location.span.end], "n");
            assert_eq!(
                error.message,
                "finite profile does not support static Nat parameters"
            );
        }
        // Precise binding provenance is tested in authoring_ergonomics.rs.
    }
    distribution(
        &execute(&SourceRoot::new(&fixture("accepted/nary_tuple"))),
        &[(vec![false; 3], 1.0)],
    );
    for name in ["accepted/basis_tuple_pattern", "accepted/pair_contract"] {
        let original = SourceRoot::new(&fixture(name));
        let error = check_project_diagnostic(&original.0).unwrap_err();
        assert_eq!(error.code, "arity", "historical {name}: {error:?}");
        assert!(
            error
                .message
                .contains("exactly one explicit basis parameter")
        );
        distribution(
            &execute(&SourceRoot::new(&current_predicate_fixture(name))),
            &[(vec![true, true], 1.0)],
        );
    }
    distribution(
        &execute(&SourceRoot::new(&fixture("accepted/auxiliary_hh"))),
        &[(vec![false], 1.0)],
    );
    distribution(
        &execute(&SourceRoot::new(&fixture("accepted/product_reassociation"))),
        &[(vec![true, false, true], 1.0)],
    );
}

#[test]
fn every_quick_reference_program_compiles_and_executes() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/quick_reference");
    let programs = [
        "exact_phase.qli",
        "teleport_minus.qli",
        "phase_kickback.qli",
        "operation_round_trip.qli",
    ];
    let inventoried: BTreeSet<_> = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .filter(|name| name.ends_with(".qli"))
        .collect();
    assert_eq!(
        inventoried,
        programs.map(String::from).into_iter().collect()
    );
    let expected = [
        vec![(vec![false], 1.0)],
        message_distribution(&[true]),
        vec![(vec![true, true], 1.0)],
        vec![(vec![false], 1.0)],
    ];
    assert_eq!(
        programs.len(),
        expected.len(),
        "each program needs an output oracle"
    );
    for (program, expected) in programs.into_iter().zip(expected) {
        let source =
            fs::read_to_string(current_namespace_fixture(&directory.join(program))).unwrap();
        distribution(&execute(&SourceRoot::new(&source)), &expected);
    }
}

#[test]
fn every_source_fixture_belongs_to_an_exercised_case() {
    let mut expected = BTreeSet::new();
    for state in STATES {
        expected.insert(format!("protocols/teleport_{state}"));
    }
    for name in [
        "teleport_reference",
        "teleport_inline_equivalent",
        "dense_coding",
        "swapping_reference",
    ] {
        expected.insert(format!("protocols/{name}"));
    }
    for k in 0..8 {
        expected.insert(format!("algorithms/phase3_t{k}"));
    }
    for name in [
        "phase2_between_bins",
        "phase3_x_plus",
        "phase3_x_minus",
        "phase3_identity_reference",
        "phase3_correlated",
        "search_00",
        "search_10",
        "search_01",
        "search_11",
        "search_overshoot",
        "overlap_real",
        "overlap_imaginary",
        "overlap_real_inverse",
        "overlap_imaginary_inverse",
    ] {
        expected.insert(format!("algorithms/{name}"));
    }
    for &(name, _) in REJECTED {
        expected.insert(format!("rejected/{name}"));
    }
    for name in [
        "teleport_missing_phase",
        "teleport_swapped_message",
        "phase3_forward_qft",
    ] {
        expected.insert(format!("faults/{name}"));
    }
    expected.insert("accepted/nary_tuple".into());
    expected.insert("accepted/basis_tuple_pattern".into());
    expected.insert("accepted/auxiliary_hh".into());
    expected.insert("accepted/pair_contract".into());
    expected.insert("accepted/product_reassociation".into());
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/qli_authoring");
    fn sources(root: &Path, path: &Path, found: &mut BTreeSet<String>) {
        for entry in fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                sources(root, &path, found);
            } else if path.extension().is_some_and(|e| e == "qli") {
                found.insert(
                    path.strip_prefix(root)
                        .unwrap()
                        .with_extension("")
                        .to_str()
                        .unwrap()
                        .replace('\\', "/"),
                );
            }
        }
    }
    let mut found = BTreeSet::new();
    sources(&root, &root, &mut found);
    assert_eq!(found, expected);
}
