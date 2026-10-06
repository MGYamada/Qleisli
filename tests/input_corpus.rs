//! Smoke checks for the frozen external input corpus. Independent exhaustive
//! complex-entry/instrument oracles live in scripts/check_input_corpus.py.
mod common;

use common::current_corpus_projects;
use qleisli::frontend::compile::compile_project;
use qleisli::sim::{SimulationLimits, run_closed};
use std::{fs, path::Path};

#[test]
fn all_reviewed_corpus_projects_compile_verify_and_execute() {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus");
    let mut logical = Vec::new();
    for source in ["quantum_katas", "qualtran", "pennylane_demos"] {
        let mut count = 0;
        for entry in fs::read_dir(corpus.join(source)).unwrap() {
            let project = entry.unwrap().path();
            if !project.join("main.qli").is_file() {
                continue;
            }
            logical.push(project);
            count += 1;
        }
        assert!(count > 0, "missing reviewed source family {source}");
    }
    logical.sort();
    assert_eq!(logical.len(), 87, "logical corpus coverage changed");
    let current = current_corpus_projects(&logical);
    assert_eq!(
        logical
            .iter()
            .zip(&current)
            .filter(|(before, after)| before != after)
            .count(),
        6,
        "current corpus snapshots not selected"
    );
    for project in current {
        let checked = compile_project(&project)
            .unwrap_or_else(|error| panic!("{}: {error}", project.display()));
        let distribution = run_closed(&checked, SimulationLimits::default()).unwrap();
        assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-11);
        assert!(distribution.values().all(|p| p.is_finite() && *p >= 0.0));
    }
}

#[test]
fn local_corpus_counterexamples_reject() {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus/negative");
    for name in [
        "duplicate_owner",
        "measured_owner",
        "measurement_adjoint",
        "dirty_auxiliary",
    ] {
        assert!(compile_project(&corpus.join(name)).is_err(), "{name}");
    }
}
