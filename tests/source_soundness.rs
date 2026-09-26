//! Finite numerical regressions for source instruments, not a soundness proof.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use qleisli_core::VerifiedProgram;
use qleisli_core::frontend::compile::compile_project;
use qleisli_core::ir::RawOp;
use qleisli_core::sim::{SimulationLimits, run_closed};

static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

struct SourceRoot(PathBuf);

impl SourceRoot {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "qleisli-source-soundness-{}-{}",
            std::process::id(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("main.qli"), source).unwrap();
        Self(path)
    }
}

impl Drop for SourceRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn compile(source: &str) -> VerifiedProgram {
    let root = SourceRoot::new(source);
    compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"))
}

fn assert_distribution(actual: &BTreeMap<Vec<bool>, f64>, expected: &BTreeMap<Vec<bool>, f64>) {
    // Compare raw, unnormalized history weights. Renormalizing the result here
    // would hide trace lost by an incorrect projection or adaptive branch.
    assert!((actual.values().sum::<f64>() - 1.0).abs() < 1e-12);
    for outcome in actual.keys().chain(expected.keys()) {
        let actual_weight = actual.get(outcome).copied().unwrap_or(0.0);
        let expected_weight = expected.get(outcome).copied().unwrap_or(0.0);
        assert!(
            (actual_weight - expected_weight).abs() < 1e-12,
            "{outcome:?}: {actual_weight}, expected {expected_weight}"
        );
    }
}

#[test]
fn hidden_measurement_histories_add_weights_despite_opposite_final_phases() {
    let program = compile(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::z;
use std::quantum::cnot;
use std::observe::measure_z;
observe fn main() -> CBit {
    let (a,r) = cnot(h(init0()),init0());
    let hidden = measure_z(a);
    let r = if hidden { x(z(r)) } else { r };
    measure_z(r)
}
"#,
    );
    assert!(program.program().operations.iter().any(|op| matches!(
        op,
        RawOp::ClassicalBranch { quantum_phis, .. } if quantum_phis.len() == 1
    )));
    // The two histories end in |0>/sqrt(2) and -|0>/sqrt(2). Hiding the
    // measured bit must add their squared norms to one, never cancel them.
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    assert_distribution(&distribution, &BTreeMap::from([(vec![false], 1.0)]));
}

#[test]
fn adaptive_observation_preserves_joint_weights_correlations_and_coarse_graining() {
    let source = r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::t;
use std::quantum::cnot;
use std::observe::measure_z;
observe fn main() -> OUTPUT_TYPE {
    let (a,r) = cnot(t(t(h(t(h(init0()))))),init0());
    let choice = measure_z(h(init0()));
    let (outcome,r) = if choice {
        let outcome = measure_z(a);
        (outcome,r)
    } else {
        let outcome = measure_z(h(a));
        (outcome,r)
    };
    let r = if choice { r } else { h(r) };
    OUTPUT
}
"#;
    // Up to one common phase, the entangled input is
    // cos(pi/8)|00> + sin(pi/8)|11>. Z/Z reads agree with biased weights;
    // X/X reads have parity bias cos(pi/4). The choice has weight one half.
    let high = (2.0 + 2.0_f64.sqrt()) / 4.0;
    let low = 1.0 - high;
    let joint = BTreeMap::from([
        (vec![true, false, false], high / 2.0),
        (vec![true, true, true], low / 2.0),
        (vec![false, false, false], high / 4.0),
        (vec![false, false, true], low / 4.0),
        (vec![false, true, false], low / 4.0),
        (vec![false, true, true], high / 4.0),
    ]);
    let retained = compile(
        &source
            .replace("OUTPUT_TYPE", "(CBit,(CBit,CBit))")
            .replace("OUTPUT", "(choice,(outcome,measure_z(r)))"),
    );
    assert!(retained.program().operations.iter().any(|op| matches!(
        op,
        RawOp::ClassicalBranch { quantum_phis, classical_phis, .. }
            if quantum_phis.len() == 1 && classical_phis.len() == 1
    )));
    assert_distribution(
        &run_closed(&retained, SimulationLimits::default()).unwrap(),
        &joint,
    );

    let hidden = compile(
        &source
            .replace("OUTPUT_TYPE", "CBit")
            .replace("OUTPUT", "measure_z(r)"),
    );
    // Independently derived marginal: average the biased Z read and the
    // uniform X read. Earlier histories are absent from the public result.
    let marginal = BTreeMap::from([
        (vec![false], (high + 0.5) / 2.0),
        (vec![true], (low + 0.5) / 2.0),
    ]);
    assert_distribution(
        &run_closed(&hidden, SimulationLimits::default()).unwrap(),
        &marginal,
    );
}

#[test]
fn injective_growth_keeps_reference_coherence_while_reset_erases_it() {
    for reset in [false, true] {
        let source = format!(
            r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::t;
use std::quantum::cnot;
use std::quantum::split;
use std::observe::measure_z;
use std::observe::reset;
observe fn main() -> (CBit,(CBit,CBit)) {{
    let (a,r) = cnot(h(init0()),init0());
    let (a,b) = split(do x <- t(a); pure (x,x));
    {}
    (measure_z(h(a)),(measure_z(h(b)),measure_z(h(r))))
}}
"#,
            if reset { "let a = reset(a);" } else { "" }
        );
        let program = compile(&source);
        assert!(program.program().operations.iter().any(|op| matches!(
            op,
            RawOp::LiftBasis { output_wires, table, .. }
                if output_wires.len() == 2 && table == &[0, 3]
        )));
        assert_eq!(
            program
                .program()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::Reset { .. }))
                .count(),
            usize::from(reset)
        );
        // The injection gives (|000> + exp(i*pi/4)|111>)/sqrt(2),
        // not two copies of an unknown state. X parity reveals the phase.
        // Reset replaces the first subsystem by |0> and leaves a classical
        // mixture on the other two, making all eight X outcomes uniform.
        let mut expected = BTreeMap::new();
        for a in [false, true] {
            for b in [false, true] {
                for r in [false, true] {
                    let parity_sign = if a ^ b ^ r { -1.0 } else { 1.0 };
                    let weight = if reset {
                        1.0 / 8.0
                    } else {
                        (1.0 + parity_sign * std::f64::consts::FRAC_1_SQRT_2) / 8.0
                    };
                    expected.insert(vec![a, b, r], weight);
                }
            }
        }
        assert_distribution(
            &run_closed(&program, SimulationLimits::default()).unwrap(),
            &expected,
        );
    }
}

#[test]
fn zero_probability_histories_do_not_execute_or_normalize_an_inactive_arm() {
    for choice in [false, true] {
        let source = format!(
            r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> (CBit,CBit) {{
    let choice = measure_z({});
    let q = init0();
    let outcome = if choice {{ measure_z({}) }} else {{ measure_z({}) }};
    (choice,outcome)
}}
"#,
            if choice { "x(init0())" } else { "init0()" },
            if choice { "q" } else { "h(q)" },
            if choice { "h(q)" } else { "q" },
        );
        // The selected path has one nonzero history throughout. The other
        // arm would create two; it must neither consume this one-component
        // budget nor contribute a normalized state from a zero-weight input.
        let limits = SimulationLimits {
            max_components: 1,
            ..SimulationLimits::default()
        };
        assert_distribution(
            &run_closed(&compile(&source), limits).unwrap(),
            &BTreeMap::from([(vec![choice, false], 1.0)]),
        );
    }
}
