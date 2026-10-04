mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use common::SourceRoot;

use qleisli::frontend::compile::{ErrorCode, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};

impl SourceRoot {
    fn example(name: &str) -> Self {
        let root = Self::new("");
        let example = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        for entry in fs::read_dir(example).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "qli") {
                fs::copy(&path, root.0.join(path.file_name().unwrap())).unwrap();
            }
        }
        root
    }

    fn run(&self) -> BTreeMap<Vec<bool>, f64> {
        let ir = compile_project(&self.0).unwrap();
        let distribution = run_closed(&ir, SimulationLimits::default()).unwrap();
        assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
        distribution
    }
}

fn probability(distribution: &BTreeMap<Vec<bool>, f64>, bits: &[bool], expected: f64) {
    let actual = distribution.get(bits).copied().unwrap_or(0.0);
    assert!(
        (actual - expected).abs() < 1e-12,
        "{bits:?}: {actual}, expected {expected}"
    );
}

#[test]
fn documented_structured_algorithms_have_their_expected_results() {
    for (name, outcome) in [
        ("grover", vec![true, true]),
        ("bernstein_vazirani", vec![true, false]),
        ("bit_flip_code", vec![true, true, false, false, false]),
    ] {
        probability(&SourceRoot::example(name).run(), &outcome, 1.0);
    }
}

#[test]
fn grover_all_targets_and_iteration_counts_match_amplitude_amplification() {
    let root = SourceRoot::example("grover");
    for target in 0..4 {
        let a = if target & 1 != 0 { "a" } else { "not a" };
        let b = if target & 2 != 0 { "b" } else { "not b" };
        root.write(
            "oracle.qli",
            &format!(
                "use std::quantum::z;
             basis fn marked((a,b): (Bit,Bit)) -> Bit {{ ({a}) and ({b}) }}
             pub unitary fn mark(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)> {{
                 with_computed(q, marked) {{ |ancilla| z(ancilla) }}
             }}"
            ),
        );
        for iterations in 0..5 {
            root.write(
                "main.qli",
                &format!(
                    "use search::step;
                 use std::quantum::init0; use std::quantum::join;
                 use std::routines::hadamard2; use std::routines::measure_z2;
                 observe fn main() -> (Bit, Bit) {{
                     let q = hadamard2(join(init0(), init0()));
                     {} measure_z2(q)
                 }}",
                    "let q = step(q);".repeat(iterations)
                ),
            );
            let distribution = root.run();
            // One solution among four: sin(theta) = 1/2.
            let marked_probability = (((2 * iterations + 1) as f64) * std::f64::consts::PI / 6.0)
                .sin()
                .powi(2);
            for output in 0..4 {
                probability(
                    &distribution,
                    &[output & 1 != 0, output & 2 != 0],
                    if output == target {
                        marked_probability
                    } else {
                        (1.0 - marked_probability) / 3.0
                    },
                );
            }
        }
    }
}

#[test]
fn bernstein_vazirani_recovers_every_two_bit_secret() {
    let root = SourceRoot::example("bernstein_vazirani");
    for secret in 0..4 {
        let a = if secret & 1 != 0 { "a" } else { "0" };
        let b = if secret & 2 != 0 { "b" } else { "0" };
        root.write(
            "oracle.qli",
            &format!(
                "use std::quantum::z;
             basis fn linear((a,b): (Bit,Bit)) -> Bit {{ {a} xor {b} }}
             pub unitary fn mark(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)> {{
                 with_computed(q, linear) {{ |ancilla| z(ancilla) }}
             }}"
            ),
        );
        probability(&root.run(), &[secret & 1 != 0, secret & 2 != 0], 1.0);
    }
}

fn bell_recovery_source(a: &str, b: &str, c: &str) -> String {
    format!(
        "use code::encode; use code::recover; use code::decode;
         use std::quantum::init0; use std::quantum::h; use std::quantum::x; use std::quantum::z;
         use std::quantum::cnot; use std::quantum::split; use std::quantum::join;
         use std::observe::measure_z; use std::routines::measure_x;
         observe fn main() -> ((Bit, Bit), ((Bit, Bit), (Bit, Bit))) {{
             let (reference, logical) = cnot(h(init0()), init0());
             let (ab, c) = split(encode(logical));
             let (a, b) = split(ab);
             let damaged = join(join({a}, {b}), {c});
             let (repaired, syndrome) = recover(damaged);
             let (logical, (a, b)) = decode(repaired);
             let (reference, logical) = cnot(reference, logical);
             (syndrome, ((measure_x(reference), measure_z(logical)), (measure_z(a), measure_z(b))))
         }}"
    )
}

#[test]
fn single_bit_flip_recovery_preserves_entanglement_with_a_reference() {
    let root = SourceRoot::example("bit_flip_code");
    for (a, b, c, syndrome) in [
        ("a", "b", "c", [false, false]),
        ("x(a)", "b", "c", [true, false]),
        ("a", "x(b)", "c", [true, true]),
        ("a", "b", "x(c)", [false, true]),
    ] {
        root.write("main.qli", &bell_recovery_source(a, b, c));
        // Inverse Bell preparation must recover 00; decoded auxiliaries are 00.
        probability(
            &root.run(),
            &[syndrome[0], syndrome[1], false, false, false, false],
            1.0,
        );
    }
}

#[test]
fn bit_flip_code_does_not_claim_to_correct_phase_or_double_bit_errors() {
    let root = SourceRoot::example("bit_flip_code");
    root.write("main.qli", &bell_recovery_source("z(a)", "b", "c"));
    probability(&root.run(), &[false, false, true, false, false, false], 1.0);
    root.write("main.qli", &bell_recovery_source("x(a)", "x(b)", "c"));
    probability(&root.run(), &[false, true, false, true, false, false], 1.0);
}

#[test]
fn parity_measurement_keeps_coherence_within_each_parity_sector() {
    let root = SourceRoot::new("");
    root.write(
        "main.qli",
        "
        use std::quantum::init0; use std::quantum::h;
        use std::routines::parity_zz; use std::routines::measure_x;
        observe fn main() -> (Bit, (Bit, Bit)) {
            let ((a, b), parity) = parity_zz(h(init0()), h(init0()));
            (parity, (measure_x(a), measure_x(b)))
        }",
    );
    let distribution = root.run();
    for parity in [false, true] {
        for x in [false, true] {
            probability(&distribution, &[parity, x, x], 0.25);
        }
    }
}

#[test]
fn derived_routines_cannot_bypass_ownership_effect_or_basis_type_checks() {
    let imports = "use std::quantum::init0; use std::routines::parity_zz; use std::routines::hadamard2; use std::routines::measure_x;";
    for (declaration, code) in [
        (
            "observe fn main() -> Unit { let q = init0(); let _ = parity_zz(q, q); () }",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn f(q: Q<Bit>) -> Bit { measure_x(q) } observe fn main() -> Unit { () }",
            ErrorCode::Effect,
        ),
        (
            "observe fn main() -> Unit { let q = hadamard2(init0()); () }",
            ErrorCode::TypeMismatch,
        ),
        (
            "observe fn main() -> Unit { let ((a, b), p) = parity_zz(init0(), init0()); () }",
            ErrorCode::Ownership,
        ),
    ] {
        let root = SourceRoot::new("");
        root.write("main.qli", &format!("{imports} {declaration}"));
        let error = compile_project(&root.0).unwrap_err();
        assert_eq!(error.code, code, "{error}");
    }
}
