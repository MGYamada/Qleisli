mod common;
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use common::accept;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::ir::*;
use qleisli::sim::{SimulationLimits, run_closed};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Root(PathBuf);
impl Root {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "qleisli-static-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("Qargo.toml"), include_str!("Qargo.toml")).unwrap();
        Self(path)
    }
    fn qpe() -> Self {
        let root = Self::new();
        for file in ["main.qli", "evolution.qli", "estimation.qli"] {
            fs::copy(
                PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/phase_estimation")
                    .join(file),
                root.0.join(file),
            )
            .unwrap();
        }
        root
    }
    fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }
    fn run(&self) -> BTreeMap<Vec<bool>, f64> {
        let ir = compile_project(&self.0).unwrap();
        let result = run_closed(&ir, SimulationLimits::default()).unwrap();
        assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
        result
    }
    fn evolution(&self, n: usize) {
        self.write("evolution.qli", &format!("use std::quantum::t; pub unitary fn evolve(q: Q<Bit>) -> Q<Bit> {{ repeat_static({n}, t, q) }}"));
    }
}
impl Drop for Root {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn probability(result: &BTreeMap<Vec<bool>, f64>, bits: &[bool], expected: f64) {
    let actual = result.get(bits).copied().unwrap_or(0.0);
    assert!(
        (actual - expected).abs() < 1e-12,
        "{bits:?}: {actual}, expected {expected}"
    );
}
const IMPORTS: &str = "use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split; use std::observe::measure_z;
use std::observe::discard; use std::measurement::measure_x;";

#[test]
fn qpe_resolves_all_eighth_turns_in_little_endian_order() {
    let root = Root::qpe();
    for n in 0..8 {
        root.evolution(n);
        probability(
            &root.run(),
            &[n & 1 != 0, n & 2 != 0, n & 4 != 0, true],
            1.0,
        );
    }
}

#[test]
fn qpe_off_grid_phases_match_the_finite_fourier_distribution() {
    let root = Root::qpe();
    root.write(
        "main.qli",
        "use estimation::phase2; use std::quantum::init0;
        use std::quantum::x; use std::observe::measure_z;
        observe fn main() -> ((Bit,Bit),Bit) {
            let (phase, q) = phase2(x(init0())); (phase, measure_z(q))
        }",
    );
    for n in [1, 3, 5, 7] {
        root.evolution(n);
        let result = root.run();
        for y in 0..4 {
            let delta = n as f64 / 8.0 - y as f64 / 4.0;
            let (mut re, mut im) = (0.0, 0.0);
            for r in 0..4 {
                let angle = std::f64::consts::TAU * r as f64 * delta;
                re += angle.cos() / 4.0;
                im += angle.sin() / 4.0;
            }
            probability(&result, &[y & 1 != 0, y & 2 != 0, true], re * re + im * im);
        }
    }
}

#[test]
fn qpe_preserves_degenerate_coherence_and_correlates_with_a_reference() {
    let root = Root::qpe();
    root.write(
        "main.qli",
        &format!(
            "{IMPORTS} use estimation::phase3;
        observe fn main() -> ((((Bit,Bit),Bit),Bit),Bit) {{
            let (r, q) = cnot(h(init0()), init0());
            let (phase, q) = phase3(q);
            ((phase, measure_z(r)), measure_z(q))
        }}"
        ),
    );
    let result = root.run();
    probability(&result, &[false, false, false, false, false], 0.5);
    probability(&result, &[true, false, false, true, true], 0.5);
    root.evolution(0);
    root.write(
        "main.qli",
        &format!(
            "{IMPORTS} use estimation::phase3;
        observe fn main() -> ((((Bit,Bit),Bit),Bit),Bit) {{
            let (r, q) = cnot(h(init0()), init0());
            let (phase, q) = phase3(q);
            let (r, q) = cnot(r, q);
            ((phase, measure_x(r)), measure_z(q))
        }}"
        ),
    );
    probability(&root.run(), &[false; 5], 1.0);
}

#[test]
fn inverse_reverses_noncommuting_gates_and_output_axis_reordering() {
    let root = Root::new();
    root.write(
        "main.qli",
        &format!(
            "{IMPORTS}
        unitary fn mix(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
            let (a,b) = split(q);
            let a = t(h(a));
            let b = basis b as x {{ not x }};
            let (a,b) = cnot(a,b);
            join(b,a)
        }}
        observe fn main() -> (Bit,Bit) {{
            let q = mix(join(init0(), h(init0())));
            let (a,b) = split(adjoint(mix,q));
            (measure_z(a),measure_x(b))
        }}"
        ),
    );
    probability(&root.run(), &[false, false], 1.0);
}

#[test]
fn control_preserves_reflection_sign_including_inverse_and_nested_control() {
    let root = Root::new();
    for operation in ["minus", "inverse_minus", "nested"] {
        root.write(
            "main.qli",
            &format!(
                "{IMPORTS}
            unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{ q }}
            unitary fn idbit(q: Q<Bit>) -> Q<Bit> {{ q }}
            unitary fn negbit(q: Q<Bit>) -> Q<Bit> {{ z(x(z(x(q)))) }}
            unitary fn minus(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
                let (a,b) = split(q); join(negbit(a),b)
            }}
            unitary fn inverse_minus(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{ adjoint(minus,q) }}
            unitary fn nested(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
                let (a,b) = split(q);
                let (a,b) = qif(a,b) {{ 0 => idbit, 1 => negbit }};
                join(a,b)
            }}
            observe fn main() -> (Bit,(Bit,Bit)) {{
                let q = join(x(init0()), h(init0()));
                let (c,q) = qif(h(init0()),q) {{ 0 => identity, 1 => {operation} }};
                let (a,b) = split(q);
                (measure_x(c),(measure_z(a),measure_x(b)))
            }}"
            ),
        );
        probability(&root.run(), &[true, true, false], 1.0);
    }
}

#[test]
fn computed_zero_width_phase_survives_inverse_and_control() {
    let root = Root::new();
    root.write(
        "main.qli",
        &format!(
            "{IMPORTS}
        classical fn yes(x: Unit) -> Bit {{ 1 }}
        unitary fn identity(q: Q<Unit>) -> Q<Unit> {{ q }}
        unitary fn phase(q: Q<Unit>) -> Q<Unit> {{ with_computed(q,yes) {{ |a| t(a) }} }}
        unitary fn phase_back(q: Q<Unit>) -> Q<Unit> {{ adjoint(phase,q) }}
        observe fn main() -> (Bit,Bit) {{
            let pair = basis init0() as b {{ ((),b) }};
            let (u,b) = split(pair);
            let (c,u) = qif(h(init0()),u) {{ 0 => identity, 1 => phase_back }};
            let c = t(c);
            discard(u);
            (measure_x(c),measure_z(b))
        }}"
        ),
    );
    probability(&root.run(), &[false, false], 1.0);
}

#[test]
fn grover_reflection_and_its_negative_are_distinguished_under_control() {
    let root = Root::new();
    for (function, expected) in [("reflect_uniform2", false), ("negative", true)] {
        root.write("main.qli", &format!("{IMPORTS}
            use std::reflection::reflect_uniform2; use std::transform::hadamard2;
            unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{ q }}
            unitary fn negative(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
                let (a,b) = split(reflect_uniform2(q)); join(z(x(z(x(a)))),b)
            }}
            observe fn main() -> (Bit,(Bit,Bit)) {{
                let (c,q) = qif(h(init0()),hadamard2(join(init0(),init0()))) {{ 0 => identity, 1 => {function} }};
                let (a,b) = split(q); (measure_x(c),(measure_x(a),measure_x(b)))
            }}"));
        probability(&root.run(), &[expected, false, false], 1.0);
    }
}

#[test]
fn repetition_zero_one_and_many_have_explicit_semantics() {
    let root = Root::new();
    for n in [0, 1, 2, 3, 4096] {
        root.write(
            "main.qli",
            &format!(
                "{IMPORTS} observe fn main() -> Bit {{ measure_z(repeat_static({n},x,init0())) }}"
            ),
        );
        probability(&root.run(), &[n % 2 == 1], 1.0);
    }
}

#[test]
fn static_forms_reject_bad_names_effects_types_and_ownership() {
    let root = Root::new();
    let cases = [
        (
            "unitary fn f(q:Q<Bit>) -> Q<Bit> { repeat_static(0,missing,q) }",
            ErrorCode::UnknownName,
        ),
        (
            "unitary fn f(q:Q<Bit>) -> Q<Bit> { repeat_static(0,measure_z,q) }",
            ErrorCode::Effect,
        ),
        (
            "observe fn u(q:Q<Bit>)->Q<Bit>{let b=measure_z(init0());q} unitary fn f(q:Q<Bit>)->Q<Bit>{adjoint(u,q)}",
            ErrorCode::Effect,
        ),
        (
            "unitary fn u(q:Q<Bit>,c:Bit)->Q<Bit>{q} unitary fn f(q:Q<Bit>)->Q<Bit>{adjoint(u,q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(q,q){0=>h,1=>x}}",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{ let h = (); adjoint(h,q) }",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{adjoint(t,q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{repeat_static(0,f,q)}",
            ErrorCode::RecursiveCall,
        ),
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{repeat_static(0,bad,q)} unitary fn bad(q:Q<Bit>)->Q<Bit>{h(q);q}",
            ErrorCode::Ownership,
        ),
    ];
    for (source, code) in cases {
        root.write("main.qli", &format!("{IMPORTS} {source}"));
        assert_eq!(check_project(&root.0).unwrap_err().code, code, "{source}");
    }
}

#[test]
fn static_syntax_has_bounded_numbers_and_precise_failures() {
    for (body, offending) in [
        ("repeat_static(4097,h,q)", "4097"),
        (
            "repeat_static(999999999999999999999999,h,q)",
            "999999999999999999999999",
        ),
        ("repeat_static(00,h,q)", "00"),
        ("repeat_static(n,h,q)", "n"),
        ("qif(q,r){1=>h,0=>x}", "1"),
    ] {
        let prefix = "unitary fn f(q:Q<Bit>,r:Q<Bit>)->Q<Bit>{";
        let source = format!("{prefix}{body}}}");
        let error = parse_module(&source).unwrap_err();
        assert_eq!(
            error.span.start,
            prefix.len() + body.find(offending).unwrap()
        );
    }
    let expr = format!("{}q{}", "adjoint(h,".repeat(10_000), ")".repeat(10_000));
    let source = format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{expr}}}");
    assert!(parse_module(&source).unwrap_err().message.contains("limit"));
}

#[test]
fn nested_static_expansion_is_bounded_in_work_and_depth() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let root = Root::new();
            root.write(
                "main.qli",
                &format!(
                    "{IMPORTS}
            unitary fn a(q:Q<Bit>)->Q<Bit>{{repeat_static(4096,t,q)}}
            unitary fn b(q:Q<Bit>)->Q<Bit>{{repeat_static(4096,a,q)}}"
                ),
            );
            assert_eq!(check_project(&root.0).unwrap_err().code, ErrorCode::Limit);
            let mut source = format!("{IMPORTS} unitary fn f0(q:Q<Bit>)->Q<Bit>{{t(q)}}");
            for i in 1..90 {
                source.push_str(&format!(
                    " unitary fn f{i}(q:Q<Bit>)->Q<Bit>{{adjoint(f{},q)}}",
                    i - 1
                ));
            }
            root.write("main.qli", &source);
            assert_eq!(check_project(&root.0).unwrap_err().code, ErrorCode::Limit);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn raw_finite_circuit_validation_rejects_forged_certificates() {
    let good = CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: vec![0],
            permutation: vec![1, 0],
            phases: vec![1, 7],
        },
    };
    let raw = |step| RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0)],
            shape: BasisShape::BIT,
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![step],
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    accept(raw(good.clone())).unwrap();
    for (indices, permutation, phases) in [
        (vec![1], vec![0, 1], vec![0, 0]),
        (vec![0, 0], vec![0, 1, 2, 3], vec![0; 4]),
        (vec![0], vec![0, 0], vec![0, 0]),
        (vec![0], vec![0, 2], vec![0, 0]),
        (vec![0], vec![0], vec![0]),
        (vec![0], vec![0, 1], vec![0]),
        (vec![0], vec![0, 1], vec![0, 8]),
    ] {
        assert!(
            accept(raw(CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases
                }
            }))
            .is_err()
        );
    }
    let mut overlap = good;
    overlap.controls = vec![BitControl {
        index: 0,
        when_one: true,
    }];
    assert!(accept(raw(overlap)).is_err());
    for controls in [
        vec![BitControl {
            index: 1,
            when_one: false,
        }],
        vec![
            BitControl {
                index: 0,
                when_one: true
            };
            2
        ],
    ] {
        assert!(
            accept(raw(CircuitStep {
                controls,
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![1]
                }
            }))
            .is_err()
        );
    }
}
