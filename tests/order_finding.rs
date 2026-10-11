use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::project::{ImportOrigin, ModuleOrigin, Project};
use qleisli::host::{Factors, PhaseInputError, factor_from_phase};
use qleisli::sim::{SimulationLimits, run_closed};

static NEXT: AtomicU64 = AtomicU64::new(0);
const ARITHMETIC: &str = include_str!("../examples/order_finding/arithmetic.qli");
const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::cnot; use std::quantum::split; use std::quantum::join;
use std::observe::measure_z; use std::observe::discard;
use std::measurement::measure_z2; use std::measurement::measure_x;
use arithmetic::increment2; use arithmetic::add2;
use arithmetic::mul2_mod15;
";

struct Root(PathBuf);

impl Root {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "qleisli-order-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("Qargo.toml"), include_str!("Qargo.toml")).unwrap();
        fs::write(path.join("arithmetic.qli"), ARITHMETIC).unwrap();
        Self(path)
    }

    fn example() -> Self {
        let root = Self::new();
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/order_finding");
        for entry in fs::read_dir(source).unwrap() {
            let path = entry.unwrap().path();
            fs::copy(&path, root.0.join(path.file_name().unwrap())).unwrap();
        }
        root
    }

    fn main(&self, source: &str) {
        fs::write(self.0.join("main.qli"), format!("{IMPORTS}\n{source}")).unwrap();
    }

    fn run(&self) -> BTreeMap<Vec<bool>, f64> {
        let program = compile_project(&self.0).unwrap();
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
        result
    }
}

impl Drop for Root {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn bits(value: usize, width: usize) -> Vec<bool> {
    (0..width).map(|i| value & (1 << i) != 0).collect()
}

fn prepare2(value: usize) -> String {
    let bit = |i: usize| {
        if value & (1usize << i) == 0 {
            "init0()"
        } else {
            "x(init0())"
        }
    };
    format!("join({}, {})", bit(0), bit(1))
}

fn prepare4(value: usize) -> String {
    format!("join({}, {})", prepare2(value & 3), prepare2(value >> 2))
}

fn probability(result: &BTreeMap<Vec<bool>, f64>, output: &[bool], expected: f64) {
    let actual = result.get(output).copied().unwrap_or(0.0);
    assert!(
        (actual - expected).abs() < 1e-12,
        "{output:?}: {actual} != {expected}"
    );
}

#[test]
fn fixed_arithmetic_is_local_ordinary_source_without_public_std_aliases() {
    let root = Root::new();
    root.main("observe fn main()->Unit{()}");
    let project = Project::load(&root.0).unwrap();
    let module = project.module("arithmetic").unwrap();
    assert_eq!(module.origin, ModuleOrigin::Local);
    assert_eq!(
        module.ast.decls.iter().filter(|decl| decl.public).count(),
        3
    );
    for name in ["increment2", "add2", "mul2_mod15"] {
        assert_eq!(
            project.module("main").unwrap().imports[name].origin,
            ImportOrigin::Local
        );
    }
    check_project(&root.0).unwrap();
    for name in ["increment2", "add2", "mul2_mod15"] {
        fs::write(
            root.0.join("main.qli"),
            format!("use std::arithmetic::{name}; fn main()->Unit{{()}}"),
        )
        .unwrap();
        assert!(
            Project::load(&root.0).is_err(),
            "retired std arithmetic alias: {name}"
        );
    }
}

#[test]
fn increment_and_add_match_modular_arithmetic_on_every_basis_input() {
    let root = Root::new();
    for y in 0..4 {
        root.main(&format!(
            "observe fn main()->(Bit,Bit){{measure_z2(increment2({}))}}",
            prepare2(y)
        ));
        probability(&root.run(), &bits((y + 1) % 4, 2), 1.0);
    }
    for x in 0..4 {
        for y in 0..4 {
            root.main(&format!(
                "observe fn main()->((Bit,Bit),(Bit,Bit)){{
                 let (a,b)=split(add2(join({},{}))); (measure_z2(a),measure_z2(b)) }}",
                prepare2(x),
                prepare2(y)
            ));
            probability(&root.run(), &bits(x | (((x + y) % 4) << 2), 4), 1.0);
        }
    }
}

#[test]
fn modular_multiply_powers_and_inverse_cover_the_full_register_space() {
    let root = Root::new();
    for input in 0..16 {
        for power in 0..=4 {
            root.main(&format!(
                "observe fn main()->((Bit,Bit),(Bit,Bit)){{
                 let (a,b)=split(power(mul2_mod15,{power})({}));
                 (measure_z2(a),measure_z2(b)) }}",
                prepare4(input)
            ));
            let expected = if input == 15 {
                15
            } else {
                (input * (1 << power)) % 15
            };
            probability(&root.run(), &bits(expected, 4), 1.0);
        }
        root.main(&format!(
            "observe fn main()->((Bit,Bit),(Bit,Bit)){{
             let (a,b)=split(adjoint(mul2_mod15)({})); (measure_z2(a),measure_z2(b)) }}",
            prepare4(input)
        ));
        probability(
            &root.run(),
            &bits(if input == 15 { 15 } else { input * 8 % 15 }, 4),
            1.0,
        );
    }
}

#[test]
fn arithmetic_round_trip_preserves_four_entangled_references() {
    let root = Root::new();
    for operation in ["add2", "mul2_mod15"] {
        root.main(&format!(
            "observe fn main()->(((Bit,Bit),(Bit,Bit)),((Bit,Bit),(Bit,Bit))){{
             let (a,ra)=cnot(h(init0()),init0()); let (b,rb)=cnot(h(init0()),init0());
             let (c,rc)=cnot(h(init0()),init0()); let (d,rd)=cnot(h(init0()),init0());
             let q=adjoint({operation})({operation}(join(join(a,b),join(c,d))));
             let (ab,cd)=split(q); let (a,b)=split(ab); let (c,d)=split(cd);
             let (a,ra)=cnot(a,ra); let (b,rb)=cnot(b,rb);
             let (c,rc)=cnot(c,rc); let (d,rd)=cnot(d,rd);
             (((measure_x(a),measure_x(b)),(measure_x(c),measure_x(d))),
              ((measure_z(ra),measure_z(rb)),(measure_z(rc),measure_z(rd)))) }}"
        ));
        probability(&root.run(), &[false; 8], 1.0);
    }
}

#[test]
fn qpe_matches_every_modular_orbit_including_zero_and_unused_fifteen() {
    let root = Root::example();
    for input in 0..16 {
        root.main(&format!(
            "use estimation::phase3;
             observe fn main()->((Bit,Bit),Bit){{
             let (phase,q)=phase3({}); discard(q); phase }}",
            prepare4(input)
        ));
        let mut period = 1;
        let mut next = if input == 15 { 15 } else { input * 2 % 15 };
        while next != input {
            period += 1;
            next = next * 2 % 15;
        }
        let result = root.run();
        for y in 0..8 {
            probability(
                &result,
                &bits(y, 3),
                if y % (8 / period) == 0 {
                    1.0 / period as f64
                } else {
                    0.0
                },
            );
        }
    }
}

#[test]
fn qpe_preserves_reference_coherence_in_the_degenerate_fixed_subspace() {
    let root = Root::example();
    root.main(
        "use estimation::phase3;
        observe fn main()->(((Bit,Bit),Bit),(Bit,((Bit,Bit),(Bit,Bit)))){
        let (r,a)=cnot(h(init0()),init0()); let (r,b)=cnot(r,init0());
        let (r,c)=cnot(r,init0()); let (r,d)=cnot(r,init0());
        let (phase,q)=phase3(join(join(a,b),join(c,d)));
        let (ab,cd)=split(q); let (a,b)=split(ab); let (c,d)=split(cd);
        let (r,a)=cnot(r,a); let (r,b)=cnot(r,b); let (r,c)=cnot(r,c); let (r,d)=cnot(r,d);
        (phase,(measure_x(r),((measure_z(a),measure_z(b)),(measure_z(c),measure_z(d))))) }",
    );
    probability(&root.run(), &[false; 8], 1.0);
}

#[test]
fn arithmetic_and_order_finding_obey_types_effects_and_ownership() {
    let root = Root::example();
    for (source, expected) in [
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{increment2(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{add2(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{mul2_mod15(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn f(q:Q<(Bit,Bit)>)->(Q<(Bit,Bit)>,Q<(Bit,Bit)>){(increment2(q),q)}",
            ErrorCode::Ownership,
        ),
        (
            "use estimation::phase3; unitary fn f(q:Q<((Bit,Bit),(Bit,Bit))>)->(((Bit,Bit),Bit),Q<((Bit,Bit),(Bit,Bit))>){phase3(q)}",
            ErrorCode::Effect,
        ),
        (
            "use estimation::phase3; observe fn main()->Unit{phase3(join(join(init0(),init0()),join(init0(),init0())));()}",
            ErrorCode::Ownership,
        ),
    ] {
        root.main(source);
        assert_eq!(
            check_project(&root.0).unwrap_err().code,
            expected,
            "{source}"
        );
    }
}

#[test]
fn full_quantum_and_classical_pipeline_keeps_retry_probability() {
    let result = Root::example().run();
    let mut success = 0.0;
    let mut retry = 0.0;
    for y in 0..8 {
        let p = result.get(&bits(y, 3)).copied().unwrap_or(0.0);
        match factor_from_phase(15, 2, 3, y as u32).unwrap() {
            Some(factors) => {
                assert_eq!(
                    factors,
                    Factors {
                        period_candidate: 4,
                        factor: 3,
                        cofactor: 5
                    }
                );
                success += p;
            }
            None => retry += p,
        }
    }
    assert!((success - 0.5).abs() < 1e-12);
    assert!((retry - 0.5).abs() < 1e-12);
    assert_eq!(factor_from_phase(15, 2, 3, 0).unwrap(), None);
    assert_eq!(factor_from_phase(15, 2, 3, 4).unwrap(), None);
}

#[test]
fn classical_reconstruction_verifies_candidates_and_handles_failed_bases() {
    // An approximate phase 43/256 approximates 1/6. This tests continued
    // fractions beyond reduction of exactly representable dyadic fractions.
    assert_eq!(
        factor_from_phase(21, 2, 8, 43).unwrap(),
        Some(Factors {
            period_candidate: 6,
            factor: 3,
            cofactor: 7,
        })
    );
    assert_eq!(
        factor_from_phase(15, 4, 3, 4).unwrap(),
        Some(Factors {
            period_candidate: 2,
            factor: 3,
            cofactor: 5,
        })
    );
    // Period 2, but a^(r/2) = -1: changing the base is necessary.
    assert_eq!(factor_from_phase(15, 14, 3, 4).unwrap(), None);
    // Base 4 modulo 21 has odd order 3; no even candidate <21 here.
    assert_eq!(factor_from_phase(21, 4, 8, 85).unwrap(), None);
    for (args, expected) in [
        ((1, 2, 3, 0), PhaseInputError::Modulus),
        ((16, 3, 3, 0), PhaseInputError::Modulus),
        ((15, 1, 3, 0), PhaseInputError::Base),
        ((15, 15, 3, 0), PhaseInputError::Base),
        ((15, 3, 3, 0), PhaseInputError::Base),
        ((15, 2, 0, 0), PhaseInputError::Precision),
        ((15, 2, 33, 0), PhaseInputError::Precision),
        ((15, 2, 3, 8), PhaseInputError::Outcome),
    ] {
        assert_eq!(
            factor_from_phase(args.0, args.1, args.2, args.3),
            Err(expected)
        );
    }
    // Maximum-width multiplication and the 2^32 denominator must not overflow.
    assert_eq!(
        factor_from_phase(u32::MAX, u32::MAX - 1, 32, 1 << 31).unwrap(),
        None
    );
    assert_eq!(
        factor_from_phase(u32::MAX, u32::MAX - 1, 32, u32::MAX).unwrap(),
        None
    );
}

#[test]
fn continued_fractions_recover_small_usable_orders_from_rounded_phases() {
    // The oracle here finds the true order by exhaustive modular iteration,
    // independently of the continued-fraction implementation.
    let mut recovered = 0;
    for n in (3u32..64).step_by(2) {
        for a in 2..n {
            let mut value = 1;
            let mut order = None;
            let mut powers = vec![1];
            for r in 1..n {
                value = value * a % n;
                powers.push(value);
                if value == 1 {
                    order = Some(r);
                    break;
                }
            }
            let Some(r) = order else { continue };
            if r % 2 != 0 || powers[(r / 2) as usize] == 1 || powers[(r / 2) as usize] == n - 1 {
                continue;
            }
            // 2^16 > 2*n^2 ensures this rounded sample is close enough for
            // the reduced fraction 1/r to occur among the convergents.
            let y = ((1u32 << 16) + r / 2) / r;
            let factors = factor_from_phase(n, a, 16, y).unwrap().unwrap();
            assert_eq!(factors.period_candidate, r, "n={n} a={a} y={y}");
            assert_eq!(factors.factor * factors.cofactor, n);
            assert!(factors.factor > 1 && factors.cofactor > 1);
            recovered += 1;
        }
    }
    assert!(recovered > 100);
}
