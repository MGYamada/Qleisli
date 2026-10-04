//! Finite source/IR correspondence examples, not a general soundness proof.

mod common;

use std::collections::BTreeMap;

use common::SourceRoot;

use common::accept;
use qleisli::AcceptedProgram;
use qleisli::frontend::compile::compile_project;
use qleisli::ir::RawOp;
use qleisli::sim::{SimulationLimits, run_closed};

fn compile(source: &str) -> AcceptedProgram {
    let root = SourceRoot::new(source);
    compile_project(&root.0).unwrap()
}

fn distribution(program: &AcceptedProgram) -> BTreeMap<Vec<bool>, f64> {
    run_closed(program, SimulationLimits::default()).unwrap()
}

fn assert_distribution(actual: &BTreeMap<Vec<bool>, f64>, expected: &[(&[bool], f64)]) {
    let expected: BTreeMap<Vec<bool>, f64> = expected
        .iter()
        .map(|(outcome, weight)| (outcome.to_vec(), *weight))
        .collect();
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

fn assert_both(source: &str, wrapped: &str, expanded: &str, expected: &[(&[bool], f64)]) {
    // Check both programs against the analytic distribution, so a common
    // source-to-IR error cannot pass merely because the programs agree.
    for body in [wrapped, expanded] {
        assert_distribution(
            &distribution(&compile(&source.replace("BODY", body))),
            expected,
        );
    }
}

#[test]
fn measured_actual_is_evaluated_once_before_classical_substitution() {
    let source = r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;
observe fn read_x(q: Q<Bit>) -> Bit { measure_z(h(q)) }
unitary fn pair(left: Bit, right: Bit) -> (Bit,Bit) { (left,right) }
unitary fn duplicate(b: Bit) -> (Bit,Bit) { pair(b,b) }
observe fn main() -> ((Bit,Bit),Bit) {
    let (a,r) = cnot(h(init0()),init0());
    BODY
}
"#;
    // Measuring one Bell half in X prepares the other half in the matching
    // X eigenstate. The two uses of b share one measurement outcome.
    assert_both(
        source,
        "let pair = duplicate(read_x(a)); (pair,measure_z(h(r)))",
        "let b = measure_z(h(a)); ((b,b),measure_z(h(r)))",
        &[(&[false, false, false], 0.5), (&[true, true, true], 0.5)],
    );
}

#[test]
fn call_substitution_respects_callee_scope_and_restores_shadowed_classical_names() {
    for (flag, other) in [(false, false), (false, true), (true, false), (true, true)] {
        let source = format!(
            r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::z;
use std::observe::measure_z;
unitary fn phase(flag: Bit, q: Q<Bit>) -> Q<Bit> {{
    if flag {{ z(q) }} else {{ q }}
}}
unitary fn wrapped(flag: Bit, q: Q<Bit>, other: Bit) -> (Bit,Q<Bit>) {{
    let selected = if flag {{ let flag = other; flag }} else {{ let flag = other; flag }};
    (flag,phase(selected,q))
}}
observe fn main() -> ((Bit,Bit),(Bit,Bit)) {{
    let flag = measure_z({});
    let other = measure_z({});
    let phase = other;
    let q = h(init0());
    BODY
}}
"#,
            if flag { "x(init0())" } else { "init0()" },
            if other { "x(init0())" } else { "init0()" },
        );
        // The caller's local `phase` must not capture the callee's function
        // name. Branch-local `flag` bindings must not replace its parameter.
        assert_both(
            &source,
            "let (saved,q) = wrapped(flag,q,other); ((flag,phase),(saved,measure_z(h(q))))",
            "let q = if other { z(q) } else { q }; ((flag,phase),(flag,measure_z(h(q))))",
            &[(&[flag, other, flag, other], 1.0)],
        );
    }
}

#[test]
fn nested_call_preserves_conditional_phase_against_an_entangled_caller_frame() {
    let source = r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::z;
use std::quantum::t;
use std::quantum::cnot;
use std::observe::measure_z;
unitary fn phased(b: Bit, q: Q<Bit>) -> Q<Bit> {
    if b { t(q) } else { z(t(q)) }
}
unitary fn relay(mixed: (Bit,Q<Bit>)) -> Q<Bit> {
    let (b,q) = mixed;
    phased(b,q)
}
observe fn main() -> (Bit,(Bit,Bit)) {
    let (a,r) = cnot(h(init0()),init0());
    let b = measure_z(h(init0()));
    BODY
    let (a,r) = cnot(a,r);
    (b,(measure_z(h(a)),measure_z(r)))
}
"#;
    // After unentangling, T gives P(X=0)=(2+sqrt(2))/4; ZT reverses
    // those probabilities. Each independently chosen branch has weight 1/2.
    let high = (2.0 + 2.0_f64.sqrt()) / 8.0;
    let low = (2.0 - 2.0_f64.sqrt()) / 8.0;
    assert_both(
        source,
        "let a = relay((b,a));",
        "let a = if b { t(a) } else { z(t(a)) };",
        &[
            (&[false, false, false], low),
            (&[false, true, false], high),
            (&[true, false, false], high),
            (&[true, true, false], low),
        ],
    );
}

#[test]
fn simultaneous_phi_order_preserves_mixed_results_zero_width_and_bell_coherence() {
    let source = r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::z;
use std::quantum::cnot;
use std::quantum::split;
use std::observe::measure_z;
use std::observe::discard;
observe fn main() -> ((Bit,Bit),((Bit,Bit),(Bit,Bit))) {
    let (a,r) = cnot(h(init0()),init0());
    let (u,a) = split(do k <- a; pure ((),k));
    let b = measure_z(h(init0()));
    let zero = measure_z(init0());
    let one = measure_z(x(init0()));
    let (((c,u),(d,a)),e) = if b {
        (((one,u),(zero,z(a))),one)
    } else {
        (((zero,u),(one,a)),zero)
    };
    discard(u);
    let (a,r) = cnot(a,r);
    ((b,c),((d,e),(measure_z(h(a)),measure_z(r))))
}
"#;
    let checked = compile(source);
    let expected: &[(&[bool], f64)] = &[
        (&[false, false, true, false, false, false], 0.5),
        (&[true, true, false, true, true, false], 0.5),
    ];
    assert_distribution(&distribution(&checked), expected);

    let mut reordered = checked.program().clone();
    let mut reordered_branches = 0;
    for op in &mut reordered.operations {
        if let RawOp::ClassicalBranch {
            quantum_phis,
            classical_phis,
            ..
        } = op
        {
            assert_eq!(classical_phis.len(), 3);
            assert_eq!(quantum_phis.len(), 3);
            assert!(quantum_phis.iter().any(|phi| phi.output_wires.is_empty()));
            // Each input belongs to an arm before the merge. Changing the
            // order of assignments must not change any selected value or axis.
            classical_phis.reverse();
            quantum_phis.reverse();
            reordered_branches += 1;
        }
    }
    assert_eq!(reordered_branches, 1);
    let reordered = accept(reordered).unwrap();
    assert_distribution(&distribution(&reordered), expected);
}
