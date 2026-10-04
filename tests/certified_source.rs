//! Source-to-IR tests of the bounded exact semantic-contract extension.

mod common;

use std::collections::BTreeMap;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::RawOp;
use qleisli::sim::{SimulationLimits, run_closed};

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z; use std::observe::discard;
basis fn predicate(x: Bit) -> Bit { x }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
";

fn run(source: &str) -> BTreeMap<Vec<bool>, f64> {
    let root = SourceRoot::new(source);
    let program = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    result
}

fn probability(actual: &BTreeMap<Vec<bool>, f64>, outcome: &[bool], expected: f64) {
    assert!(
        (actual.get(outcome).copied().unwrap_or(0.0) - expected).abs() < 1e-12,
        "{actual:?}: expected {outcome:?} with probability {expected}"
    );
}

fn rejects(source: &str, code: ErrorCode) {
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, code, "{source}\n{error}");
}

#[test]
fn phase_oracle_and_auxiliary_hh_retain_physical_and_logical_circuits() {
    for (logical, body, expected) in [("z", "(d,z(a))", true), ("identity", "(d,h(h(a)))", false)] {
        let source = format!(
            "{IMPORTS}
            observe fn main() -> Bit {{
                let q = with_computed(h(init0()), predicate, {logical}) {{ |d,a| {body} }};
                measure_z(h(q))
            }}"
        );
        let root = SourceRoot::new(&source);
        let ir = compile_project(&root.0).unwrap();
        let (physical, meaning) = ir
            .program()
            .operations
            .iter()
            .find_map(|op| match op {
                RawOp::CertifiedCompute {
                    use_steps,
                    logical_steps,
                    ..
                } => Some((use_steps, logical_steps)),
                _ => None,
            })
            .expect("the generated IR retains the checked implementation");
        assert_eq!(physical.len(), if expected { 1 } else { 2 });
        assert_eq!(meaning.len(), usize::from(expected));
        probability(
            &run_closed(&ir, SimulationLimits::default()).unwrap(),
            &[expected],
            1.0,
        );
    }
}

#[test]
fn simultaneous_data_auxiliary_flip_preserves_reference_correlations() {
    let result = run(&format!(
        "{IMPORTS}
        observe fn main() -> (Bit,Bit) {{
            let (r,q) = cnot(h(init0()),init0());
            let q = with_computed(q,predicate,x) {{ |d,a| (x(d),x(a)) }};
            (measure_z(r),measure_z(q))
        }}"
    ));
    probability(&result, &[false, true], 0.5);
    probability(&result, &[true, false], 0.5);
}

#[test]
fn certified_phase_is_visible_against_a_correlated_reference() {
    let result = run(&format!(
        "{IMPORTS}
        observe fn main() -> (Bit,Bit) {{
            let (r,q) = cnot(h(init0()),init0());
            let q = with_computed(q,predicate,z) {{ |d,a| (d,z(a)) }};
            let (r,q) = cnot(r,q);
            (measure_z(h(r)),measure_z(q))
        }}"
    ));
    probability(&result, &[true, false], 1.0);
}

#[test]
fn explicit_contract_rejects_auxiliary_only_flip_and_wrong_logical_meaning() {
    for (logical, body) in [
        ("identity", "(d,x(a))"),
        ("identity", "(x(d),x(a))"),
        ("identity", "(d,z(a))"),
        ("z", "(d,t(a))"),
    ] {
        rejects(
            &format!(
                "{IMPORTS} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                    with_computed(q,predicate,{logical}) {{ |d,a| {body} }}
                }}"
            ),
            ErrorCode::InvalidIr,
        );
    }
}

#[test]
fn predicate_and_returned_axis_order_participate_in_the_equation() {
    let result = run(&format!(
        "{IMPORTS} observe fn main() -> Bit {{
            let q = with_computed(x(init0()),predicate,identity) {{ |d,a| (a,d) }};
            measure_z(q)
        }}"
    ));
    probability(&result, &[true], 1.0);
    for body in ["(a,d)", "(d,z(a))"] {
        rejects(
            &format!(
                "{IMPORTS} basis fn zero(x: Bit) -> Bit {{ 0 }}
                unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                    with_computed(q,zero,z) {{ |d,a| {body} }}
                }}"
            ),
            ErrorCode::InvalidIr,
        );
    }
}

#[test]
fn source_body_cannot_capture_or_lose_ownership() {
    for body in ["(d,x(r))", "(d,d)", "(d,init0())", "(d,a)"] {
        let extra = if body == "(d,a)" {
            "let spare = a;"
        } else {
            ""
        };
        rejects(
            &format!(
                "{IMPORTS} unitary fn candidate(q: Q<Bit>, r: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
                    let q = with_computed(q,predicate,identity) {{ |d,a| {extra} {body} }};
                    (q,r)
                }}"
            ),
            ErrorCode::Ownership,
        );
    }
}

#[test]
fn outer_classical_values_are_unavailable_but_closed_classical_branches_are_static() {
    rejects(
        &format!(
            "{IMPORTS} unitary fn candidate(flag: Bit, q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,predicate,identity) {{ |d,a| if flag {{ (d,a) }} else {{ (d,a) }} }}
            }}"
        ),
        ErrorCode::Ownership,
    );
    let result = run(&format!(
        "{IMPORTS} observe fn main() -> Bit {{
            let q = with_computed(init0(),predicate,identity) {{ |d,a|
                if 1 xor 0 {{ (d,h(h(a))) }} else {{ (d,a) }}
            }};
            measure_z(q)
        }}"
    ));
    probability(&result, &[false], 1.0);
}

#[test]
fn predicate_and_logical_names_obey_outer_shadowing() {
    for name in ["predicate", "identity"] {
        rejects(
            &format!(
                "{IMPORTS} unitary fn candidate({name}: Bit, q: Q<Bit>) -> Q<Bit> {{
                    with_computed(q,predicate,identity) {{ |d,a| (d,a) }}
                }}"
            ),
            ErrorCode::TypeMismatch,
        );
    }
    rejects(
        &format!(
            "{IMPORTS} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,predicate,identity) {{ |a,a| (a,a) }}
            }}"
        ),
        ErrorCode::Ownership,
    );
}

#[test]
fn temporary_binders_do_not_consume_shadowed_outer_owners() {
    let result = run(&format!(
        "{IMPORTS} observe fn main() -> (Bit,Bit) {{
            let a = x(init0());
            let q = with_computed(init0(),predicate,identity) {{ |d,a| (d,a) }};
            (measure_z(a),measure_z(q))
        }}"
    ));
    probability(&result, &[true, false], 1.0);
}

#[test]
fn exact_basis_shape_and_declared_unitary_effect_are_required() {
    for declaration in [
        "unitary fn specified(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> { q }",
        "iso fn specified(q: Q<Bit>) -> Q<Bit> { q }",
    ] {
        let code = if declaration.starts_with("iso") {
            ErrorCode::Effect
        } else {
            ErrorCode::TypeMismatch
        };
        rejects(
            &format!(
                "{IMPORTS} {declaration} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                    with_computed(q,predicate,specified) {{ |d,a| (d,a) }}
                }}"
            ),
            code,
        );
    }
    rejects(
        &format!(
            "{IMPORTS} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,predicate,identity) {{ |d,a|
                    let observed = measure_z(a); (d,init0())
                }}
            }}"
        ),
        ErrorCode::Effect,
    );
}

#[test]
fn zero_width_data_ownership_and_scalar_phase_are_preserved() {
    let source = format!(
        "{IMPORTS} basis fn yes(q: Unit) -> Bit {{ 1 }}
        unitary fn phase(q: Q<Unit>) -> Q<Unit> {{ with_computed(q,yes) {{ |a| z(a) }} }}
        unitary fn certified(q: Q<Unit>) -> Q<Unit> {{
            with_computed(q,yes,phase) {{ |d,a| (d,z(a)) }}
        }}
        unitary fn unit_identity(q: Q<Unit>) -> Q<Unit> {{ q }}
        observe fn main() -> Bit {{
            let q = do x <- init0(); pure ((),x);
            let (u,q) = split(q);
            let (c,u) = qif(h(init0()),u) {{ 0 => unit_identity, 1 => certified }};
            discard(u); discard(q); measure_z(h(c))
        }}"
    );
    probability(&run(&source), &[true], 1.0);
    rejects(
        &format!(
            "{IMPORTS} basis fn no(q: Unit) -> Bit {{ 0 }}
            unitary fn unit_identity(q: Q<Unit>) -> Q<Unit> {{ q }}
            unitary fn candidate(q: Q<Unit>) -> Q<Unit> {{
                with_computed(q,no,unit_identity) {{ |d,a| ((),a) }}
            }}"
        ),
        ErrorCode::Ownership,
    );
}

#[test]
fn certified_functions_support_adjoint_and_coherent_control() {
    let result = run(&format!(
        "{IMPORTS} unitary fn phase(q: Q<Bit>) -> Q<Bit> {{
            with_computed(q,predicate,t) {{ |d,a| (d,h(h(t(a)))) }}
        }}
        observe fn main() -> (Bit,Bit) {{
            let q = adjoint(phase,phase(h(init0())));
            let (c,tgt) = qif(h(init0()),x(init0())) {{ 0 => identity, 1 => phase }};
            discard(tgt);
            (measure_z(h(q)),measure_z(h(c)))
        }}"
    ));
    probability(&result, &[false, false], (1.0 + 1.0 / 2.0_f64.sqrt()) / 2.0);
    probability(&result, &[false, true], (1.0 - 1.0 / 2.0_f64.sqrt()) / 2.0);
}

#[test]
fn one_logical_client_accepts_two_phase_oracle_implementations() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS} use oracle::phase;
        observe fn main() -> Bit {{ measure_z(h(phase(h(init0())))) }}"
    ));
    for body in ["(d,z(a))", "(d,h(h(z(a))))"] {
        root.write(
            "oracle.qli",
            &format!(
                "{IMPORTS} pub unitary fn phase(q: Q<Bit>) -> Q<Bit> {{
                    with_computed(q,predicate,z) {{ |d,a| {body} }}
                }}"
            ),
        );
        let program = compile_project(&root.0).unwrap();
        probability(
            &run_closed(&program, SimulationLimits::default()).unwrap(),
            &[true],
            1.0,
        );
    }
}

#[test]
fn certified_source_checks_step_width_and_recursion_limits() {
    rejects(
        &format!(
            "{IMPORTS} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,predicate,identity) {{ |d,a| (d,repeat_static(1025,h,a)) }}
            }}"
        ),
        ErrorCode::Limit,
    );
    rejects(
        "basis fn predicate((((((a,b),c),d),e),f): (((((Bit,Bit),Bit),Bit),Bit),Bit)) -> Bit { a }
        unitary fn identity(q: Q<(((((Bit,Bit),Bit),Bit),Bit),Bit)>) -> Q<(((((Bit,Bit),Bit),Bit),Bit),Bit)> { q }
        unitary fn candidate(q: Q<(((((Bit,Bit),Bit),Bit),Bit),Bit)>) -> Q<(((((Bit,Bit),Bit),Bit),Bit),Bit)> {
            with_computed(q,predicate,identity) { |d,a| (d,a) }
        }",
        ErrorCode::Limit,
    );
    rejects(
        &format!(
            "{IMPORTS} unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,predicate,candidate) {{ |d,a| (d,a) }}
            }}"
        ),
        ErrorCode::RecursiveCall,
    );
}
