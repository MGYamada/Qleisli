//! Boundary checks for finite source judgments, not a general soundness proof.

mod common;

use std::fs;

use common::SourceRoot;

use qleisli_core::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli_core::ir::{Effect, ProtectedUse, RawOp, SingleGate};
use qleisli_core::sim::{SimulationLimits, run_closed};

fn accepted(source: &str) {
    let root = SourceRoot::new(source);
    check_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
}

fn rejected(source: &str, expected: ErrorCode) {
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, expected, "{source}\n{error}");
}

#[test]
fn declared_effects_survive_arguments_tuples_conditions_and_both_arms() {
    let declarations = r#"
observe fn strong(v: Unit) -> Unit { v }
observe fn condition(b: CBit) -> CBit { b }
unitary fn keep(v: Unit) -> Unit { v }
"#;
    // Each callee emits no operations. Its declared effect must nevertheless
    // reach the caller through every ordinary composition rule.
    for body in [
        "keep(strong(()))",
        "let pair = (strong(()),()); ()",
        "strong(()); ()",
        "if condition(b) { () } else { () }",
        "if b { strong(()) } else { () }",
        "if b { () } else { strong(()) }",
    ] {
        rejected(
            &format!("{declarations} iso fn caller(b: CBit) -> Unit {{ {body} }}"),
            ErrorCode::Effect,
        );
        accepted(&format!(
            "{declarations} observe fn caller(b: CBit) -> Unit {{ {body} }}"
        ));
    }

    let root = SourceRoot::new(&format!(
        "{declarations} observe fn main() -> Unit {{ keep(strong(())) }}"
    ));
    let program = compile_project(&root.0).unwrap();
    assert_eq!(program.program().declared_effect, Effect::Observe);
    assert_eq!(program.derived_effect(), Effect::Unitary);
    assert!(program.program().operations.is_empty());
    assert!(program.program().quantum_outputs.is_empty());
    assert!(program.program().classical_outputs.is_empty());
}

#[test]
fn branch_local_shadows_expire_but_moved_outer_names_remain_reserved() {
    accepted(
        r#"
use std::quantum::h;
unitary fn restored(b: CBit, q: Q<Bit>) -> Q<Bit> {
    let q = if b { let h = q; h } else { q };
    h(q)
}
"#,
    );
    rejected(
        r#"
use std::quantum::h;
unitary fn reserved(b: CBit, h: Q<Bit>) -> Q<Bit> {
    let q = if b { let h = h; h } else { h };
    h(q)
}
"#,
        ErrorCode::TypeMismatch,
    );
    rejected(
        r#"
basis fn predicate(x: Bit) -> Bit { x }
unitary fn reserved(predicate: Q<Unit>, q: Q<Bit>) -> (Q<Unit>,Q<Bit>) {
    let saved = predicate;
    (saved,with_computed(q,predicate) { |a| a })
}
"#,
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn basis_domains_and_branch_results_preserve_exact_product_trees() {
    let predicate = "basis fn p(a: Bit, u: Unit, b: Bit) -> Bit { a xor b }";
    accepted(&format!(
        "{predicate} unitary fn oracle(q: Q<((Bit,Unit),Bit)>) -> Q<((Bit,Unit),Bit)> {{
            with_computed(q,p) {{ |a| a }}
        }}"
    ));
    // All three domains have two physical bits. Neither reassociation nor
    // removal of a zero-bit Unit component is an implicit type conversion.
    for basis in ["(Bit,(Unit,Bit))", "(Bit,Bit)"] {
        rejected(
            &format!(
                "{predicate} unitary fn oracle(q: Q<{basis}>) -> Q<{basis}> {{
                    with_computed(q,p) {{ |a| a }}
                }}"
            ),
            ErrorCode::TypeMismatch,
        );
    }
    rejected(
        "unitary fn different_trees(b: CBit) -> ((Unit,CBit),Unit) {
            if b { (((),b),()) } else { ((),(b,())) }
        }",
        ErrorCode::TypeMismatch,
    );
    accepted(
        "unitary fn explicit_regroup(q: Q<Bit>) -> Q<(Unit,Bit)> {
            do x <- q; pure ((),x)
        }",
    );
}

#[test]
fn basis_context_is_closed_and_has_its_own_callable_shadowing() {
    let function = "basis fn flip(x: Bit) -> Bit { not x }";
    // The surrounding ordinary value named flip is absent from the separate
    // basis context; the top-level basis function remains available there.
    accepted(&format!(
        "{function} unitary fn lifted(flip: Unit, q: Q<Bit>) -> Q<Bit> {{
            do x <- q; pure flip(x)
        }}"
    ));
    rejected(
        &format!(
            "{function} unitary fn lifted(q: Q<Bit>) -> Q<Bit> {{
                do flip <- q; pure flip(flip)
            }}"
        ),
        ErrorCode::TypeMismatch,
    );
    rejected(
        "unitary fn lifted(q: Q<Bit>) -> Q<Bit> { do x <- q; pure q }",
        ErrorCode::UnknownName,
    );
}

#[test]
fn computed_certificates_preserve_effects_and_outer_name_restrictions() {
    let prefix = r#"
use std::quantum::z;
basis fn p(x: Bit) -> Bit { x }
unitary fn forget(b: CBit) -> Unit { () }
"#;
    for classification in ["unitary", "iso", "observe"] {
        let source = format!(
            "{prefix}
            {classification} fn phase(a: Q<Bit>) -> Q<Bit> {{ z(a) }}
            unitary fn oracle(b: CBit, q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,p) {{ |a| forget(b); phase(a) }}
            }}"
        );
        if classification == "unitary" {
            accepted(&source);
            let root = SourceRoot::new(&format!(
                "{source}
                use std::quantum::init0;
                use std::observe::measure_z;
                observe fn main() -> CBit {{
                    let b = measure_z(init0());
                    measure_z(oracle(b,init0()))
                }}"
            ));
            let program = compile_project(&root.0).unwrap();
            let certificates: Vec<_> = program
                .program()
                .operations
                .iter()
                .filter_map(|operation| match operation {
                    RawOp::ComputeUseUncompute {
                        function, use_ops, ..
                    } => Some((function, use_ops)),
                    _ => None,
                })
                .collect();
            assert_eq!(certificates.len(), 1);
            assert_eq!(certificates[0].0, &[0, 1]);
            assert!(matches!(
                certificates[0].1.as_slice(),
                [ProtectedUse::ProtectedGate {
                    gate: SingleGate::Z,
                    ..
                }]
            ));
        } else {
            // Expanded gates alone qualify, but the source declaration still
            // exceeds the computed body's required Unitary classification.
            rejected(&source, ErrorCode::Effect);
        }
    }
    rejected(
        &format!(
            "{prefix} use std::quantum::init0;
            unitary fn prepare() -> Q<Bit> {{ with_computed(init0(),p) {{ |a| a }} }}"
        ),
        ErrorCode::Effect,
    );
    rejected(
        &format!(
            "{prefix} unitary fn hidden(z: Q<Unit>, q: Q<Bit>) -> (Q<Unit>,Q<Bit>) {{
                let q = with_computed(q,p) {{ |a| z(a) }};
                (z,q)
            }}"
        ),
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn ordinary_basis_and_computed_names_resolve_in_the_declaration_module() {
    let root = SourceRoot::new(
        r#"
use helper::ordinary;
use helper::lifted;
use helper::oracle;
use std::quantum::init0;
use std::quantum::h;
use std::observe::measure_z;
unitary fn flip(q: Q<Bit>) -> Q<Bit> { q }
basis fn predicate(x: Bit) -> Bit { 0 }
observe fn main() -> (CBit,(CBit,CBit)) {
    let a = ordinary(init0());
    let b = lifted(init0());
    let c = h(oracle(h(init0())));
    (measure_z(a),(measure_z(b),measure_z(c)))
}
"#,
    );
    fs::write(
        root.0.join("helper.qli"),
        r#"
use std::quantum::x;
use std::quantum::z;
unitary fn flip(q: Q<Bit>) -> Q<Bit> { x(q) }
basis fn predicate(x: Bit) -> Bit { not x }
pub unitary fn ordinary(q: Q<Bit>) -> Q<Bit> { flip(q) }
pub unitary fn lifted(q: Q<Bit>) -> Q<Bit> { do b <- q; pure predicate(b) }
pub unitary fn oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q,predicate) { |a| z(a) }
}
"#,
    )
    .unwrap();
    let program = compile_project(&root.0).unwrap();
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    // X|0>, the NOT lift, and H diag(-1,1) H|0> all measure as one.
    assert!((distribution.get(&vec![true; 3]).copied().unwrap_or(0.0) - 1.0).abs() < 1e-12);
    let unwanted: f64 = distribution
        .iter()
        .filter(|(bits, _)| **bits != [true; 3])
        .map(|(_, probability)| probability)
        .sum();
    assert!(unwanted.abs() < 1e-12);
}
