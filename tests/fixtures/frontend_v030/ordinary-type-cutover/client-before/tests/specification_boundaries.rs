//! Finite-v0 syntax and ownership regressions, not a soundness proof.

mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};

fn accepted(source: &str) {
    let root = SourceRoot::new(source);
    check_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
}

fn rejected(source: &str, expected: ErrorCode) {
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, expected, "{source}\n{error}");
}

fn deterministic(source: &str, expected: &[bool]) {
    let root = SourceRoot::new(source);
    let program = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    // Keep the raw weights: normalization could hide a lost measurement branch.
    assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
    assert!((distribution.get(expected).copied().unwrap_or(0.0) - 1.0).abs() < 1e-12);
    for (outcome, weight) in &distribution {
        if outcome.as_slice() != expected {
            assert!(weight.abs() < 1e-12, "unexpected {outcome:?}: {weight}");
        }
    }
}

#[test]
fn basis_lifts_destructure_exact_product_patterns() {
    accepted(
        r#"
iso fn duplicate(q: Q<(Bit,Bit)>) -> Q<((Bit,Bit),(Bit,Bit))> {
    do x <- q; pure (x,x)
}
unitary fn collapse_units(q: Q<(Unit,Unit)>) -> Q<Unit> {
    do x <- q; pure ()
}
"#,
    );
    accepted(
        "unitary fn swap(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
            do (a,b) <- q; pure (b,a)
        }",
    );
    accepted(
        "unitary fn remove_unit(q: Q<(Bit,Unit)>) -> Q<Bit> {
            do (a,_) <- q; pure a
        }
        unitary fn regroup(q: Q<(Bit,(Unit,Bit))>) -> Q<(Bit,Bit)> {
            do (a,(_,b)) <- q; pure (b,a)
        }",
    );
    // Basis declarations still use named parameters and expression bodies.
    rejected(
        "basis fn first(p: (Bit,Bit)) -> Bit { let (a,b) = p; a }",
        ErrorCode::Project,
    );
    accepted(
        r#"
use std::quantum::split;
use std::quantum::join;
unitary fn swap(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b) = split(q);
    join(b,a)
}
"#,
    );
}

#[test]
fn basis_patterns_reject_wrong_shapes_duplicate_names_and_lost_bits() {
    for source in [
        "unitary fn bad(q: Q<Bit>) -> Q<(Bit,Bit)> { do (a,b) <- q; pure (a,b) }",
        "unitary fn bad(q: Q<(Bit,(Bit,Bit))>) -> Q<((Bit,Bit),Bit)> {
            do ((a,b),c) <- q; pure ((a,b),c)
        }",
    ] {
        rejected(source, ErrorCode::TypeMismatch);
    }
    for source in [
        "unitary fn bad(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
            do (a,a) <- q; pure (a,a)
        }",
        "unitary fn bad(q: Q<(Bit,Bit)>) -> Q<Bit> { do (a,_) <- q; pure a }",
        "unitary fn bad(q: Q<Bit>) -> Q<Bit> { do _ <- q; pure 0 }",
    ] {
        rejected(source, ErrorCode::Ownership);
    }
    for a in [false, true] {
        for b in [false, true] {
            let left = if a { "x(init0())" } else { "init0()" };
            let right = if b { "x(init0())" } else { "init0()" };
            deterministic(
                &format!(
                    "use std::quantum::init0; use std::quantum::x;
                    use std::quantum::join; use std::quantum::split;
                    use std::observe::measure_z;
                    unitary fn regroup(q: Q<((Bit,Bit),Unit)>) -> Q<(Bit,Bit)> {{
                        do ((a,b),_) <- q; pure (b,a)
                    }}
                    observe fn main() -> (CBit,CBit) {{
                        let q = do p <- join({left},{right}); pure (p,());
                        let (b,a) = split(regroup(q));
                        (measure_z(b),measure_z(a))
                    }}"
                ),
                &[b, a],
            );
        }
    }
    // Removing a singleton basis factor must preserve phase, not just bits.
    deterministic(
        "use std::quantum::init0; use std::quantum::h;
        use std::observe::measure_z;
        observe fn main() -> CBit {
            let q = do a <- h(init0()); pure (a,());
            let q = do (a,_) <- q; pure a;
            measure_z(h(q))
        }",
        &[false],
    );
}

#[test]
fn zero_wire_ownership_requires_explicit_consumption() {
    rejected(
        "use std::quantum::split;
        unitary fn remove(q: Q<(Bit,Unit)>) -> Q<Bit> {
            let (b,u) = split(q); b
        }",
        ErrorCode::Ownership,
    );
    // A Unit basis result remains quantum ownership, not an ordinary Unit.
    rejected(
        "unitary fn remove(q: Q<Unit>) -> Unit { do u <- q; pure () }",
        ErrorCode::TypeMismatch,
    );
    rejected(
        "use std::observe::discard;
        unitary fn remove(q: Q<Unit>) -> Unit { discard(q) }",
        ErrorCode::Effect,
    );
    accepted(
        "use std::observe::discard;
        observe fn remove(q: Q<Unit>) -> Unit { discard(q) }",
    );
}

#[test]
fn basis_calls_ignore_outer_cbit_names_but_respect_basis_binders() {
    let declaration = "basis fn flip(x: Bit) -> Bit { not x }";
    accepted(&format!(
        "{declaration}
        unitary fn lifted(flip: CBit, q: Q<Bit>) -> Q<Bit> {{
            do x <- q; pure flip(x)
        }}"
    ));
    rejected(
        &format!(
            "{declaration}
            unitary fn lifted(q: Q<Bit>) -> Q<Bit> {{
                do flip <- q; pure flip(flip)
            }}"
        ),
        ErrorCode::TypeMismatch,
    );
    rejected(
        &format!(
            "{declaration}
            unitary fn lifted(q: Q<(Bit,Unit)>) -> Q<Bit> {{
                do (flip,_) <- q; pure flip(flip)
            }}"
        ),
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn computed_auxiliary_shadow_preserves_the_outer_owner() {
    let prefix = "use std::quantum::z; basis fn p(x: Bit) -> Bit { x }";
    deterministic(
        &format!(
            r#"{prefix}
use std::quantum::init0;
use std::quantum::x;
use std::quantum::h;
use std::observe::measure_z;
unitary fn keep(a: Q<Bit>, q: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
    let q = with_computed(q,p) {{ |a| z(a) }};
    (a,q)
}}
observe fn main() -> (CBit,CBit) {{
    let (a,q) = keep(x(init0()),h(init0()));
    (measure_z(a),measure_z(h(q)))
}}
"#
        ),
        // The outer a stays |1>; the predicate phase turns |+> into |->.
        &[true, true],
    );
    rejected(
        &format!(
            "{prefix}
            unitary fn lose(a: Q<Bit>, q: Q<Bit>) -> Q<Bit> {{
                with_computed(q,p) {{ |a| z(a) }}
            }}"
        ),
        ErrorCode::Ownership,
    );
}

#[test]
fn ordinary_cbit_literals_and_operators_have_their_truth_tables() {
    for source in [
        "unitary fn zero() -> CBit { 0 }",
        "unitary fn one() -> CBit { 1 }",
    ] {
        rejected(source, ErrorCode::Project);
    }
    for a in [false, true] {
        for b in [false, true] {
            deterministic(
                &format!(
                    "unitary fn booleans(a: CBit,b: CBit) -> (CBit,(CBit,CBit)) {{
                        (not a,(a and b,a xor b))
                    }}
                    observe fn main() -> (CBit,(CBit,CBit)) {{
                        booleans({a},{b})
                    }}"
                ),
                &[!a, a && b, a ^ b],
            );
            deterministic(
                &format!(
                    "unitary fn both(a: CBit,b: CBit) -> CBit {{
                        if a {{ b }} else {{ a }}
                    }}
                    observe fn main() -> CBit {{ both({a},{b}) }}"
                ),
                &[a && b],
            );
        }
    }
    deterministic(
        "observe fn main() -> (CBit,CBit) {
            (true xor false and false,not false and true xor true)
        }",
        &[true, false],
    );
}

#[test]
fn ordinary_boolean_operands_require_cbits_and_have_checked_dependencies() {
    // The computed certificate still accepts only a complete empty/Z/T IR
    // sequence, even when an extra classical instruction is harmless.
    rejected(
        "basis fn p(b:Bit)->Bit { b }
        unitary fn f(q:Q<Bit>)->Q<Bit> {
            with_computed(q,p) { |a| let unused = true; a }
        }",
        ErrorCode::Unsupported,
    );
    for source in [
        "unitary fn bad() -> CBit { not () }",
        "unitary fn bad() -> CBit { true and () }",
        "unitary fn bad() -> CBit { () xor false }",
        "unitary fn bad(q: Q<Bit>) -> CBit { not q }",
        "unitary fn bad(q: Q<Bit>) -> CBit { false and q }",
        "unitary fn bad() -> CBit { (true,false) xor false }",
    ] {
        rejected(source, ErrorCode::TypeMismatch);
    }
    for expression in ["not missing()", "false and missing()", "true xor missing()"] {
        rejected(
            &format!("unitary fn bad() -> CBit {{ {expression} }}"),
            ErrorCode::UnknownName,
        );
    }
    rejected(
        "unitary fn recursive(b: CBit) -> CBit { false and recursive(b) }",
        ErrorCode::RecursiveCall,
    );
}

#[test]
fn boolean_operands_are_eager_and_preserve_pending_quantum_ownership() {
    deterministic(
        "use std::quantum::init0; use std::quantum::x;
        use std::observe::measure_z;
        observe fn keep(pair: (Q<Bit>,Q<Bit>)) -> (Q<Bit>,CBit) {
            let (q,r) = pair;
            (q,false and measure_z(r))
        }
        observe fn main() -> (CBit,CBit) {
            let (q,b) = keep((x(init0()),x(init0())));
            (measure_z(q),b)
        }",
        &[true, false],
    );
    rejected(
        "use std::observe::measure_z;
        unitary fn bad(q: Q<Bit>) -> CBit { false and measure_z(q) }",
        ErrorCode::Effect,
    );
    rejected(
        "use std::observe::measure_z;
        observe fn bad(q: Q<Bit>) -> (CBit,Q<Bit>) {
            (false and measure_z(q),q)
        }",
        ErrorCode::Ownership,
    );
    // Both measurements must occur exactly once and in source order, even
    // when the first result forces an AND result of false.
    let root = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::x;
        use std::observe::measure_z;
        observe fn main() -> CBit {
            measure_z(init0()) and measure_z(x(init0()))
        }",
    );
    let program = compile_project(&root.0).unwrap();
    use qleisli::ir::RawOp;
    assert!(matches!(
        program.program().operations.as_slice(),
        [
            RawOp::Init0 { .. },
            RawOp::MeasureZ { .. },
            RawOp::Init0 { .. },
            RawOp::Gate { .. },
            RawOp::MeasureZ { .. },
            RawOp::ClassicalAnd { .. },
        ]
    ));
}

#[test]
fn basis_call_arity_is_distinct_from_lift_injectivity() {
    for (name, constant, identity) in [("xor2", "x", "0"), ("and2", "0", "1")] {
        let import = format!("use std::basis::{name};");
        rejected(
            &format!(
                "{import}
                unitary fn invalid(q: Q<(Bit,Bit)>) -> Q<Bit> {{
                    do p <- q; pure {name}(p)
                }}"
            ),
            ErrorCode::Arity,
        );
        // Both calls now have exactly two Bit arguments, but the induced
        // unary table is constant: xor2(x,x)=0 and and2(x,0)=0.
        rejected(
            &format!(
                "{import}
                unitary fn invalid(q: Q<Bit>) -> Q<Bit> {{
                    do x <- q; pure {name}(x,{constant})
                }}"
            ),
            ErrorCode::Ownership,
        );
        rejected(
            &format!(
                "{import}
                unitary fn invalid(q: Q<(Bit,Bit)>) -> Q<Bit> {{
                    do (a,b) <- q; pure {name}(a,b)
                }}"
            ),
            ErrorCode::Ownership,
        );
        accepted(&format!(
            "{import}
            iso fn retain_inputs(q: Q<(Bit,Bit)>) -> Q<((Bit,Bit),Bit)> {{
                do (a,b) <- q; pure ((a,b),{name}(a,b))
            }}"
        ));
        accepted(&format!(
            "{import}
            unitary fn identity(q: Q<Bit>) -> Q<Bit> {{
                do x <- q; pure {name}(x,{identity})
            }}"
        ));
    }
}

#[test]
fn entry_point_accepts_nested_classical_products() {
    deterministic(
        r#"
use std::quantum::init0;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> (Unit,(CBit,(CBit,Unit))) {
    ((),(measure_z(init0()),(measure_z(x(init0())),())))
}
"#,
        // Unit leaves carry no output bit; CBit leaves retain their tree order.
        &[false, true],
    );
}
