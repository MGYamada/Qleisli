//! Fixed-width M1 source/evidence regressions; not a general soundness proof.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};

const PRELUDE: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z; use std::observe::discard;
unitary fn ident(q:Q<Bit>)->Q<Bit>{q}
unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)}
unitary fn phase(q:Q<Bit>)->Q<Bit>{t(q)}
unitary fn had(q:Q<Bit>)->Q<Bit>{h(q)}
unitary fn direct_z(q:Q<Bit>)->Q<Bit>{z(q)}
basis fn z_phase(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn use_op[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
";

#[test]
fn shipped_contract_examples_execute_after_reserved_module_migration() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    for (name, bits) in [
        ("operation_contracts", vec![true, true]),
        ("function_contracts", vec![true, false, true]),
    ] {
        let program = compile_project(&root.join(name)).unwrap();
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert!((result[&bits] - 1.0).abs() < 1e-12, "{name}: {result:?}");
    }
}

fn check(source: &str) {
    let root = SourceRoot::new(&format!("{PRELUDE}{source}"));
    check_project(&root.0).unwrap_or_else(|e| panic!("{source}\n{e}"));
}

#[test]
fn new_grammar_imports_documentation_and_depth_limits_are_explicit() {
    use qleisli::frontend::documentation::render_markdown;
    use qleisli::frontend::parser::parse_module;
    let source = "/// A phase-fixed contract.\nmeaning M:Bit=phase_by(phi);\n\
        /// Requires explicit access.\nunitary fn helper[static U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}";
    let rendered = render_markdown(source).unwrap();
    assert!(rendered.contains("meaning M:Bit=phase_by(phi);"));
    assert!(rendered.contains("requires Apply(U)"));
    for source in [
        "unitary fn f[static U:Op<Bit>,](q:Q<Bit>)->Q<Bit>{q}",
        "basis fn f[static U:Op<Bit>](b:Bit)->Bit{b}",
        "unitary fn f(q:Q<Bit>)->Q<Bit>{g[repeat_op(01,u)](q)}",
        "unitary fn f(q:Q<Bit>)->Q<Bit>{inverse_op(u)}",
        "unitary fn meaning(q:Q<Bit>)->Q<Bit>{q}",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
    // These are existing sized spellings now represented by the common AST.
    // Complete source checking resolves the callee before concrete count limits.
    parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{g[](q)}").unwrap();
    let source = "unitary fn f(q:Q<Bit>)->Q<Bit>{g[repeat_op(4097,u)](q)}";
    parse_module(source).unwrap();
    let root = SourceRoot::new(source);
    assert_eq!(
        check_project(&root.0).unwrap_err().code,
        ErrorCode::UnknownName
    );
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let source = format!(
                "unitary fn f(q:Q<Bit>)->Q<Bit>{{g[{}u{}](q)}}",
                "inverse_op(".repeat(1000),
                ")".repeat(1000)
            );
            assert!(parse_module(&source).unwrap_err().message.contains("limit"));
        })
        .unwrap()
        .join()
        .unwrap();
    let root = SourceRoot::new(
        "use meanings::Flip; use meanings::implementation;
        unitary fn run[static U:Op<Bit,Flip>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
        unitary fn client(q:Q<Bit>)->Q<Bit>{run[bind_op(implementation,Flip)](q)}",
    );
    root.write(
        "meanings.qli",
        "use std::quantum::x; basis fn flip(b:Bit)->Bit{not b}
        pub meaning Flip:Bit=permutation_by(flip);
        pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}",
    );
    check_project(&root.0).unwrap();
    root.write(
        "meanings.qli",
        "basis fn flip(b:Bit)->Bit{not b} meaning Flip:Bit=permutation_by(flip);
        pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{q}",
    );
    assert_eq!(check_project(&root.0).unwrap_err().code, ErrorCode::Project);
}

fn rejects(source: &str, code: ErrorCode) {
    let root = SourceRoot::new(&format!("{PRELUDE}{source}"));
    let e = check_project(&root.0).unwrap_err();
    assert_eq!(e.code, code, "{source}\n{e}");
}

fn deterministic(source: &str, bits: &[bool]) {
    let root = SourceRoot::new(&format!("{PRELUDE}{source}"));
    let program = compile_project(&root.0).unwrap_or_else(|e| panic!("{source}\n{e}"));
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!(
        (result.get(bits).copied().unwrap_or_default() - 1.0).abs() < 1e-12,
        "{result:?}"
    );
}

#[test]
fn unchanged_generic_client_accepts_two_independent_providers_and_retains_receipts() {
    let root = SourceRoot::new(&format!(
        "{PRELUDE}
        use provider::implementation;
        unitary fn client[static U:Op<Bit,ZMeaning>](q:Q<Bit>)->Q<Bit>
        requires Apply(U), Controlled(U) {{ U(q) }}
        observe fn main()->(Bit,Bit) {{
            let (r,q)=cnot(h(init0()),init0());
            let q=client[bind_op(implementation,ZMeaning)](q);
            let (r,q)=cnot(r,q);
            (measure_z(h(r)),measure_z(q))
        }}"
    ));
    for body in ["z(q)", "repeat_static(4,t,q)"] {
        root.write(
            "provider.qli",
            &format!(
                "use std::quantum::z; use std::quantum::t;
            pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{{{body}}}"
            ),
        );
        let p = compile_project(&root.0).unwrap();
        assert!(
            (run_closed(&p, SimulationLimits::default()).unwrap()[&vec![true, false]] - 1.0).abs()
                < 1e-12
        );
        let receipt = p
            .program()
            .operations
            .iter()
            .find_map(|op| match op {
                RawOp::ApplyUnitary { steps, .. } => steps.iter().find_map(|s| match &s.action {
                    CircuitAction::Contract { evidence, .. } => Some(evidence),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap();
        assert_eq!(receipt.identity().specification, "meaning main::ZMeaning");
        assert!(
            receipt
                .identity()
                .sources
                .iter()
                .any(|(_, s)| s.contains(body))
        );
    }
    root.write(
        "provider.qli",
        "use std::quantum::x; pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}",
    );
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        ErrorCode::Contract
    );
}

#[test]
fn all_constructors_match_independent_full_operator_specifications() {
    for (description, expected) in [
        ("inverse_op(phase)", "adjoint(t,q)"),
        ("then_op(had,phase)", "t(h(q))"),
        ("repeat_op(3,phase)", "t(t(t(q)))"),
        ("repeat_op(0,phase)", "q"),
        ("conjugate_op(phase,had)", "t(h(adjoint(t,q)))"),
    ] {
        check(&format!(
            "unitary fn actual(q:Q<Bit>)->Q<Bit>{{use_op[{description}](q)}}
            unitary fn expected(q:Q<Bit>)->Q<Bit>{{{expected}}}
            unitary fn compare(q:Q<Bit>)->Q<Bit>{{apply_contract(actual,expected,q)}}"
        ));
    }
    for (description, body) in [
        (
            "tensor_op(phase,had)",
            "let (a,b)=split(q); join(t(a),h(b))",
        ),
        (
            "controlled_op(phase)",
            "let (a,b)=split(q); let (a,b)=qif(a,b){0=>ident,1=>phase}; join(a,b)",
        ),
        (
            "inverse_op(controlled_op(phase))",
            "let (a,b)=split(q); let (a,b)=qif(a,b){0=>ident,1=>inv}; join(a,b)",
        ),
    ] {
        check(&format!("unitary fn inv(q:Q<Bit>)->Q<Bit>{{adjoint(t,q)}}
            unitary fn pair_op[static U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> requires Apply(U){{U(q)}}
            unitary fn actual(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{pair_op[{description}](q)}}
            unitary fn expected(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{{body}}}
            unitary fn compare(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{apply_contract(actual,expected,q)}}"));
    }
}

#[test]
fn control_conjugation_needs_no_controlled_basis_change_and_keeps_phase() {
    // V=T; W=H followed by T. Both order and non-Hermitian inverse matter.
    check("unitary fn middle(q:Q<Bit>)->Q<Bit>{t(h(q))}
        unitary fn ctrl[static V:Op<Bit>,static W:Op<Bit>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
        requires Apply(V),Adjoint(V),Controlled(W){pair_apply[controlled_op(conjugate_op(V,W))](q)}
        unitary fn pair_apply[static U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> requires Apply(U){U(q)}
        unitary fn full(q:Q<Bit>)->Q<Bit>{t(middle(adjoint(t,q)))}
        unitary fn actual(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{ctrl[phase,middle](q)}
        unitary fn expected(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let(c,q)=split(q); let(c,q)=qif(c,q){0=>ident,1=>full};join(c,q)}
        unitary fn compare(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{apply_contract(actual,expected,q)}");
}

#[test]
fn parameter_adjoint_repeat_and_both_qif_polarities_are_correct() {
    deterministic(
        "unitary fn transform[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>
        requires Apply(U),Adjoint(U){adjoint(U,repeat_static(5,U,q))}
        unitary fn coherent[static U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
        requires Controlled(U){qif(c,q){0=>U,1=>ident}}
        observe fn main()->(Bit,Bit){
            let q=transform[phase](h(init0()));
            let(c,q)=coherent[direct_z](init0(),q);
            (measure_z(c),measure_z(h(q)))
        }",
        &[false, false],
    );
}

#[test]
fn scalar_phase_and_zero_width_ownership_survive_control() {
    deterministic(
        "basis fn yes(u:Unit)->Bit{1}
        basis fn scalar(u:Unit)->(Bit,(Bit,Bit)){(0,(0,1))}
        meaning Minus:Unit=phase_by(scalar);
        unitary fn minus(q:Q<Unit>)->Q<Unit>{with_computed(q,yes){|a|z(a)}}
        unitary fn zero(q:Q<Unit>)->Q<Unit>{q}
        unitary fn ctrl[static U:Op<Unit,Minus>](c:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>)
        requires Controlled(U){qif(c,q){0=>U,1=>zero}}
        observe fn main()->Bit{let q=do b<-init0();pure ((),b);let(e,b)=split(q);discard(b);
            let(c,e)=ctrl[bind_op(minus,Minus)](h(init0()),e);discard(e);measure_z(h(c))}",
        &[true],
    );
    rejects(
        "unitary fn bad[static U:Op<Unit>](q:Q<Unit>)->(Q<Unit>,Q<Unit>) requires Apply(U){(U(q),q)}",
        ErrorCode::Ownership,
    );
}

#[test]
fn generic_bodies_cannot_borrow_undeclared_access_from_concrete_providers() {
    for (constraints, body) in [
        ("Apply(U)", "adjoint(U,q)"),
        ("Controlled(U)", "U(q)"),
        ("Adjoint(U)", "repeat_static(0,U,q)"),
        ("Apply(U)", "if 0 {adjoint(U,q)} else {q}"),
        ("Apply(U)", "use_op[inverse_op(U)](q)"),
        ("Adjoint(U)", "use_op[repeat_op(0,U)](q)"),
        ("Apply(U)", "use_op[conjugate_op(U,U)](q)"),
    ] {
        rejects(&format!("unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires {constraints}{{{body}}}
            unitary fn caller(q:Q<Bit>)->Q<Bit>{{bad[direct_z](q)}}"),ErrorCode::Capability);
    }
    rejects(
        "unitary fn bad[static U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Apply(U){qif(c,q){0=>ident,1=>U}}",
        ErrorCode::Capability,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{U(q)}",
        ErrorCode::Capability,
    );
}

#[test]
fn controlled_only_access_derives_transparent_inverse_and_controlled_circuits() {
    // A020-09: preserve M1's transparent constructor rules until a versioned
    // migration; this does not grant direct Apply(U) or Adjoint(U).
    // T is non-Hermitian, so replacing its derived inverse by T must fail.
    for body in [
        "let (c,q) = ctrl[inverse_op(U)](c,q); join(c,q)",
        "adjoint2[controlled_op(U)](join(c,q))",
        "adjoint2[controlled_op(U)](apply2[controlled_op(U)](adjoint2[controlled_op(U)](join(c,q))))",
    ] {
        deterministic(
            &format!(
                "unitary fn ctrl[static U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
                 requires Controlled(U){{qif(c,q){{0=>ident,1=>U}}}}
                 unitary fn apply2[static V:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
                 requires Apply(V){{V(q)}}
                 unitary fn adjoint2[static V:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
                 requires Adjoint(V){{adjoint(V,q)}}
                 unitary fn derived[static U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->Q<(Bit,Bit)>
                 requires Controlled(U){{{body}}}
                 observe fn main()->(Bit,Bit){{
                     let (c,q) = split(derived[phase](x(init0()),t(h(init0()))));
                     (measure_z(x(c)),measure_z(h(q)))
                 }}"
            ),
            &[false, false],
        );
    }
    for body in ["U(q)", "adjoint(U,q)", "use_op[inverse_op(U)](q)"] {
        rejects(
            &format!(
                "unitary fn direct[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>
                 requires Controlled(U){{{body}}}"
            ),
            ErrorCode::Capability,
        );
    }
}

#[test]
fn meanings_reject_wrong_phase_wrong_tree_and_nonpermutations() {
    rejects(
        "unitary fn client[static U:Op<Bit,ZMeaning>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{client[flip](q)}",
        ErrorCode::Contract,
    );
    rejects(
        "unitary fn minus_z(q:Q<Bit>)->Q<Bit>{x(z(x(q)))}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[bind_op(minus_z,ZMeaning)](q)}",
        ErrorCode::Contract,
    );
    rejects(
        "basis fn constant(b:Bit)->Bit{0} meaning Bad:Bit=permutation_by(constant);",
        ErrorCode::Contract,
    );
    rejects(
        "basis fn wrong(b:Bit)->Bit{b} meaning Bad:Bit=phase_by(wrong);",
        ErrorCode::TypeMismatch,
    );
    rejects(
        "unitary fn wrong(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{q}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[wrong](q)}",
        ErrorCode::TypeMismatch,
    );
    rejects(
        "observe fn wrong(q:Q<Bit>)->Q<Bit>{let b=measure_z(init0());q}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[wrong](q)}",
        ErrorCode::Effect,
    );
}

#[test]
fn generic_cleanup_obligations_are_discharged_for_each_actual_instance() {
    let generic = "basis fn pred(b:Bit)->Bit{b}
        unitary fn clean[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){
            with_computed(q,pred,direct_z){|d,a|(d,U(a))}}
        unitary fn client(q:Q<Bit>)->Q<Bit>{clean[PROVIDER](q)}";
    check(&generic.replace("PROVIDER", "direct_z"));
    rejects(&generic.replace("PROVIDER", "flip"), ErrorCode::InvalidIr);
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){apply_contract(U,direct_z,q)}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn pending_call_frames_declared_effects_and_local_shadowing_are_preserved() {
    deterministic("unitary fn pair[static U:Op<Bit>](a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Apply(U){(a,U(b))}
        observe fn main()->(Bit,Bit){let (a,b)=cnot(h(init0()),init0());
            let(a,b)=pair[ident](a,if 1 {b} else {b});(measure_z(a) xor measure_z(b),0)}", &[false,false]);
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){let U=q;U(U)}",
        ErrorCode::TypeMismatch,
    );
    rejects(
        "observe fn obs[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){let b=measure_z(init0());U(q)}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{obs[ident](q)}",
        ErrorCode::Effect,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){use_op[q](q)}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn unused_generic_declarations_and_static_dependencies_are_checked() {
    rejects(
        "unitary fn bad[static U:Op<Bit>,static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
        ErrorCode::Ownership,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](U:Q<Bit>)->Q<Bit>{U}",
        ErrorCode::Ownership,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U),Apply(U){q}",
        ErrorCode::Capability,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(missing){q}",
        ErrorCode::UnknownName,
    );
    rejects(
        "unitary fn cycle(q:Q<Bit>)->Q<Bit>{use_op[repeat_op(0,cycle)](q)}",
        ErrorCode::RecursiveCall,
    );
    rejects(
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op(q)}",
        ErrorCode::Arity,
    );
    rejects(
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{h[phase](q)}",
        ErrorCode::Arity,
    );
    rejects(
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{ZMeaning(q)}",
        ErrorCode::TypeMismatch,
    );
    rejects(
        "unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{let v=U;q}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn static_basis_errors_and_concrete_step_instance_limits_reject_without_panics() {
    rejects("unitary fn dual[static U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controlled(U){qif(c,q){0=>U,1=>U}}
        unitary fn bad(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){dual[repeat_op(513,phase)](c,q)}", ErrorCode::Limit);
    rejects(
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[repeat_op(1025,phase)](q)}",
        ErrorCode::Limit,
    );
    let too_wide = "controlled_op(".repeat(6) + "phase" + &")".repeat(6);
    rejects(
        &format!("unitary fn bad(q:Q<Bit>)->Q<Bit>{{use_op[{too_wide}](q)}}"),
        // This deliberately wrong Op basis fails before a concrete width limit.
        ErrorCode::TypeMismatch,
    );
    let mut source = String::new();
    // Structurally different, valid identity descriptions remain distinct instances.
    for n in 0..257 {
        source.push_str(&format!(
            "unitary fn f{n}(q:Q<Bit>)->Q<Bit>{{use_op[repeat_op({n},ident)](q)}}"
        ));
    }
    let root = SourceRoot::new(&format!("{PRELUDE}{source}"));
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(error.message.contains("256 distinct"), "{error}");
}

#[test]
fn lexical_runtime_binding_rejects_static_shadow_before_later_calls() {
    // Both original sources fail at the preceding let; later call arguments
    // cannot make an illegal static-name shadow binding valid.
    for source in [
        include_str!(
            "fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-missing-argument/main.qli"
        ),
        include_str!(
            "fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-valid-argument/main.qli"
        ),
    ] {
        let root = SourceRoot::new(source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch);
        assert_eq!(error.message, "binding U shadows a static parameter/index");
        assert_eq!(&source[error.span.start..error.span.end], "U");
        assert_eq!(error.span.start, source.find("let U").unwrap() + 4);
    }
}
