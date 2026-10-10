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
classical fn z_phase(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn use_op[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
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
        /// Requires explicit access.\nunitary fn helper[const U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}";
    let rendered = render_markdown(source).unwrap();
    assert!(rendered.contains("meaning M:Bit=phase_by(phi);"));
    assert!(rendered.contains("requires Applicable(U)"));
    for source in [
        "unitary fn f[const U:Op<Bit>,](q:Q<Bit>)->Q<Bit>{q}",
        "classical fn f[const U:Op<Bit>](b:Bit)->Bit{b}",
        "unitary fn f(q:Q<Bit>)->Q<Bit>{g[power(u,01)](q)}",
        "unitary fn f(q:Q<Bit>)->Q<Bit>{adjoint(u)}",
        "unitary fn meaning(q:Q<Bit>)->Q<Bit>{q}",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
    // These are existing sized spellings now represented by the common AST.
    // Complete source checking resolves the callee before concrete count limits.
    parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{g[](q)}").unwrap();
    let source = "unitary fn f(q:Q<Bit>)->Q<Bit>{g[power(u,4097)](q)}";
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
                "adjoint(".repeat(1000),
                ")".repeat(1000)
            );
            assert!(parse_module(&source).unwrap_err().message.contains("limit"));
        })
        .unwrap()
        .join()
        .unwrap();
    let root = SourceRoot::new(
        "use meanings::Flip; use meanings::implementation;
        unitary fn run[const U:Op<Bit,Flip>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        unitary fn client(q:Q<Bit>)->Q<Bit>{run[checked_op(implementation,Flip)](q)}",
    );
    root.write(
        "meanings.qli",
        "use std::quantum::x; classical fn flip(b:Bit)->Bit{not b}
        pub meaning Flip:Bit=permutation_by(flip);
        pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}",
    );
    check_project(&root.0).unwrap();
    root.write(
        "meanings.qli",
        "classical fn flip(b:Bit)->Bit{not b} meaning Flip:Bit=permutation_by(flip);
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
        unitary fn client[const U:Op<Bit,ZMeaning>](q:Q<Bit>)->Q<Bit>
        requires Applicable(U), Controllable(U) {{ U(q) }}
        observe fn main()->(Bit,Bit) {{
            let (r,q)=cnot(h(init0()),init0());
            let q=client[checked_op(implementation,ZMeaning)](q);
            let (r,q)=cnot(r,q);
            (measure_z(h(r)),measure_z(q))
        }}"
    ));
    for body in ["z(q)", "power(t,4)(q)"] {
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
        ("adjoint(phase)", "adjoint(t)(q)"),
        ("then_op(had,phase)", "t(h(q))"),
        ("power(phase,3)", "t(t(t(q)))"),
        ("power(phase,0)", "q"),
        ("conjugate_op(phase,had)", "t(h(adjoint(t)(q)))"),
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
            "controlled(phase)",
            "let (a,b)=split(q); let (a,b)=qif(a,b){0=>ident,1=>phase}; join(a,b)",
        ),
        (
            "adjoint(controlled(phase))",
            "let (a,b)=split(q); let (a,b)=qif(a,b){0=>ident,1=>inv}; join(a,b)",
        ),
    ] {
        check(&format!("unitary fn inv(q:Q<Bit>)->Q<Bit>{{adjoint(t)(q)}}
            unitary fn pair_op[const U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> requires Applicable(U){{U(q)}}
            unitary fn actual(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{pair_op[{description}](q)}}
            unitary fn expected(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{{body}}}
            unitary fn compare(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{apply_contract(actual,expected,q)}}"));
    }
}

#[test]
fn control_conjugation_needs_no_controlled_basis_change_and_keeps_phase() {
    // V=T; W=H followed by T. Both order and non-Hermitian inverse matter.
    check("unitary fn middle(q:Q<Bit>)->Q<Bit>{t(h(q))}
        unitary fn ctrl[const V:Op<Bit>,const W:Op<Bit>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
        requires Applicable(V),Adjointable(V),Controllable(W){pair_apply[controlled(conjugate_op(V,W))](q)}
        unitary fn pair_apply[const U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> requires Applicable(U){U(q)}
        unitary fn full(q:Q<Bit>)->Q<Bit>{t(middle(adjoint(t)(q)))}
        unitary fn actual(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{ctrl[phase,middle](q)}
        unitary fn expected(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let(c,q)=split(q); let(c,q)=qif(c,q){0=>ident,1=>full};join(c,q)}
        unitary fn compare(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{apply_contract(actual,expected,q)}");
}

#[test]
fn parameter_adjoint_repeat_and_both_qif_polarities_are_correct() {
    deterministic(
        "unitary fn transform[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
        requires Applicable(U),Adjointable(U){adjoint(U)(power(U,5)(q))}
        unitary fn coherent[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
        requires Controllable(U){qif(c,q){0=>U,1=>ident}}
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
        "classical fn yes(u:Unit)->Bit{1}
        classical fn scalar(u:Unit)->(Bit,(Bit,Bit)){(0,(0,1))}
        meaning Minus:Unit=phase_by(scalar);
        unitary fn minus(q:Q<Unit>)->Q<Unit>{with_computed(q,yes){|a|z(a)}}
        unitary fn zero(q:Q<Unit>)->Q<Unit>{q}
        unitary fn ctrl[const U:Op<Unit,Minus>](c:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>)
        requires Controllable(U){qif(c,q){0=>U,1=>zero}}
        observe fn main()->Bit{let q=basis init0() as b { ((),b) };let(e,b)=split(q);discard(b);
            let(c,e)=ctrl[checked_op(minus,Minus)](h(init0()),e);discard(e);measure_z(h(c))}",
        &[true],
    );
    rejects(
        "unitary fn bad[const U:Op<Unit>](q:Q<Unit>)->(Q<Unit>,Q<Unit>) requires Applicable(U){(U(q),q)}",
        ErrorCode::Ownership,
    );
}

#[test]
fn generic_bodies_cannot_borrow_undeclared_access_from_concrete_providers() {
    for (constraints, body) in [
        ("Applicable(U)", "adjoint(U)(q)"),
        ("Controllable(U)", "U(q)"),
        ("Adjointable(U)", "power(U,0)(q)"),
        ("Applicable(U)", "if 0 {adjoint(U)(q)} else {q}"),
        ("Applicable(U)", "use_op[adjoint(U)](q)"),
        ("Adjointable(U)", "use_op[power(U,0)](q)"),
        ("Applicable(U)", "use_op[conjugate_op(U,U)](q)"),
    ] {
        rejects(
            &format!(
                "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires {constraints}{{{body}}}
            unitary fn caller(q:Q<Bit>)->Q<Bit>{{bad[direct_z](q)}}"
            ),
            ErrorCode::Capability,
        );
    }
    rejects(
        "unitary fn bad[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){qif(c,q){0=>ident,1=>U}}",
        ErrorCode::Capability,
    );
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{U(q)}",
        ErrorCode::Capability,
    );
}

#[test]
fn controlled_only_access_derives_transparent_inverse_and_controlled_circuits() {
    // Reversing a constructed controlled circuit uses its retained exact body.
    // Constructing the bare operand's adjoint still needs Adjointable(U).
    // T is non-Hermitian, so replacing its derived inverse by T must fail.
    for (body, extra) in [
        (
            "let (c,q) = ctrl[adjoint(U)](c,q); join(c,q)",
            ",Adjointable(U)",
        ),
        ("adjoint2[controlled(U)](join(c,q))", ""),
        (
            "adjoint2[controlled(U)](apply2[controlled(U)](adjoint2[controlled(U)](join(c,q))))",
            "",
        ),
    ] {
        deterministic(
            &format!(
                "unitary fn ctrl[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
                 requires Controllable(U){{qif(c,q){{0=>ident,1=>U}}}}
                 unitary fn apply2[const V:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
                 requires Applicable(V){{V(q)}}
                 unitary fn adjoint2[const V:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
                 requires Adjointable(V){{adjoint(V)(q)}}
                 unitary fn derived[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->Q<(Bit,Bit)>
                 requires Controllable(U){extra}{{{body}}}
                 observe fn main()->(Bit,Bit){{
                     let (c,q) = split(derived[phase](x(init0()),t(h(init0()))));
                     (measure_z(x(c)),measure_z(h(q)))
                 }}"
            ),
            &[false, false],
        );
    }
    for body in ["U(q)", "adjoint(U)(q)", "use_op[adjoint(U)](q)"] {
        rejects(
            &format!(
                "unitary fn direct[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
                 requires Controllable(U){{{body}}}"
            ),
            ErrorCode::Capability,
        );
    }
}

#[test]
fn meanings_reject_wrong_phase_wrong_tree_and_nonpermutations() {
    rejects(
        "unitary fn client[const U:Op<Bit,ZMeaning>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{client[flip](q)}",
        ErrorCode::Contract,
    );
    rejects(
        "unitary fn minus_z(q:Q<Bit>)->Q<Bit>{x(z(x(q)))}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[checked_op(minus_z,ZMeaning)](q)}",
        ErrorCode::Contract,
    );
    rejects(
        "classical fn constant(b:Bit)->Bit{0} meaning Bad:Bit=permutation_by(constant);",
        ErrorCode::Contract,
    );
    rejects(
        "classical fn wrong(b:Bit)->Bit{b} meaning Bad:Bit=phase_by(wrong);",
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
    let generic = "classical fn pred(b:Bit)->Bit{b}
        unitary fn clean[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){
            with_computed(q,pred,direct_z){|d,a|(d,U(a))}}
        unitary fn client(q:Q<Bit>)->Q<Bit>{clean[PROVIDER](q)}";
    check(&generic.replace("PROVIDER", "direct_z"));
    rejects(&generic.replace("PROVIDER", "flip"), ErrorCode::InvalidIr);
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){apply_contract(U,direct_z,q)}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn pending_call_frames_declared_effects_and_local_shadowing_are_preserved() {
    deterministic("unitary fn pair[const U:Op<Bit>](a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){(a,U(b))}
        observe fn main()->(Bit,Bit){let (a,b)=cnot(h(init0()),init0());
            let(a,b)=pair[ident](a,if 1 {b} else {b});(measure_z(a) xor measure_z(b),0)}", &[false,false]);
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){let U=q;U(U)}",
        ErrorCode::TypeMismatch,
    );
    rejects(
        "observe fn obs[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){let b=measure_z(init0());U(q)}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{obs[ident](q)}",
        ErrorCode::Effect,
    );
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){use_op[q](q)}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn unused_generic_declarations_and_static_dependencies_are_checked() {
    rejects(
        "unitary fn bad[const U:Op<Bit>,const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
        ErrorCode::Ownership,
    );
    rejects(
        "unitary fn bad[const U:Op<Bit>](U:Q<Bit>)->Q<Bit>{U}",
        ErrorCode::Ownership,
    );
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U),Applicable(U){q}",
        ErrorCode::Capability,
    );
    rejects(
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(missing){q}",
        ErrorCode::UnknownName,
    );
    rejects(
        "unitary fn cycle(q:Q<Bit>)->Q<Bit>{use_op[power(cycle,0)](q)}",
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
        "unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{let v=U;q}",
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn static_basis_errors_and_concrete_step_instance_limits_reject_without_panics() {
    rejects("unitary fn dual[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(U){qif(c,q){0=>U,1=>U}}
        unitary fn bad(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){dual[power(phase,513)](c,q)}", ErrorCode::Limit);
    rejects(
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[power(phase,1025)](q)}",
        ErrorCode::Limit,
    );
    let too_wide = "controlled(".repeat(6) + "phase" + &")".repeat(6);
    rejects(
        &format!("unitary fn bad(q:Q<Bit>)->Q<Bit>{{use_op[{too_wide}](q)}}"),
        // This deliberately wrong Op basis fails before a concrete width limit.
        ErrorCode::TypeMismatch,
    );
    let mut source = String::new();
    // Structurally different, valid identity descriptions remain distinct instances.
    for n in 0..257 {
        source.push_str(&format!(
            "unitary fn f{n}(q:Q<Bit>)->Q<Bit>{{use_op[power(ident,{n})](q)}}"
        ));
    }
    let root = SourceRoot::new(&format!("{PRELUDE}{source}"));
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(error.message.contains("256 distinct"), "{error}");
}

#[test]
fn lexical_runtime_binding_rejects_static_shadow_before_later_calls() {
    // Both selected sources fail at the preceding let; later call arguments
    // cannot make an illegal static-name shadow binding valid.
    for source in [
        common::current_source_text(
            "tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-missing-argument/main.qli",
        ),
        common::current_source_text(
            "tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-valid-argument/main.qli",
        ),
    ] {
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch);
        assert_eq!(error.message, "binding U shadows a static parameter/index");
        assert_eq!(&source[error.span.start..error.span.end], "U");
        assert_eq!(error.span.start, source.find("let U").unwrap() + 4);
    }
}

#[test]
fn retired_static_headers_reject_at_both_source_entry_points() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;
    for source in [
        "pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit>{q}",
        "pub fn f[const n:Nat,static U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
    ] {
        let root = SourceRoot::new(source);
        let project = check_project(&root.0).unwrap_err();
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(project.code, ErrorCode::Project);
        assert_eq!(selected.code(), "parse");
        assert!(project.message.contains(selected.message()));
        assert_eq!(project.span, selected.span());
        assert_eq!(&source[project.span.start..project.span.end], "static");
    }
}

#[test]
fn retired_operation_spellings_reject_at_both_source_entry_points() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;
    for (body, token) in [
        ("adjoint(U,q)", "adjoint"),
        ("helper[repeat_op(2,U)](q)", "repeat_op"),
        ("repeat_static(2,U,q)", "repeat_static"),
        ("inverse(U)(q)", "inverse"),
        ("helper[inverse_op(U)](q)", "inverse_op"),
        ("helper[controlled_op(U)](q)", "controlled_op"),
    ] {
        let source = format!("pub unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
        let root = SourceRoot::new(&source);
        let project = check_project(&root.0).unwrap_err();
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(project.code, ErrorCode::Project);
        assert_eq!(selected.code(), "parse");
        assert!(project.message.contains(selected.message()));
        assert_eq!(project.span, selected.span());
        assert_eq!(&source[project.span.start..project.span.end], token);
    }
}

#[test]
fn direct_literal_power_keeps_named_function_access_distinct_from_static_providers() {
    for body in ["power(z,0)(q)", "power(z,2)(q)", "power(z,0)(h(q))"] {
        check(&format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}"));
    }
    // Direct repetition does not grant primitive names a general Op provider
    // contract, even at zero count or through a constructed inverse/control.
    for body in [
        "use_op[power(z,0)](q)",
        "adjoint(power(z,0))(q)",
        "let (c,q)=controlled(power(z,0))(init0(),q);discard(c);q",
    ] {
        rejects(
            &format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}"),
            ErrorCode::TypeMismatch,
        );
    }
}

fn arrow_study(name: &str) -> String {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/arrow-interfaces-v030/attempt-01")
            .join(format!("{name}.qli")),
    )
    .unwrap()
}

#[test]
fn direct_arrows_keep_their_principal_effect_before_static_arrow_extension() {
    use qleisli::frontend::compile::ParsedProgram;
    use qleisli::ir::Effect;
    use std::collections::BTreeMap;

    for (name, effect) in [
        ("direct-unitor", Effect::Unitary),
        ("direct-preparation", Effect::Isometry),
        ("endomorphic-control", Effect::Unitary),
    ] {
        let source = arrow_study(name);
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        assert_eq!(
            parsed.function_effect("main::main").unwrap().inferred(),
            effect,
            "{name}"
        );
        // Whole-source checking and a selected specialization remain separate
        // from native acceptance and an independently requested Meaning.
        parsed
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .check_lowering_profile()
            .unwrap();
    }
}

#[test]
fn an_equal_dimension_unitor_is_not_an_endomorphic_static_provider() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;

    let source = arrow_study("endomorphic-unitor-refusal");
    let files = SourceRoot::new(&source);
    let project = check_project(&files.0).unwrap_err();
    let selected =
        ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
    assert_eq!(project.code, ErrorCode::TypeMismatch);
    assert_eq!(selected.code(), "type");
    assert_eq!(project.message, selected.message());
    assert_eq!(project.span, selected.span());
    assert_eq!(&source[project.span.start..project.span.end], "strip");
    assert!(project.message.contains("Q<Bit>"), "{project}");
    assert!(project.message.contains("Q<(Unit,Bit)>"), "{project}");
}

fn composition_study(name: &str, attempt: &str) -> String {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/meaning-composition-v030")
            .join(attempt)
            .join(format!("{name}.qli")),
    )
    .unwrap()
}

#[test]
fn composed_meanings_check_actual_providers_in_both_public_paths() {
    use qleisli::contract::exact::Budget;
    use qleisli::frontend::compile::ParsedProgram;
    use qleisli::interchange::native::Kernel;
    use std::collections::BTreeMap;
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    for (name, valid) in [
        ("compose", true),
        ("compose-wrong-order", false),
        ("tensor", true),
        ("tensor-wrong-axes", false),
    ] {
        // Finite uses the observing client; selected uses its explicit pure adapter.
        // Exact targets and implementation bodies are identical in both snapshots.
        let source = composition_study(name, "attempt-03");
        let root = SourceRoot::new(&composition_study(name, "attempt-02"));
        let finite = check_project(&root.0);
        let selected = ParsedProgram::parse(BTreeMap::from([("main".into(), source)]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        // The unchanged evidence gate must run before hierarchy emission.
        assert_eq!(selected.lower().unwrap_err().code(), "meaning");
        let checked = selected.check_operation_meanings(
            &kernel,
            &mut Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
        );
        if valid {
            finite.unwrap_or_else(|e| panic!("{name}: {e}"));
            let checked = checked.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(checked.checked_bindings() > 0);
            let proposal = checked.lower_hierarchy().unwrap();
            qleisli::interchange::hierarchical::Kernel::new(
                std::env::var_os("QLEISLI_KERNEL").unwrap(),
            )
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        } else {
            assert_eq!(finite.unwrap_err().code, ErrorCode::Contract, "{name}");
            assert_eq!(checked.unwrap_err().code(), "contract", "{name}");
        }
    }
}

#[test]
fn composed_meanings_reject_unused_wrong_trees_categories_and_cycles() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;
    for declarations in [
        "meaning Bad:(Unit,Bit)=compose(X,X);",
        "meaning Bad:(Bit,Unit)=tensor(X,U); meaning Other:(Unit,Bit)=compose(Bad,Bad);",
        "meaning Bad:(Bit,Bit)=tensor(X,f);",
        "meaning Bad:Bit=compose(X,Bad);",
        "meaning A:Bit=compose(X,B); meaning B:Bit=compose(A,X);",
    ] {
        let source = format!(
            "classical fn f(b:Bit)->Bit{{b}} classical fn u(v:Unit)->Unit{{v}}
             meaning X:Bit=permutation_by(f); meaning U:Unit=permutation_by(u);
             {declarations} unitary fn main(q:Q<Bit>)->Q<Bit>{{q}}"
        );
        let root = SourceRoot::new(&source);
        let finite = check_project(&root.0).unwrap_err();
        let selected = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap_err();
        assert_eq!(finite.message, selected.message());
        assert_ne!(selected.code(), "parse");
    }
}
