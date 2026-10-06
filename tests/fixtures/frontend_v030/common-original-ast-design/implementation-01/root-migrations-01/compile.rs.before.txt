mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use common::SourceRoot;

use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};

fn run(root: &Path) -> BTreeMap<Vec<bool>, f64> {
    let checked = compile_project(root).unwrap();
    let result = run_closed(&checked, SimulationLimits::default()).unwrap();
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    result
}

fn probability(distribution: &BTreeMap<Vec<bool>, f64>, outcome: &[bool], expected: f64) {
    let actual = distribution.get(outcome).copied().unwrap_or(0.0);
    assert!(
        (actual - expected).abs() < 1e-12,
        "{outcome:?}: {actual}, expected {expected}"
    );
}

#[test]
fn documented_projects_compile_verify_and_simulate() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let bell = run(&examples.join("bell"));
    assert_eq!(bell.len(), 2);
    probability(&bell, &[false, false], 0.5);
    probability(&bell, &[true, true], 0.5);
    let phase = run(&examples.join("phase_oracle"));
    probability(&phase, &[true], 1.0);
    let feedback = run(&examples.join("feedback"));
    assert_eq!(feedback.len(), 2);
    probability(&feedback, &[false, false], 0.5);
    probability(&feedback, &[true, false], 0.5);
}

#[test]
fn function_branch_preserves_the_callers_quantum_frame() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
unitary fn choose(b: Bit, q: Q<Bit>) -> Q<Bit> {
    if b { x(q) } else { q }
}
observe fn main() -> (Bit, Bit) {
    let spectator = h(init0());
    let b = measure_z(x(init0()));
    let q = choose(b, init0());
    (measure_z(spectator), measure_z(q))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, true], 0.5);
    probability(&result, &[true, true], 0.5);
}

#[test]
fn branch_created_wires_and_classical_results_merge() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> (Bit, Bit) {
    let b = measure_z(h(init0()));
    let (c, q) = if b {
        (measure_z(x(init0())), x(init0()))
    } else {
        (measure_z(init0()), init0())
    };
    (c, measure_z(q))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, false], 0.5);
    probability(&result, &[true, true], 0.5);
}

#[test]
fn invalid_source_is_rejected_before_execution() {
    let imports = "use std::quantum::init0; use std::quantum::h; use std::quantum::x; use std::quantum::z; use std::quantum::split; use std::observe::measure_z; use std::observe::discard;";
    let cases = [
        (
            "observe fn main() -> Unit { let q = init0(); let pair = (q, q); () }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { let q = init0(); let b = measure_z(q); h(q) }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { let q = init0(); () }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { let _ = init0(); () }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { init0(); () }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { let q = init0(); let q = init0(); () }",
            ErrorCode::Ownership,
        ),
        (
            "iso fn bad(q: Q<Bit>) -> Bit { measure_z(q) } observe fn main() -> Unit { () }",
            ErrorCode::Effect,
        ),
        (
            "unitary fn bad() -> Q<Bit> { init0() } observe fn main() -> Unit { () }",
            ErrorCode::Effect,
        ),
        (
            "observe fn main() -> Bit { let q = init0(); let q = do b <- q; pure 0; measure_z(q) }",
            ErrorCode::Ownership,
        ),
        (
            "observe fn main() -> Unit { let q = init0(); if q { () } else { () } }",
            ErrorCode::TypeMismatch,
        ),
        (
            "observe fn main() -> Unit { let b = measure_z(init0()); let q = init0(); if b { discard(q) } else { () } }",
            ErrorCode::Ownership,
        ),
        (
            "basis fn p(x: Bit) -> Bit { x } observe fn main() -> Bit { measure_z(with_computed(init0(), p) { |a| h(a) }) }",
            ErrorCode::Unsupported,
        ),
        (
            "basis fn p(x: Bit) -> Bit { x } observe fn main() -> Bit { measure_z(with_computed(init0(), p) { |a| let b = measure_z(a); init0() }) }",
            ErrorCode::Effect,
        ),
        (
            "basis fn p(x: Bit) -> Bit { x } observe fn main() -> Bit { let q = init0(); measure_z(with_computed(q, p) { |a| let q = h(q); a }) }",
            ErrorCode::Ownership,
        ),
        (
            "basis fn bad(x: Bit) -> Bit { missing } observe fn main() -> Unit { () }",
            ErrorCode::UnknownName,
        ),
        (
            "iso fn f(q: Q<Bit>) -> Q<Bit> { g(q) } iso fn g(q: Q<Bit>) -> Q<Bit> { f(q) } observe fn main() -> Unit { () }",
            ErrorCode::RecursiveCall,
        ),
        (
            "observe fn main() -> Q<Bit> { init0() }",
            ErrorCode::InvalidEntry,
        ),
        (
            "observe fn main() -> Bit { measure_z(init0(), init0()) }",
            ErrorCode::Arity,
        ),
    ];
    for (source, code) in cases {
        let root = SourceRoot::new(&format!("{imports}\n{source}"));
        let error = compile_project(&root.0).unwrap_err();
        assert_eq!(error.code, code, "{source}\n{error}");
        assert!(error.path.ends_with("main.qli"));
        assert!(error.line > 0 && error.column > 0);
    }
}

#[test]
fn missing_import_reports_the_call_site_even_in_unused_functions() {
    let source = "// 日本語\nobserve fn hidden() -> Bit { measure_z(init0()) }\nobserve fn main() -> Unit { () }";
    let root = SourceRoot::new(source);
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::UnknownName);
    assert_eq!(error.span.start, source.find("measure_z").unwrap());
    assert_eq!(error.line, 2);
}

#[test]
fn quantum_rebinding_inside_a_branch_cannot_escape_its_scope() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::observe::measure_z;
observe fn main() -> Bit {
    let b = measure_z(init0());
    let q = init0();
    if b { let q = h(q); () } else { () };
    measure_z(q)
}
"#,
    );
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        ErrorCode::Ownership
    );
}

#[test]
fn bundled_basis_functions_control_a_product_register() {
    let root = SourceRoot::new(
        r#"
use std::basis::and2;
use std::basis::xor2;
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::z;
use std::quantum::join;
use std::quantum::split;
use std::observe::measure_z;
basis fn predicate((a,b): (Bit,Bit)) -> Bit { xor2(and2(a, b), 0) }
observe fn main() -> (Bit, Bit) {
    let q = join(h(init0()), x(init0()));
    let q = with_computed(q, predicate) { |a| z(a) };
    let (a, b) = split(q);
    (measure_z(h(a)), measure_z(b))
}
"#,
    );
    probability(&run(&root.0), &[true, true], 1.0);
}

#[test]
fn nested_toffoli_result_reset_and_discard_lower_to_observation() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::x;
use std::quantum::toffoli;
use std::observe::reset;
use std::observe::discard;
use std::observe::measure_z;
observe fn main() -> (Bit, Bit) {
    let ((a, b), q) = toffoli(x(init0()), x(init0()), init0());
    let a = reset(a);
    discard(b);
    (measure_z(a), measure_z(q))
}
"#,
    );
    probability(&run(&root.0), &[false, true], 1.0);
}

#[test]
fn conditional_swap_pairs_different_input_registers() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> (Bit, Bit) {
    let c = measure_z(h(init0()));
    let a = init0();
    let b = x(init0());
    let (a, b) = if c { (a, b) } else { (b, a) };
    (measure_z(a), measure_z(b))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, true], 0.5);
    probability(&result, &[true, false], 0.5);
}

#[test]
fn library_check_needs_no_entry_and_project_errors_have_coordinates() {
    let root = SourceRoot::new("pub unitary fn id(q: Q<Bit>) -> Q<Bit> { q }");
    check_project(&root.0).unwrap();
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        ErrorCode::InvalidEntry
    );
    let source = "// λ\r\nobserve fn main() -> Unit {\r\n @\r\n}";
    fs::write(root.0.join("main.qli"), source).unwrap();
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Project);
    assert_eq!((error.line, error.column), (3, 2));
    assert_eq!(error.span.start, source.find('@').unwrap());
}

#[test]
fn exponential_call_expansion_has_a_checked_work_limit() {
    let mut source = "unitary fn f0(q: Q<Bit>) -> Q<Bit> { q }\n".to_owned();
    for index in 1..20 {
        let previous = index - 1;
        source.push_str(&format!(
            "unitary fn f{index}(q: Q<Bit>) -> Q<Bit> {{ f{previous}(f{previous}(q)) }}\n"
        ));
    }
    let root = SourceRoot::new(&source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(error.message.contains("work limit"), "{error}");
}

#[test]
fn growing_values_and_zero_bit_types_return_limits_on_a_normal_thread_stack() {
    let cases = [
        format!(
            "observe fn main() -> Unit {{ let v = (); {} () }}",
            "let v = (v, v);".repeat(21)
        ),
        format!(
            "observe fn main() -> Unit {{ let v = (); {} () }}",
            "let v = ((), v);".repeat(8192)
        ),
        format!(
            "use std::observe::discard; observe fn f(q: Q<Unit>) -> Unit {{ {} discard(q) }}",
            "let q = do x <- q; pure (x, x);".repeat(18)
        ),
        format!(
            "use std::observe::discard; observe fn f(q: Q<Unit>) -> Unit {{ {} discard(q) }}",
            "let q = do x <- q; pure ((), x);".repeat(8192)
        ),
    ];
    // Stack overflow aborts the process rather than unwinding. Use the same
    // 2 MiB stack as the review reproducer, including destruction of the input.
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            for source in cases {
                let root = SourceRoot::new(&source);
                let error = check_project(&root.0).unwrap_err();
                assert_eq!(error.code, ErrorCode::Limit, "{error}");
                assert!(error.message.contains("internal value or type"), "{error}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn annotated_types_and_computed_domains_share_the_tree_limits() {
    let mut ty = "Unit".to_owned();
    for _ in 0..12 {
        ty = format!("({ty}, {ty})");
    }
    for source in [
        format!("unitary fn f(v: {ty}) -> Unit {{ () }}"),
        format!(
            "basis fn p(value: {ty}) -> Bit {{ 0 }} unitary fn f(q: Q<Unit>) -> Q<Unit> {{ with_computed(q, p) {{ |a| a }} }}"
        ),
    ] {
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit, "{error}");
        assert!(error.message.contains("internal value or type"), "{error}");
    }
}

#[test]
fn bounded_classical_copies_and_unit_lifts_remain_valid() {
    let source = format!(
        "use std::observe::discard;
         observe fn f(q: Q<Unit>) -> Unit {{ {} discard(q) }}
         observe fn main() -> Unit {{ let v = (); {} {} () }}",
        "let q = do x <- q; pure (x, x);".repeat(10),
        "let v = (v, v);".repeat(10),
        "let v = ((), v);".repeat(40),
    );
    let root = SourceRoot::new(&source);
    let result = run(&root.0);
    assert_eq!(result, BTreeMap::from([(vec![], 1.0)]));
}

#[test]
fn repeated_tree_copies_and_branch_frames_spend_the_work_budget() {
    let classical_prefix = format!(
        "observe fn f(b: Bit) -> Unit {{ let v = (); {}",
        "let v = (v, v);".repeat(9),
    );
    let cases = [
        format!("{classical_prefix} {} () }}", "let _ = v;".repeat(1000)),
        format!(
            "{classical_prefix} {} () }}",
            "if b { () } else { () };".repeat(200)
        ),
        // The large register is in the caller's frame, outside noop's Env.
        format!(
            "use std::observe::discard;
             unitary fn noop(b: Bit) -> Unit {{ if b {{ () }} else {{ () }} }}
             observe fn f(b: Bit, q: Q<Unit>) -> Unit {{ {} {} discard(q) }}",
            "let q = do x <- q; pure (x, x);".repeat(9),
            "noop(b);".repeat(600),
        ),
    ];
    for source in cases {
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit, "{error}");
        assert!(error.message.contains("work limit"), "{error}");
    }
}

#[test]
fn imported_argument_errors_point_to_the_call_and_actual_argument() {
    for (call, code, offset, width) in [
        ("id(())", ErrorCode::TypeMismatch, 3, 2),
        ("id()", ErrorCode::Arity, 0, 4),
        ("id((), ())", ErrorCode::Arity, 0, 10),
    ] {
        let source = format!(
            "use helper::id;\r\nuse std::quantum::init0;\r\nuse std::observe::discard;\r\n// 日本語\r\nobserve fn main() -> Unit {{\r\n    discard(id(init0()));\r\n    discard({call})\r\n}}"
        );
        let root = SourceRoot::new(&source);
        fs::write(
            root.0.join("helper.qli"),
            "pub unitary fn id(q: Q<Bit>) -> Q<Bit> { q }",
        )
        .unwrap();
        let error = compile_project(&root.0).unwrap_err();
        assert_eq!(error.code, code, "{error}");
        assert_eq!(
            error.path,
            fs::canonicalize(root.0.join("main.qli")).unwrap()
        );
        assert_eq!(error.span.start, source.rfind(call).unwrap() + offset);
        assert_eq!(error.span.end, error.span.start + width);
        assert_eq!((error.line, error.column), (7, 13 + offset));
    }
}

#[test]
fn invalid_callee_body_still_reports_its_own_source() {
    let root = SourceRoot::new("use helper::bad; observe fn main() -> Unit { bad() }");
    let helper = "pub unitary fn bad() -> Bit { () }";
    fs::write(root.0.join("helper.qli"), helper).unwrap();
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
    assert_eq!(
        error.path,
        fs::canonicalize(root.0.join("helper.qli")).unwrap()
    );
    assert_eq!(error.span.start, helper.rfind("()").unwrap());
}

// Finite v0 conformance boundaries.
#[test]
fn finite_v0_type_shapes_and_zero_wire_ownership() {
    for source in [
        "unitary fn id(q: Q<Unit>) -> Q<Unit> { q }",
        "unitary fn id(b: Bit) -> Bit { b }",
        "use std::quantum::split; use std::quantum::join;
         unitary fn regroup(q: Q<(Unit,Bit)>) -> Q<(Unit,Bit)> {
             let (u, b) = split(q); join(u, b)
         }",
    ] {
        check_project(&SourceRoot::new(source).0).unwrap();
    }
    for (source, code) in [
        (
            "unitary fn bad(q: Q<Unit>) -> Unit { () }",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn bad(q: Q<Unit>) -> (Q<Unit>,Q<Unit>) { (q,q) }",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn bad(q: Q<(Unit,Bit)>) -> Q<Bit> { q }",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn bad(q: Q<((Bit,Bit),Bit)>) -> Q<(Bit,(Bit,Bit))> { q }",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn bad(b: Bit) -> Q<Bit> { b }",
            ErrorCode::TypeMismatch,
        ),
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, code, "{source}\n{error}");
    }
}

#[test]
fn finite_v0_effects_classify_quantum_maps_and_respect_declarations() {
    // Classical erasure is allowed; Unitary describes the quantum map for each
    // fixed classical input, not a bijection of the classical inputs/outputs.
    check_project(
        &SourceRoot::new(
            "unitary fn forget(b: Bit) -> Unit { () }
             unitary fn id(q: Q<Bit>) -> Q<Bit> { q }
             unitary fn caller(b: Bit, q: Q<Bit>) -> Q<Bit> { forget(b); id(q) }",
        )
        .0,
    )
    .unwrap();
    for (callee_kind, caller_kind) in [("iso", "unitary"), ("observe", "iso")] {
        let source = format!(
            "{callee_kind} fn id(q: Q<Bit>) -> Q<Bit> {{ q }}
             {caller_kind} fn caller(q: Q<Bit>) -> Q<Bit> {{ id(q) }}"
        );
        // A broader assertion on an identity cannot inflate its principal
        // body effect or force a narrower caller to reject.
        check_project(&SourceRoot::new(&source).0).unwrap();
    }
    for source in [
        "use std::quantum::init0; iso fn prepare()->Q<Bit>{init0()}
         unitary fn caller()->Q<Bit>{prepare()}",
        "use std::observe::measure_z; observe fn measure(q:Q<Bit>)->Bit{measure_z(q)}
         iso fn caller(q:Q<Bit>)->Bit{measure(q)}",
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Effect, "{error}");
    }
}

#[test]
fn finite_v0_mixed_values_move_as_a_whole() {
    check_project(
        &SourceRoot::new(
            "unitary fn copy_classical(v: (Bit,Q<Bit>)) -> ((Bit,Bit),Q<Bit>) {
                 let (b,q) = v; ((b,b),q)
             }",
        )
        .0,
    )
    .unwrap();
    let root = SourceRoot::new(
        "unitary fn bad(v: (Bit,Q<Bit>)) -> ((Bit,Q<Bit>),(Bit,Q<Bit>)) {
             let moved = v; (moved,v)
         }",
    );
    assert_eq!(
        check_project(&root.0).unwrap_err().code,
        ErrorCode::Ownership
    );
}

#[test]
fn finite_v0_basis_lifts_are_injective_and_closed() {
    check_project(
        &SourceRoot::new(
            "iso fn prepare(q: Q<Unit>) -> Q<Bit> { do x <- q; pure 0 }
             unitary fn swap_label(q: Q<Bit>) -> Q<Bit> { do x <- q; pure not x }",
        )
        .0,
    )
    .unwrap();
    for (source, code) in [
        (
            "unitary fn bad(q: Q<Bit>) -> Q<Bit> { do x <- q; pure 0 }",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn bad(b: Bit, q: Q<Bit>) -> Q<Bit> { do x <- q; pure b }",
            ErrorCode::UnknownName,
        ),
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, code, "{source}\n{error}");
    }
}

#[test]
fn finite_v0_computed_blocks_require_the_structural_certificate() {
    let prefix = "use std::quantum::h; use std::quantum::z; use std::quantum::t;
                  basis fn p(x: Bit) -> Bit { x }
                  unitary fn phase(a: Q<Bit>) -> Q<Bit> { t(z(a)) }";
    for body in ["a", "phase(a)"] {
        let source = format!(
            "{prefix} unitary fn oracle(q: Q<Bit>) -> Q<Bit> {{
                 with_computed(q,p) {{ |a| {body} }}
             }}"
        );
        check_project(&SourceRoot::new(&source).0).unwrap();
    }
    // H H and Z^2 are identities, but v0 certificates are structural. A static
    // transform emits ApplyUnitary, which this source certificate excludes.
    for body in ["h(h(a))", "adjoint(t,a)", "repeat_static(2,z,a)"] {
        let source = format!(
            "{prefix} unitary fn oracle(q: Q<Bit>) -> Q<Bit> {{
                 with_computed(q,p) {{ |a| {body} }}
             }}"
        );
        let error = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Unsupported, "{body}\n{error}");
    }
}

#[test]
fn finite_v0_local_names_shadow_static_callees() {
    for source in [
        "basis fn f(x: Bit) -> Bit { x }
         basis fn bad(f: Bit) -> Bit { f(f) }",
        "use std::quantum::h;
         unitary fn bad(h: Q<Bit>) -> Q<Bit> { let q = h; adjoint(h,q) }",
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{source}\n{error}");
    }
}

// SPEC-3 resource calculus boundaries (R1).
#[test]
fn resource_rules_pending_mixed_argument_survives_nested_call() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::cnot;
use std::observe::measure_z;
unitary fn choose(b: Bit, q: Q<Bit>) -> Q<Bit> {
    if b { if b { h(h(q)) } else { x(x(q)) } } else { q }
}
unitary fn pack(v: (Bit,Q<Bit>), q: Q<Bit>) -> ((Bit,Q<Bit>),Q<Bit>) {
    (v,q)
}
observe fn main() -> ((Bit,Bit),(Bit,Bit)) {
    let (a,r) = cnot(h(init0()),init0());
    let b = measure_z(h(init0()));
    let ((saved,a),r) = pack((b,a),choose(b,r));
    let (a,r) = cnot(a,r);
    ((saved,b),(measure_z(h(a)),measure_z(r)))
}
"#,
    );
    let result = run(&root.0);
    // The first actual argument has moved out of the caller environment when
    // the second argument enters choose. Its quantum leaf is still entangled.
    probability(&result, &[false, false, false, false], 0.5);
    probability(&result, &[true, true, false, false], 0.5);
}

#[test]
fn resource_rules_pending_tuple_field_survives_branch() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;
observe fn main() -> (Bit,(Bit,Bit)) {
    let (a,r) = cnot(h(init0()),init0());
    let b = measure_z(h(init0()));
    let (a,r) = (a,if b { h(h(r)) } else { r });
    let (a,r) = cnot(a,r);
    (b,(measure_z(h(a)),measure_z(r)))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, false, false], 0.5);
    probability(&result, &[true, false, false], 0.5);
}

#[test]
fn resource_rules_mixed_branch_results_follow_positions() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> ((Bit,Bit),(Bit,Bit)) {
    let b = measure_z(h(init0()));
    let a = init0();
    let r = x(init0());
    let (left,right) = if b { ((b,a),(b,r)) } else { ((b,r),(b,a)) };
    let (c,a) = left;
    let (d,r) = right;
    ((c,d),(measure_z(a),measure_z(r)))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, false, true, false], 0.5);
    probability(&result, &[true, true, false, true], 0.5);
}

#[test]
fn resource_rules_zero_width_result_and_frame_are_both_merged() {
    use qleisli::ir::RawOp;

    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::split;
use std::observe::measure_z;
use std::observe::discard;
unitary fn choose(b: Bit, u: Q<Unit>) -> Q<Unit> {
    if b { u } else { u }
}
observe fn main() -> (Bit,Bit) {
    let pair = do b <- init0(); pure ((),b);
    let (u,q) = split(pair);
    let b = measure_z(h(init0()));
    let u = choose(b,u);
    discard(u);
    (b,measure_z(q))
}
"#,
    );
    let checked = compile_project(&root.0).unwrap();
    let branches: Vec<_> = checked
        .program()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ClassicalBranch { quantum_phis, .. } => Some(quantum_phis),
            _ => None,
        })
        .collect();
    assert_eq!(branches.len(), 1);
    let mut widths: Vec<_> = branches[0]
        .iter()
        .map(|phi| phi.output_wires.len())
        .collect();
    widths.sort();
    // A wire-only comparison would omit the Unit result. The other phi is
    // the caller's q, which is not accessible inside choose's environment.
    assert_eq!(widths, [0, 1]);
    let result = run_closed(&checked, SimulationLimits::default()).unwrap();
    probability(&result, &[false, false], 0.5);
    probability(&result, &[true, false], 0.5);
}

#[test]
fn resource_rules_reset_branch_keeps_reference_and_classical_history() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;
use std::observe::reset;
observe fn main() -> (Bit,(Bit,Bit)) {
    let (a,r) = cnot(h(init0()),init0());
    let b = measure_z(h(init0()));
    let r = if b { reset(r) } else { r };
    (b,(measure_z(a),measure_z(r)))
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, false, false], 0.25);
    probability(&result, &[false, true, true], 0.25);
    probability(&result, &[true, false, false], 0.25);
    probability(&result, &[true, true, false], 0.25);
}

#[test]
fn resource_rules_nested_classical_results_keep_their_scopes() {
    let root = SourceRoot::new(
        r#"
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::observe::measure_z;
observe fn main() -> (Bit,Bit) {
    let b = measure_z(h(init0()));
    let c = if b {
        if b { measure_z(x(init0())) } else { measure_z(init0()) }
    } else {
        if b { measure_z(x(init0())) } else { measure_z(init0()) }
    };
    (b,c)
}
"#,
    );
    let result = run(&root.0);
    probability(&result, &[false, false], 0.5);
    probability(&result, &[true, true], 0.5);
}

#[test]
fn resource_rules_reject_lost_or_differently_consumed_bindings() {
    for source in [
        // Same wire width does not make different outer consumption sets equal.
        "unitary fn bad(c:Bit,a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){
             let r=if c {a} else {b}; (r,a)
         }",
        // Rebinding the same spelling and slot still creates local ownership.
        "use std::quantum::h;
         unitary fn bad(c:Bit,q:Q<Bit>)->Q<Bit>{
             if c { let q=h(q); () } else { () }; q
         }",
        "unitary fn bad(c:Bit,u:Q<Unit>)->Unit{
             let _=if c {u} else {u}; ()
         }",
        "unitary fn bad(v:(Bit,Q<Unit>))->Bit{let (b,_)=v; b}",
        "unitary fn bad(v:(Bit,Q<Bit>))->((Bit,Q<Bit>),(Bit,Q<Bit>)){
             let moved=v; (moved,v)
         }",
        // A callee must account for every quantum parameter independently.
        "unitary fn bad(a:Q<Bit>,b:Q<Bit>)->Q<Bit>{a}",
    ] {
        let error = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Ownership, "{source}\n{error}");
    }
}
