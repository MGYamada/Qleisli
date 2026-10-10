//! Source arrow contracts and small complex observations, not general soundness.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, OperationBinding, ParsedProgram, check_project};
use qleisli::ir::Effect;
use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

fn selected(source: &str, action: &str, basis: usize) -> String {
    let root = SourceRoot::new(source);
    let kernel = std::env::var_os("QLEISLI_KERNEL").expect("select native Lean checker");
    let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["--format=json", action, "--entry=main::main"])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .arg(format!("--lean-kernel={}", Path::new(&kernel).display()))
        .args(if action == "run" {
            vec![format!("--basis={basis}")]
        } else {
            vec![]
        })
        .output()
        .unwrap();
    assert!(result.status.success(), "{result:?}");
    assert!(result.stderr.is_empty(), "{result:?}");
    let text = String::from_utf8(result.stdout).unwrap();
    assert!(text.contains("\"source_meaning_verified\":false"), "{text}");
    assert!(
        text.contains("\"execution_authority\":\"checked-produced-ir\""),
        "{text}"
    );
    text
}

fn amplitudes(text: &str, expected: &[[f64; 2]]) {
    let rows = text
        .split_once("\"amplitudes\":[")
        .unwrap()
        .1
        .split_once("]]")
        .unwrap()
        .0;
    let actual: Vec<f64> = rows
        .split(['[', ']', ','])
        .filter_map(|s| {
            let s = s.trim();
            (!s.is_empty()).then(|| s.parse().unwrap())
        })
        .collect();
    assert_eq!(actual.len(), expected.len() * 2, "{text}");
    for (actual, expected) in actual.iter().zip(expected.iter().flatten()) {
        assert!((actual - expected).abs() < 1e-12, "{text}");
    }
}

#[test]
fn retained_first_sources_reach_native_checking_and_complex_execution() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/general-arrows-v030/attempt-02");
    let preparation = std::fs::read_to_string(directory.join("preparation.qli")).unwrap();
    assert_eq!(
        parsed(&preparation)
            .function_effect("main::main")
            .unwrap()
            .inferred(),
        Effect::Isometry
    );
    selected(&preparation, "check", 0);
    amplitudes(
        &selected(&preparation, "run", 0),
        &[[std::f64::consts::FRAC_1_SQRT_2, 0.0]; 2],
    );
    let unitor = std::fs::read_to_string(directory.join("unitor.qli")).unwrap();
    for basis in 0..=1 {
        let mut expected = [[0.0; 2]; 2];
        expected[basis] = [1.0, 0.0];
        amplitudes(&selected(&unitor, "run", basis), &expected);
    }
    // A valid common judgment must not silently erase the codomain in the
    // finite adapter, whose general-arrow lowering remains unsupported.
    let finite = check_project(&SourceRoot::new(&preparation).0).unwrap_err();
    assert_eq!(finite.code, ErrorCode::Unsupported);
}

#[test]
fn ordered_basis_formals_keep_codomain_and_scalar_phase() {
    let source = "use std::quantum::{finish,split,phase};
        fn strip(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,b)=split(q);finish(u);phase[1,3](b)}
        fn invoke[const A:Basis,const B:Basis,const U:Op<A -> B>](q:Q<A>)->Q<B>
            requires Applicable(U){U(q)}
        pub fn main(q:Q<(Unit,Bit)>)->Q<Bit>{invoke[type((Unit,Bit)),type(Bit),strip](q)}";
    let omega = std::f64::consts::FRAC_1_SQRT_2;
    amplitudes(&selected(source, "run", 0), &[[1.0, 0.0], [0.0, 0.0]]);
    amplitudes(&selected(source, "run", 1), &[[0.0, 0.0], [omega, omega]]);
    // The codomain cannot use a later kind binder even in an unused function.
    let wrong = "fn bad[const A:Basis,const U:Op<A -> B>,const B:Basis](q:Q<A>)->Q<A>{q}";
    assert!(ParsedProgram::parse(BTreeMap::from([("main".into(), wrong.into())])).is_err());
}

#[test]
fn entry_provider_bindings_check_both_ports_and_actual_effect() {
    let source = "use std::quantum::{finish,init0};
        pub fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);init0()}
        pub fn wrong(q:Q<Bit>)->Q<Bit>{q}
        pub fn main[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)}";
    let program = parsed(source);
    for (provider, success) in [("main::prepare", true), ("main::wrong", false)] {
        let instance = program.instantiate(
            "main::main",
            BTreeMap::new(),
            BTreeMap::from([("U".into(), OperationBinding::new(provider, BTreeMap::new()))]),
        );
        assert_eq!(instance.is_ok(), success);
        if let Ok(instance) = instance {
            instance.elaborate().unwrap().lower().unwrap();
        }
    }
}

#[test]
fn explicit_endomorphism_keeps_abbreviation_effect_and_provider_rules() {
    for kind in ["Op<Bit>", "Op<Bit -> Bit>"] {
        let source = format!(
            "use std::quantum::h; fn had(q:Q<Bit>)->Q<Bit>{{h(q)}}
             unitary fn invoke[const U:{kind}](q:Q<Bit>)->Q<Bit>
                requires Applicable(U){{U(q)}}
             pub fn main(q:Q<Bit>)->Q<Bit>{{invoke[had](q)}}"
        );
        let program = parsed(&source);
        assert_eq!(
            program.function_effect("main::invoke").unwrap().inferred(),
            Effect::Unitary
        );
        selected(&source, "check", 0);
    }
}

#[test]
fn whole_source_checking_refuses_arrow_counterexamples_before_profile_selection() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/general-arrows-v030/attempt-02");
    for (name, code) in [
        ("false-unitary", "effect"),
        ("wrong-input", "type"),
        ("zero-power", "type"),
        ("controlled", "type"),
    ] {
        let source = std::fs::read_to_string(directory.join(format!("{name}.qli"))).unwrap();
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(error.code(), code, "{name}: {error}");
        let finite = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(
            finite.code,
            if code == "effect" {
                ErrorCode::Effect
            } else {
                ErrorCode::TypeMismatch
            },
            "{name}: {finite}"
        );
    }
    for (source, code) in [
        (
            "use std::quantum::{init0,finish}; use std::observe::measure_z; fn bad(q:Q<Unit>)->Q<Bit>{finish(q); let b=init0(); let c=measure_z(b);init0()} fn invoke[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)} fn call(q:Q<Unit>)->Q<Bit>{invoke[bad](q)}",
            "effect",
        ),
        (
            "meaning M:Bit=phase_by(phi); classical fn phi(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))} fn bad[const U:Op<Unit -> Bit,M>](q:Q<Unit>)->Q<Unit>{q}",
            "type",
        ),
        (
            "fn bad[const U:Op<(Unit,Bit) -> Bit>](q:Q<(Unit,Bit)>)->Q<Bit> requires Applicable(U){U(q)} fn id(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{q} fn client(q:Q<(Unit,Bit)>)->Q<Bit>{bad[id](q)}",
            "type",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), code, "{error}");
    }
}

#[test]
fn retained_constructor_sources_preserve_ports_phase_and_ordered_axes() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/general-arrow-constructors-v030/attempt-01");
    let source = |name: &str| {
        std::fs::read_to_string(directory.join(format!("{name}.qli")))
            .unwrap()
            .replace("pub fn entry", "pub fn main")
    };
    let omega = std::f64::consts::FRAC_1_SQRT_2;
    amplitudes(&selected(&source("sequence"), "run", 0), &[[omega, 0.0]; 2]);
    for name in ["adjoint", "endomorphic-sequence"] {
        for basis in 0..=1 {
            let mut expected = [[0.0; 2]; 2];
            expected[basis] = [1.0, 0.0];
            amplitudes(&selected(&source(name), "run", basis), &expected);
        }
    }
    for basis in 0..=1 {
        // Axis zero belongs to the left factor. The retained right input is
        // therefore output bit one; this also detects a reversed tensor.
        let mut expected = [[0.0; 2]; 4];
        expected[basis * 2] = [1.0, 0.0];
        amplitudes(&selected(&source("tensor"), "run", basis), &expected);
    }
    assert_eq!(
        ParsedProgram::parse(BTreeMap::from([("main".into(), source("wrong-middle"))]))
            .unwrap_err()
            .code(),
        "type"
    );
}

#[test]
fn constructed_endomorphisms_repeat_and_preserve_complex_phase() {
    let source = "use std::quantum::{finish,split,phase};
        fn unitor(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,b)=split(q);finish(u);b}
        fn twist(q:Q<Bit>)->Q<Bit>{phase[1,3](q)}
        fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub fn main(q:Q<Bit>)->Q<Bit>{invoke[power(then_op(then_op(adjoint(unitor),unitor),twist),2)](q)}";
    amplitudes(&selected(source, "run", 0), &[[1.0, 0.0], [0.0, 0.0]]);
    amplitudes(&selected(source, "run", 1), &[[0.0, 0.0], [0.0, 1.0]]);
}

#[test]
fn selected_pure_tensor_control_and_conjugation_keep_exact_ordering() {
    let prefix = "use std::quantum::{h,phase};
        fn twist(q:Q<Bit>)->Q<Bit>{phase[1,3](q)}
        fn had(q:Q<Bit>)->Q<Bit>{h(q)}";
    let omega = std::f64::consts::FRAC_1_SQRT_2;
    for (operation, basis, expected) in [
        (
            "tensor_op(twist,had)",
            1,
            vec![[0.0, 0.0], [0.5, 0.5], [0.0, 0.0], [0.5, 0.5]],
        ),
        (
            "controlled(twist)",
            3,
            vec![[0.0, 0.0], [0.0, 0.0], [0.0, 0.0], [omega, omega]],
        ),
    ] {
        let source = format!("{prefix} fn invoke[const U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> requires Applicable(U){{U(q)}}
            pub fn main(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{invoke[{operation}](q)}}");
        amplitudes(&selected(&source, "run", basis), &expected);
    }
    let source = format!(
        "{prefix} fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
        pub fn main(q:Q<Bit>)->Q<Bit>{{invoke[conjugate_op(twist,had)](q)}}"
    );
    amplitudes(&selected(&source, "run", 0), &[[omega, 0.0], [0.5, 0.5]]);
    let source = "use std::quantum::{split,join,finish,phase};
        fn strip(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,b)=split(q);finish(u);b}
        fn middle(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let(u,b)=split(q);join(u,phase[1,3](b))}
        fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub fn main(q:Q<Bit>)->Q<Bit>{invoke[conjugate_op(strip,middle)](q)}";
    amplitudes(&selected(source, "run", 1), &[[0.0, 0.0], [omega, omega]]);
}

#[test]
fn shared_constructor_subtrees_remain_bounded_before_expanded_key_allocation() {
    let source = |depth: usize| {
        let mut source = String::from(
            "use std::quantum::h; fn had(q:Q<Bit>)->Q<Bit>{h(q)}
            fn f0[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}",
        );
        for n in 1..=depth {
            source.push_str(&format!("fn f{n}[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{f{}[then_op(U,U)](q)}}",n-1));
        }
        source.push_str(&format!(
            "pub fn main(q:Q<Bit>)->Q<Bit>{{f{depth}[had](q)}}"
        ));
        source
    };
    amplitudes(&selected(&source(4), "run", 1), &[[0.0, 0.0], [1.0, 0.0]]);
    let mut repeated_leaf = String::from("had");
    for _ in 0..24 {
        repeated_leaf = format!("power({repeated_leaf},0)");
    }
    // Repeated old-profile leaves still occupy key cells when duplicated by
    // a constructor, even though their runtime power is zero.
    for source in [
        source(18),
        source(10).replace("f10[had]", &format!("f10[{repeated_leaf}]")),
    ] {
        let instance = parsed(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap();
        let error = instance.elaborate().unwrap_err();
        assert_eq!(error.code(), "limit");
    }
}

#[test]
fn raw_constructors_check_refined_children_even_under_zero_repetition() {
    let source = "fn id(q:Q<Bit>)->Q<Bit>{q}
        fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub fn main(q:Q<Bit>)->Q<Bit>{invoke[then_op(id,id)](q)}";
    let elaborate = |source: &str| {
        parsed(source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
    };
    let plain = elaborate(source);
    let kernel =
        qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let raw = plain.lower_raw().unwrap();
    let accepted = kernel.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    let source = format!(
        "classical fn phi(b:Bit)->(Bit,(Bit,Bit)){{(0,(0,b))}}
        meaning M:Bit=phase_by(phi); {}",
        source.replace("then_op(id,id)", "power(then_op(checked_op(id,M),id),0)")
    );
    let refined = elaborate(&source);
    assert_eq!(refined.lower().unwrap_err().code(), "meaning");
    let kernel =
        qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let mut budget = qleisli::contract::exact::Budget::new(20_000);
    // Preserve the original false phase claim as a negative even though the
    // enclosing zero power produces the identity. No child claim is skipped.
    let error = refined
        .check_operation_meanings(&kernel, &mut budget)
        .unwrap_err();
    assert_eq!(error.code(), "contract");
    assert!(error.message().contains("original Meaning"));
    let identity = elaborate(&source.replace("(0,(0,b))", "(0,(0,0))"));
    let checked = identity
        .check_operation_meanings(&kernel, &mut qleisli::contract::exact::Budget::new(20_000))
        .unwrap();
    // The original call argument and the callee's retained U binding each
    // carry this child annotation and must both be checked.
    assert_eq!(checked.checked_bindings(), 2);
    checked.lower_hierarchy().unwrap();
    let raw = checked
        .lower_raw(&kernel, &mut qleisli::contract::exact::Budget::new(100_000))
        .unwrap();
    let accepted = kernel.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
}

#[test]
fn refined_raw_intervals_preserve_phase_and_axes_with_a_suspended_owner() {
    let source = "use std::quantum::{x,phase,split,join};
        classical fn flip(b:Bit)->Bit{not b}
        meaning X:Bit=permutation_by(flip);
        fn direct(q:Q<Bit>)->Q<Bit>{x(q)}
        fn apply[const U:Op<Bit,X>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub fn main(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let(a,b)=split(q);let a=apply[checked_op(direct,X)](a);let b=phase[1,3](b);join(a,b)}";
    let source = parsed(source)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel =
        qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    assert_eq!(source.lower_raw().unwrap_err().code(), "meaning");
    let mut budget = qleisli::contract::exact::Budget::new(100_000);
    let checked = source
        .check_operation_meanings(&kernel, &mut budget)
        .unwrap();
    let raw = checked.lower_raw(&kernel, &mut budget).unwrap();
    let accepted = kernel.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    assert!(budget.remaining() < 100_000);
    // Independent joint action: X on the low axis and omega on high-axis 1.
    // The expected coefficients are not read from the producer or its request.
    use qleisli::contract::BasisType;
    use qleisli::contract::exact::{Exact, Matrix};
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
    let boundary = UnitaryBoundary::new(
        BasisType::Pair(Box::new(BasisType::Bit), Box::new(BasisType::Bit)),
        accepted.raw().quantum_inputs[0].clone(),
        accepted.output_ports()[0].clone(),
    )
    .unwrap();
    let mut entries = vec![Exact::zero(); 16];
    for column in 0..4 {
        entries[(column ^ 1) * 4 + column] = if column & 2 == 0 {
            Exact::one()
        } else {
            Exact::phase(1)
        };
    }
    check_unitary(
        raw.payload(),
        &boundary,
        &Matrix::new(4, 4, entries).unwrap(),
        &mut qleisli::contract::exact::Budget::new(100_000),
    )
    .unwrap();
    assert_eq!(
        checked
            .lower_raw(&kernel, &mut qleisli::contract::exact::Budget::new(0))
            .unwrap_err()
            .code(),
        "limit"
    );
}

#[test]
fn runtime_transforms_check_the_complete_endomorphic_interface_even_when_unused() {
    let source = include_str!(
        "fixtures/authoring_sessions/general-arrow-constructors-v030/attempt-02/runtime-adjoint.qli"
    );
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), "type", "{error}");
    assert_eq!(
        check_project(&SourceRoot::new(source).0).unwrap_err().code,
        ErrorCode::TypeMismatch
    );
}

#[test]
fn constructors_preserve_the_existing_nested_repetition_product_bound() {
    for source in [
        include_str!(
            "fixtures/authoring_sessions/general-arrow-constructors-v030/attempt-02/repeat-then.qli"
        ),
        include_str!(
            "fixtures/authoring_sessions/general-arrow-constructors-v030/attempt-02/repeat-adjoint.qli"
        ),
    ] {
        let source = source.replace("pub fn entry", "pub fn main");
        let instance = parsed(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap();
        let error = instance.elaborate().unwrap_err();
        assert_eq!(error.code(), "limit", "{error}");
        // Exactly 256 repetitions on every path remains supported.
        selected(
            &source.replace("power(had,256)", "power(had,128)"),
            "check",
            0,
        );
    }
    for (basis, constructor) in [
        ("(Bit,Bit)", "tensor_op(power(had,256),id)"),
        ("(Bit,Bit)", "controlled(power(had,256))"),
        ("Bit", "conjugate_op(power(had,256),id)"),
    ] {
        let source = format!(
            "use std::quantum::h; fn had(q:Q<Bit>)->Q<Bit>{{h(q)}}
             fn id(q:Q<Bit>)->Q<Bit>{{q}}
             fn invoke[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}>
                requires Applicable(U){{U(q)}}
             pub fn main(q:Q<{basis}>)->Q<{basis}>{{invoke[power({constructor},2)](q)}}"
        );
        let instance = parsed(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap();
        assert_eq!(instance.elaborate().unwrap_err().code(), "limit");
        selected(
            &source.replace("power(had,256)", "power(had,128)"),
            "check",
            0,
        );
    }
}

#[test]
fn whole_constructor_meanings_preserve_phase_axes_and_reject_false_descendants() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/general-arrow-raw-constructors-v030");
    let read = |attempt: &str, name: &str| {
        std::fs::read_to_string(directory.join(attempt).join(format!("{name}.qli"))).unwrap()
    };
    let omega = std::f64::consts::FRAC_1_SQRT_2;
    amplitudes(
        &selected(&read("attempt-01", "sequence"), "run", 1),
        &[[0.0, 0.0], [1.0, 0.0]],
    );
    amplitudes(
        &selected(&read("attempt-01", "adjoint"), "run", 1),
        &[[0.0, 0.0], [omega, -omega]],
    );
    amplitudes(
        &selected(&read("attempt-02", "tensor"), "run", 0),
        &[[0.0, 0.0], [1.0, 0.0], [0.0, 0.0], [0.0, 0.0]],
    );
    let kernel =
        qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    for (attempt, name) in [("attempt-01", "sequence"), ("attempt-02", "tensor")] {
        let source = parsed(&read(attempt, name))
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let mut budget = qleisli::contract::exact::Budget::new(100_000);
        let checked = source
            .check_operation_meanings(&kernel, &mut budget)
            .unwrap();
        let raw = checked.lower_raw(&kernel, &mut budget).unwrap();
        raw.validate_source_steps(&kernel.accept(raw.proposal()).unwrap())
            .unwrap();
        let root = SourceRoot::new(&read(attempt, name));
        let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args([
                "check",
                "--format=json",
                "--entry=main::main",
                "--ir-profile=raw",
            ])
            .arg(format!(
                "--module=main={}",
                root.0.join("main.qli").display()
            ))
            .output()
            .unwrap();
        assert!(result.status.success(), "{name}: {result:?}");
        assert!(
            String::from_utf8(result.stdout)
                .unwrap()
                .contains("\"source_meaning_verified\":false")
        );
    }
    let adjoint = parsed(&read("attempt-01", "adjoint"))
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let mut budget = qleisli::contract::exact::Budget::new(100_000);
    let checked = adjoint
        .check_operation_meanings(&kernel, &mut budget)
        .unwrap();
    let raw = checked.lower_raw(&kernel, &mut budget).unwrap();
    raw.validate_source_steps(&kernel.accept(raw.proposal()).unwrap())
        .unwrap();
    for (attempt, name) in [
        ("attempt-01", "zero-bad-child"),
        ("attempt-02", "wrong-tensor"),
    ] {
        let source = parsed(&read(attempt, name))
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let error = source
            .check_operation_meanings(&kernel, &mut qleisli::contract::exact::Budget::new(100_000))
            .unwrap_err();
        assert_eq!(error.code(), "contract", "{name}: {error}");
        assert!(error.message().contains("original Meaning"));
    }
}

#[test]
fn transformed_raw_meanings_preserve_hidden_requests_scalar_phase_and_axis_order() {
    use qleisli::contract::{
        BasisType,
        exact::{Budget, Exact, Matrix},
    };
    use qleisli::interchange::{
        finite_leaf::{UnitaryBoundary, check_unitary},
        native::Kernel,
    };
    let bit = BasisType::Bit;
    let pair = |a, b| BasisType::Pair(Box::new(a), Box::new(b));
    // Literal whole-program expectations, independent of generated requests
    // and of the producer's inversion/control/axis transformations.
    let cases = [
        ("hidden-inverse", bit.clone(), vec![0, 1], vec![0, 7]),
        (
            "nested-control-inverse",
            pair(bit.clone(), bit.clone()),
            vec![0, 1, 2, 3],
            vec![0, 0, 0, 7],
        ),
        (
            "controlled-scalar",
            pair(bit.clone(), BasisType::Unit),
            vec![0, 1],
            vec![0, 1],
        ),
        (
            "reordered-tensor-inverse",
            pair(pair(bit.clone(), bit.clone()), bit),
            vec![0, 2, 1, 3, 4, 6, 5, 7],
            vec![0, 0, 0, 0, 7, 7, 7, 7],
        ),
    ];
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/refined-raw-access-v030/attempt-01");
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let extra = (
        "hidden-controlled-swap",
        pair(BasisType::Bit, pair(BasisType::Bit, BasisType::Bit)),
        vec![0, 1, 2, 5, 4, 3, 6, 7],
        vec![0; 8],
    );
    for (name, signature, permutation, phases) in cases.into_iter().chain([extra]) {
        let text = std::fs::read_to_string(
            directory
                .with_file_name(if name == "hidden-controlled-swap" {
                    "attempt-02"
                } else {
                    "attempt-01"
                })
                .join(format!("{name}.qli")),
        )
        .unwrap();
        let source = parsed(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let mut budget = Budget::new(100_000);
        let checked = source
            .check_operation_meanings(&kernel, &mut budget)
            .unwrap();
        assert!(checked.checked_bindings() > 0, "{name}");
        let raw = checked
            .lower_raw(&kernel, &mut budget)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let accepted = kernel.accept(raw.proposal()).unwrap();
        raw.validate_source_steps(&accepted).unwrap();
        let boundary = UnitaryBoundary::new(
            signature,
            accepted.raw().quantum_inputs[0].clone(),
            accepted.output_ports()[0].clone(),
        )
        .unwrap();
        let dim = permutation.len();
        let mut entries = vec![Exact::zero(); dim * dim];
        for column in 0..dim {
            entries[permutation[column] * dim + column] = Exact::phase(phases[column]);
        }
        check_unitary(
            raw.payload(),
            &boundary,
            &Matrix::new(dim, dim, entries).unwrap(),
            &mut Budget::new(100_000),
        )
        .unwrap_or_else(|e| panic!("{name}: {e}"));
        let root = SourceRoot::new(&text);
        let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args([
                "check",
                "--format=json",
                "--entry=main::main",
                "--ir-profile=raw",
            ])
            .arg(format!(
                "--module=main={}",
                root.0.join("main.qli").display()
            ))
            .output()
            .unwrap();
        assert!(result.status.success(), "{name}: {result:?}");
    }
}
