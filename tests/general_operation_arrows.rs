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
        Effect::Iso
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
