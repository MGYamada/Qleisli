//! Capture diagnostics preserve the computed body's existing ownership boundary.
// Copyright 2026 Masahiko G. Yamada
// SPDX-License-Identifier: Apache-2.0

mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{check_project, check_project_diagnostic, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z;
basis fn predicate(x: Bit) -> Bit { x }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
";

fn assert_capture(source: &str, name: &str, quantum: bool) {
    let root = SourceRoot::new(source);
    let diagnostic = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(diagnostic.code, "ownership", "{source}\n{diagnostic:?}");
    assert!(diagnostic.message.contains(&format!(
        "with_computed body cannot capture outer binding `{name}`"
    )));
    assert!(!diagnostic.message.contains("already been consumed"));
    if quantum {
        assert!(diagnostic.message.contains("source data with `join`"));
        assert!(diagnostic.message.contains("data binder"));
    } else {
        assert!(diagnostic.message.contains("closed classical expression"));
    }
    let location = diagnostic.primary.unwrap();
    assert_eq!(
        location.path,
        root.0.join("main.qli").canonicalize().unwrap()
    );
    assert_eq!(&source[location.span.start..location.span.end], name);
    assert!(location.span.start > source.find("with_computed").unwrap());
}

#[test]
fn two_argument_body_reports_live_quantum_capture_at_the_use() {
    let source = format!(
        "{IMPORTS}
unitary fn candidate(q: Q<Bit>, other: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
    let q = with_computed(q,predicate) {{ |flag| cnot(flag,other) }};
    (q,other)
}}"
    );
    assert_capture(&source, "other", true);
}

#[test]
fn certified_body_reports_live_quantum_capture_at_the_use() {
    let source = format!(
        "{IMPORTS}
unitary fn candidate(q: Q<Bit>, other: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
    let q = with_computed(q,predicate,identity) {{ |data,flag| (data,x(other)) }};
    (q,other)
}}"
    );
    assert_capture(&source, "other", true);
}

#[test]
fn certified_classical_capture_has_a_classical_repair_hint() {
    let source = format!(
        "{IMPORTS}
unitary fn candidate(tag: CBit, q: Q<Bit>) -> Q<Bit> {{
    with_computed(q,predicate,identity) {{ |data,flag|
        if tag {{ (data,flag) }} else {{ (data,flag) }}
    }}
}}"
    );
    assert_capture(&source, "tag", false);
}

#[test]
fn actual_consumption_keeps_its_diagnostic_inside_computed_bodies() {
    for (prefix, body, name) in [
        ("let saved=other;", "(data,x(other))", "other"),
        ("", "let held=data; (held,data)", "data"),
    ] {
        let source = format!(
            "{IMPORTS}
unitary fn candidate(q: Q<Bit>, other: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
    {prefix}
    let q=with_computed(q,predicate,identity) {{ |data,flag| {body} }};
    (q,other)
}}"
        );
        let root = SourceRoot::new(&source);
        let diagnostic = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(diagnostic.code, "ownership");
        assert_eq!(
            diagnostic.message,
            format!("quantum ownership `{name}` has already been consumed")
        );
        let span = diagnostic.primary.unwrap().span;
        assert_eq!(&source[span.start..span.end], name);
        assert!(span.start > source.find("with_computed").unwrap());
    }
}

#[test]
fn local_owners_can_shadow_hidden_outer_owners_without_consuming_them() {
    for computed in [
        "with_computed(q,predicate) { |flag| let other=flag; z(other) }",
        "with_computed(q,predicate,identity) { |data,flag| let other=data; (other,flag) }",
    ] {
        let source = format!(
            "{IMPORTS}
unitary fn candidate(q: Q<Bit>, other: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
    let q={computed};
    (q,other)
}}"
        );
        check_project(&SourceRoot::new(&source).0)
            .unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
}

#[test]
fn two_argument_body_keeps_its_existing_classical_capture_support() {
    let source = format!(
        "{IMPORTS}
unitary fn candidate(tag: CBit, q: Q<Bit>) -> Q<Bit> {{
    with_computed(q,predicate) {{ |flag| let _=tag; flag }}
}}"
    );
    check_project(&SourceRoot::new(&source).0).unwrap();
}

#[test]
fn joined_source_data_supports_the_suggested_controlled_gate_repair() {
    let source = format!(
        "{IMPORTS}
basis fn first((x,y): (Bit,Bit)) -> Bit {{ x }}
unitary fn controlled_x(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
    let (control,target)=split(q);
    let (control,target)=cnot(control,target);
    join(control,target)
}}
observe fn main() -> (CBit,CBit) {{
    let q=h(init0());
    let other=init0();
    let pair=with_computed(join(q,other),first,controlled_x) {{ |data,flag|
        let (control,other)=split(data);
        let (flag,other)=cnot(flag,other);
        (join(control,other),flag)
    }};
    let (q,other)=split(pair);
    (measure_z(q),measure_z(other))
}}"
    );
    let root = SourceRoot::new(&source);
    let program = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
    let outcomes = run_closed(&program, SimulationLimits::default()).unwrap();
    for (bits, probability) in &outcomes {
        let expected = if bits[0] == bits[1] { 0.5 } else { 0.0 };
        assert!(
            (probability - expected).abs() < 1e-12,
            "{bits:?}: {probability}"
        );
    }
    for bits in [vec![false, false], vec![true, true]] {
        assert!((outcomes.get(&bits).copied().unwrap_or_default() - 0.5).abs() < 1e-12);
    }
}
