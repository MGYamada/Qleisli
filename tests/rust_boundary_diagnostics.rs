//! Existing Rust-boundary refusals and permitted ordinary/explicit consumption.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::Span;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::{check_project, check_project_with_kernel, compile_project};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::Effect;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn sources(source: &str) -> BTreeMap<String, String> {
    BTreeMap::from([("main".into(), source.into())])
}

fn at(source: &str, marker: &str, offset: usize, length: usize) -> Span {
    let start = source.rfind(marker).unwrap() + offset;
    Span::new(start, start + length)
}

fn shared_rejection(
    source: &str,
    common_code: &str,
    finite_code: &str,
    span: Span,
    prefix: &str,
) -> String {
    let common = ParsedProgram::parse(sources(source)).unwrap_err();
    assert_eq!(common.code(), common_code, "{source}\n{common}");
    assert_eq!(common.module(), Some("main"));
    assert_eq!(common.span(), span, "{source}\n{common}");
    assert!(common.message().starts_with(prefix), "{common}");

    let root = SourceRoot::new(source);
    let absent = root.0.join("must-not-start-a-native-checker");
    assert!(!absent.exists());
    // Use the public explicit gate, without changing process environment.
    // An accidental acceptance would reach the absent checker and report a
    // different category rather than the expected first source judgment.
    let finite = check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent))
        .unwrap_err();
    assert_eq!(finite.code, finite_code, "{source}\n{finite:?}");
    assert_eq!(finite.message, common.message(), "{source}");
    let location = finite.primary.unwrap();
    assert_eq!(
        location.path,
        root.0.join("main.qli").canonicalize().unwrap()
    );
    assert_eq!(location.span, span, "{source}");
    common.message().into()
}

fn implicit_loss(message: &str) {
    assert!(
        message.contains("implicit quantum destruction is forbidden"),
        "{message}"
    );
    assert!(
        message.contains("Measurement, discard, reset and checked clean discharge are distinct"),
        "{message}"
    );
    assert!(
        message.contains("reset returns a fresh quantum owner"),
        "{message}"
    );
}

fn no_rust_name_hint(message: &str) {
    assert!(!message.contains("built-in Rust"), "{message}");
    assert!(
        !message.contains("implicit quantum destruction"),
        "{message}"
    );
}

fn common_and_finite(source: &str) -> ParsedProgram {
    let common = ParsedProgram::parse(sources(source)).unwrap();
    check_project(&SourceRoot::new(source).0).unwrap();
    common
}

fn closed_bit(source: &str, expected: bool) -> ParsedProgram {
    let common = ParsedProgram::parse(sources(source)).unwrap();
    let program = compile_project(&SourceRoot::new(source).0).unwrap();
    let actual = run_closed(&program, SimulationLimits::default()).unwrap();
    let desired = BTreeMap::from([(vec![expected], 1.0)]);
    for outcome in actual.keys().chain(desired.keys()) {
        let got = actual.get(outcome).copied().unwrap_or(0.0);
        let want = desired.get(outcome).copied().unwrap_or(0.0);
        assert!((got - want).abs() < 1e-12, "{source}\n{actual:?}");
    }
    common
}

#[test]
fn unresolved_drop_keeps_callee_priority_without_inspecting_its_argument() {
    let mut messages = Vec::new();
    // The Unicode/CRLF prefix also keeps the common and filesystem locations
    // accountable to source byte offsets. `not q` would be a type error if its
    // argument were checked, but unresolved callee lookup must win first.
    for argument in ["0", "q", "not q"] {
        let source =
            format!("// 日本語\r\npub unitary fn client(q:Q<Bit>)->Q<Bit>{{drop({argument});q}}");
        let message = shared_rejection(
            &source,
            "name",
            "unknown_name",
            at(&source, "drop(", 0, 4),
            "unresolved function drop",
        );
        assert!(
            message.contains("there is no built-in Rust drop or forget operation"),
            "{message}"
        );
        assert!(
            message.contains("Ordinary Bit/Unit may be unused or matched by _"),
            "{message}"
        );
        assert!(
            message.contains("If a value contains live Q<T>"),
            "{message}"
        );
        assert!(
            message.contains("scope exit is not destruction"),
            "{message}"
        );
        messages.push(message);
    }
    assert_eq!(messages[0], messages[1]);
    assert_eq!(messages[1], messages[2]);

    let ordinary = "pub unitary fn client(q:Q<Bit>)->Q<Bit>{missing(not q);q}";
    let message = shared_rejection(
        ordinary,
        "name",
        "unknown_name",
        at(ordinary, "missing(", 0, 7),
        "unresolved function missing",
    );
    assert_eq!(message, "unresolved function missing");
}

#[test]
fn user_helpers_and_local_categories_do_not_acquire_rust_name_privileges() {
    let classical = "unitary fn drop(b:Bit)->Unit{()}
        pub observe fn main()->Bit{drop(0);1}";
    let common = closed_bit(classical, true);
    assert_eq!(
        common.function_effect("main::drop").unwrap().inferred(),
        Effect::Unitary
    );

    let observing = "use std::quantum::init0; use std::observe::discard;
        observe fn drop(q:Q<Bit>)->Unit{discard(q)}
        pub observe fn main()->Bit{drop(init0());1}";
    let common = closed_bit(observing, true);
    assert_eq!(
        common.function_effect("main::drop").unwrap().inferred(),
        Effect::Observe
    );

    let wrong_argument = "unitary fn drop(b:Bit)->Unit{()}
        pub unitary fn client(q:Q<Bit>)->Q<Bit>{drop(q);q}";
    let message = shared_rejection(
        wrong_argument,
        "type",
        "type_mismatch",
        at(wrong_argument, "drop(q)", "drop(".len(), 1),
        "type or tuple/size shape mismatch: expected `Bit`, found `Q<Bit>`",
    );
    no_rust_name_hint(&message);

    let local = "unitary fn drop(b:Bit)->Unit{()}
        pub unitary fn client(q:Q<Bit>)->Q<Bit>{let drop=0;drop(q)}";
    let message = shared_rejection(
        local,
        "type",
        "type_mismatch",
        at(local, "drop(", 0, 4),
        "a local value is not callable",
    );
    assert_eq!(message, "a local value is not callable");
    no_rust_name_hint(&message);

    // An ordinary function named clone may transfer one owner, but cannot
    // confer a second use of its consumed input by virtue of that spelling.
    let transfer = "unitary fn clone(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn client(q:Q<Bit>)->(Q<Bit>,Q<Bit>){(clone(q),q)}";
    let message = shared_rejection(
        transfer,
        "ownership",
        "ownership",
        at(transfer, ",q)", 1, 1),
        "quantum ownership `q` has already been consumed",
    );
    no_rust_name_hint(&message);
}

#[test]
fn ordinary_loss_remains_permitted_but_nested_zero_width_owners_cannot_disappear() {
    // Pair each existing loss site with the same ordinary tuple shape. Unit
    // adds no wire; replacing one ordinary field with Q<Unit> still creates
    // a live owner and must preserve each site's original diagnostic span.
    for (body, marker, length, prefix) in [
        (
            "()",
            "env:",
            3,
            "quantum ownership `env` was not returned or explicitly consumed",
        ),
        (
            "let _=env;()",
            "_",
            1,
            "wildcard would discard quantum ownership",
        ),
        (
            "env;()",
            "env;",
            3,
            "expression statement would discard quantum ownership",
        ),
        (
            "let packet=env;()",
            "packet",
            6,
            "local quantum ownership `packet` escapes neither through the result nor an explicit discard",
        ),
        (
            "let env=0;()",
            "env=0",
            3,
            "binding env would drop a live quantum owner",
        ),
    ] {
        let classical = format!("pub unitary fn client(env:(Bit,(Unit,Bit)))->Unit{{{body}}}");
        common_and_finite(&classical);

        let quantum = format!("pub unitary fn client(env:(Bit,(Unit,Q<Unit>)))->Unit{{{body}}}");
        let message = shared_rejection(
            &quantum,
            "ownership",
            "ownership",
            at(&quantum, marker, 0, length),
            prefix,
        );
        implicit_loss(&message);
    }
}

#[test]
fn reset_returns_an_owner_and_linear_shadowing_can_return_the_replacement() {
    let lost = "use std::observe::reset;
        pub observe fn client(q:Q<Bit>)->Unit{reset(q);()}";
    let message = shared_rejection(
        lost,
        "ownership",
        "ownership",
        at(lost, "reset(q)", 0, "reset(q)".len()),
        "expression statement would discard quantum ownership",
    );
    implicit_loss(&message);

    let retained = "use std::quantum::init0; use std::quantum::h;
        use std::observe::reset; use std::observe::measure_z;
        pub observe fn reset_owner(q:Q<Bit>)->Q<Bit>{reset(q)}
        pub unitary fn linear_owner(q:Q<Bit>)->Q<Bit>{let q=h(q);q}
        pub observe fn main()->Bit{measure_z(reset_owner(linear_owner(init0())))}";
    // One qubit: H prepares |+>; reset returns |0> as a new logical owner;
    // returning/observing that owner is valid and must read zero with weight 1.
    let common = closed_bit(retained, false);
    assert_eq!(
        common
            .function_effect("main::reset_owner")
            .unwrap()
            .inferred(),
        Effect::Observe
    );
    assert_eq!(
        common
            .function_effect("main::linear_owner")
            .unwrap()
            .inferred(),
        Effect::Unitary
    );
}
