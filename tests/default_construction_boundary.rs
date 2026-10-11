//! Default spelling never manufactures live quantum ownership or hides effects.
//! Bounded source/native controls do not establish a general trait theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::Span;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::{check_project_with_kernel, project_effects_with_kernel};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::Effect;
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
    // No process-global environment override: source refusal must precede an
    // accidental native invocation, which would instead fail at this path.
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

fn checked_finite_effects(source: &str, expected: &[(&str, Effect)]) {
    let common = ParsedProgram::parse(sources(source)).unwrap();
    let finite = project_effects_with_kernel(
        &SourceRoot::new(source).0,
        SourcePolicy::default(),
        &Kernel::selected().unwrap(),
    )
    .unwrap();
    for (name, effect) in expected {
        let path = format!("main::{name}");
        let fact = common.function_effect(&path).unwrap();
        assert_eq!(fact.inferred(), *effect, "{source}\n{path}");
        assert_eq!(fact, finite.function_effect(&path).unwrap(), "{path}");
    }
}

fn no_default_hint(message: &str) {
    assert!(!message.contains("built-in Rust Default"), "{message}");
}

#[test]
fn unresolved_default_has_one_conditional_hint_without_creating_a_factory() {
    let mut messages = Vec::new();
    // Identical callee failures for ordinary and quantum results do not infer
    // the requested result type or silently insert a conversion/preparation.
    for result in [
        "Bit",
        "Unit",
        "Q<Bit>",
        "Q<Unit>",
        "Q<Bits<0>>",
        "(Bit,(Unit,Q<Unit>))",
    ] {
        let source = format!("// 日本語\r\npub fn client()->{result}{{default()}}");
        messages.push(shared_rejection(
            &source,
            "name",
            "unknown_name",
            at(&source, "default()", 0, 7),
            "unresolved function default",
        ));
    }
    // All declarations are source checked, including an unused Basis body.
    let generic = "pub fn unused[const A:Basis]()->Q<A>{default()}\n\
        pub fn client()->Unit{()}";
    messages.push(shared_rejection(
        generic,
        "name",
        "unknown_name",
        at(generic, "default()", 0, 7),
        "unresolved function default",
    ));
    // `not q` would fail typing, but unresolved callee lookup still wins.
    let priority = "pub fn client(q:Q<Bit>)->Q<Bit>{default(not q);q}";
    messages.push(shared_rejection(
        priority,
        "name",
        "unknown_name",
        at(priority, "default(", 0, 7),
        "unresolved function default",
    ));
    for message in &messages {
        assert_eq!(message, &messages[0]);
        assert!(
            message.contains("there is no built-in Rust Default operation"),
            "{message}"
        );
        assert!(
            message.contains("Ordinary Bit/Unit can be constructed explicitly"),
            "{message}"
        );
        assert!(message.contains("Q<Unit>"), "{message}");
        assert!(message.contains("product"), "{message}");
        assert!(
            message.contains("quantum preparation is explicit"),
            "{message}"
        );
    }
    let missing = "pub fn client(q:Q<Bit>)->Q<Bit>{missing(not q);q}";
    assert_eq!(
        shared_rejection(
            missing,
            "name",
            "unknown_name",
            at(missing, "missing(", 0, 7),
            "unresolved function missing",
        ),
        "unresolved function missing"
    );
}

#[test]
fn resolved_user_defaults_keep_ordinary_bodies_and_explicit_preparation() {
    checked_finite_effects(
        "fn default()->Bit{0} pub fn client()->Bit{default()}",
        &[("default", Effect::Unitary), ("client", Effect::Unitary)],
    );
    checked_finite_effects(
        "fn default()->Unit{()} pub fn client()->(Unit,Unit){let u=default();(u,u)}",
        &[("default", Effect::Unitary), ("client", Effect::Unitary)],
    );
    checked_finite_effects(
        "use std::quantum::init0; fn default()->Q<Bit>{init0()}\n\
         pub fn client()->Q<Bit>{default()}",
        &[("default", Effect::Isometry), ("client", Effect::Isometry)],
    );
    let generic = "fn default[const A:Basis](q:Q<A>)->Q<A>{q}\n\
        pub fn client(q:Q<Bit>)->Q<Bit>{default[type(Bit)](q)}";
    let common = ParsedProgram::parse(sources(generic)).unwrap();
    for name in ["default", "client"] {
        assert_eq!(
            common
                .function_effect(&format!("main::{name}"))
                .unwrap()
                .inferred(),
            Effect::Unitary
        );
    }
    common
        .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    // First execution exposed the existing finite type-argument restriction.
    // A valid common judgment does not supply that missing concrete lowering.
    let finite = project_effects_with_kernel(
        &SourceRoot::new(generic).0,
        SourcePolicy::default(),
        &Kernel::selected().unwrap(),
    )
    .unwrap_err();
    assert_eq!(finite.code, "unsupported");
    assert_eq!(
        finite.message,
        "static argument is outside the finite lowering profile"
    );
    assert_eq!(finite.primary.unwrap().span, at(generic, "type(Bit)", 0, 9));

    let local = "fn default()->Bit{0} pub fn client()->Bit{let default=0;default()}";
    let message = shared_rejection(
        local,
        "type",
        "type_mismatch",
        at(local, "default()", 0, 7),
        "a local value is not callable",
    );
    assert_eq!(message, "a local value is not callable");
    no_default_hint(&message);
}

#[test]
fn false_unitary_assertions_cannot_hide_default_named_preparation() {
    for (source, marker) in [
        (
            "use std::quantum::init0; unitary fn default()->Q<Bit>{init0()}\n\
             pub fn client()->Q<Bit>{default()}",
            "init0()",
        ),
        (
            "use std::quantum::init0; fn default()->Q<Bit>{init0()}\n\
             pub unitary fn client()->Q<Bit>{default()}",
            "default()",
        ),
    ] {
        let message = shared_rejection(
            source,
            "effect",
            "effect",
            at(source, marker, 0, marker.len()),
            "body effect `Isometry` exceeds asserted `Unitary`",
        );
        assert!(
            message.contains("Semantic error: \"externally unitary\" is not supported"),
            "{message}"
        );
        assert!(
            message.contains("cannot override the effect inferred from the body"),
            "{message}"
        );
        assert!(!message.contains("github.com"), "{message}");
        no_default_hint(&message);
    }
}

#[test]
fn explicit_unit_maps_do_not_make_zero_width_owners_ordinary_defaults() {
    let explicit = "use std::quantum::{unit,finish}; fn default()->Q<Unit>{unit(())}\n\
        pub fn client()->Unit{finish(default())}";
    let common = ParsedProgram::parse(sources(explicit)).unwrap();
    for name in ["default", "client"] {
        assert_eq!(
            common
                .function_effect(&format!("main::{name}"))
                .unwrap()
                .inferred(),
            Effect::Unitary
        );
    }
    // Finite concrete lowering deliberately does not materialize these maps.
    // Existing quantum_unit_maps supplies independent native/scalar equations.
    common
        .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();

    let implicit = "pub fn default()->Q<Unit>{()}";
    let message = shared_rejection(
        implicit,
        "type",
        "type_mismatch",
        at(implicit, "{()}", 1, 2),
        "type or tuple/size shape mismatch: expected `Q<Unit>`, found `Unit`",
    );
    no_default_hint(&message);

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
    ] {
        let source = format!("pub fn default(env:(Bit,(Unit,Q<Unit>)))->Unit{{{body}}}");
        let message = shared_rejection(
            &source,
            "ownership",
            "ownership",
            at(&source, marker, 0, length),
            prefix,
        );
        assert!(
            message.contains("implicit quantum destruction is forbidden"),
            "{message}"
        );
        no_default_hint(&message);
    }

    let duplicate = "pub fn default(q:Q<Unit>)->(Q<Unit>,Q<Unit>){(q,q)}";
    let message = shared_rejection(
        duplicate,
        "ownership",
        "ownership",
        at(duplicate, ",q)", 1, 1),
        "quantum ownership `q` has already been consumed",
    );
    no_default_hint(&message);
}
