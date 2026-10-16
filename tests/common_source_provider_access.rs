//! Independent permission counterexamples through both public source paths.
//! Source negatives fail before native transport; admitted collections use the native gate.
//! Opaque declarations remain conditional until a concrete operation is bound.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::check_project_with_kernel;
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::Effect;
use std::collections::BTreeMap;

macro_rules! source {
    ($case:literal) => {
        std::fs::read_to_string(common::current_namespace_fixture(
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(concat!(
                "tests/fixtures/authoring_sessions/common-provider-access-v030/attempt-01/",
                $case,
                "/main.qli"
            )),
        ))
        .expect("current permission fixture")
    };
}

fn selected(source: &str) -> Result<ParsedProgram, qleisli::frontend::compile::Error> {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
}

fn finite(source: &str) -> qleisli::frontend::diagnostic::Diagnostic {
    let root = SourceRoot::new(source);
    // Invalid source contracts must fail before any native invocation.
    // An erroneous advance cannot execute this deliberately absent path.
    let absent = root.0.join("must-not-be-executed-native-kernel");
    assert!(!absent.exists());
    check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent)).unwrap_err()
}

fn common_source_valid(source: &str) {
    let prepared = selected(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    assert_eq!(
        prepared.function_effect("main::probe").unwrap().inferred(),
        Effect::Unitary
    );
}

fn ordinary_source_valid(source: &str) {
    common_source_valid(source);
    check_project_with_kernel(
        &SourceRoot::new(source).0,
        SourcePolicy::default(),
        &Kernel::selected().unwrap(),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
}

fn missing_path(source: &str, capability: &str, supplied_wrapper: &str) {
    let sized = selected(source).unwrap_err();
    assert_eq!(sized.code(), "access", "{source}\n{sized}");
    assert!(sized.message().contains(capability), "{sized}");
    assert_eq!(sized.module(), Some("main"));
    assert_eq!(
        &source[sized.span().start..sized.span().end],
        supplied_wrapper
    );

    let finite = finite(source);
    // Complete original checking must report the capability failure before
    // constructing concrete bodies or attempting native transport.
    assert_eq!(finite.code, "capability", "{source}\n{finite:?}");
    assert!(finite.message.contains(capability), "{finite:?}");
    let location = finite.primary.unwrap();
    assert!(location.path.ends_with("main.qli"));
    assert_eq!(
        &source[location.span.start..location.span.end],
        supplied_wrapper
    );
}

// Curated source-contract cases are independent of the implementation's masks.
// An unbound opaque operation remains a conditional source contract.
fn constructor_sources() -> impl Iterator<Item = (String, &'static str, bool)> {
    [
        ("power(U,0)", "Bit", "Applicable(U)", "Applicable", true),
        ("power(U,0)", "Bit", "Applicable(U)", "Adjointable", false),
        ("power(U,0)", "Bit", "Adjointable(U)", "Applicable", false),
        ("power(U,2)", "Bit", "Controllable(U)", "Controllable", true),
        ("adjoint(U)", "Bit", "Adjointable(U)", "Applicable", true),
        ("adjoint(U)", "Bit", "Adjointable(U)", "Adjointable", false),
        ("adjoint(U)", "Bit", "Applicable(U)", "Applicable", false),
        (
            "controlled(U)",
            "(Bit,Bit)",
            "Controllable(U)",
            "Applicable",
            true,
        ),
        (
            "controlled(U)",
            "(Bit,Bit)",
            "Controllable(U)",
            "Adjointable",
            true,
        ),
        (
            "controlled(U)",
            "(Bit,Bit)",
            "Controllable(U)",
            "Controllable",
            true,
        ),
        (
            "controlled(U)",
            "(Bit,Bit)",
            "Applicable(U)",
            "Applicable",
            false,
        ),
        (
            "then_op(U,V)",
            "Bit",
            "Applicable(U),Applicable(V)",
            "Applicable",
            true,
        ),
        (
            "then_op(U,V)",
            "Bit",
            "Applicable(U),Adjointable(V)",
            "Applicable",
            false,
        ),
        (
            "tensor_op(U,V)",
            "(Bit,Bit)",
            "Adjointable(U),Adjointable(V)",
            "Adjointable",
            true,
        ),
        (
            "tensor_op(U,V)",
            "(Bit,Bit)",
            "Adjointable(U),Applicable(V)",
            "Adjointable",
            false,
        ),
        (
            "conjugate_op(U,V)",
            "Bit",
            "Applicable(U),Adjointable(U),Controllable(V)",
            "Controllable",
            true,
        ),
        (
            "conjugate_op(U,V)",
            "Bit",
            "Applicable(U),Controllable(V)",
            "Controllable",
            false,
        ),
        (
            "conjugate_op(U,V)",
            "Bit",
            "Adjointable(U),Controllable(V)",
            "Controllable",
            false,
        ),
        (
            "conjugate_op(U,V)",
            "Bit",
            "Applicable(U),Adjointable(U),Adjointable(V)",
            "Adjointable",
            true,
        ),
        (
            "checked_op(U,Identity)",
            "Bit",
            "Applicable(U)",
            "Applicable",
            true,
        ),
        (
            "checked_op(U,Identity)",
            "Bit",
            "Applicable(U)",
            "Adjointable",
            false,
        ),
        ("wrap[U]", "Bit", "Applicable(U)", "Applicable", true),
        ("wrap[U]", "Bit", "Applicable(U)", "Adjointable", false),
        (
            "wrap[U]",
            "Bit",
            "Applicable(U),Adjointable(U)",
            "Adjointable",
            true,
        ),
        (
            "wrap[U]",
            "Bit",
            "Applicable(U),Adjointable(U)",
            "Controllable",
            false,
        ),
        (
            "wrap[U]",
            "Bit",
            "Applicable(U),Adjointable(U),Controllable(U)",
            "Controllable",
            true,
        ),
    ]
    .into_iter()
    .map(|(description, basis, premises, requested, available)| {
        let text = format!(
            "// π\r\nclassical fn identity(b:Bit)->Bit{{b}}
            meaning Identity:Bit=permutation_by(identity);
            unitary fn demand[const B:Basis,const W:Op<B>](q:Q<B>)->Q<B>
                requires {requested}(W){{q}}
            unitary fn wrap[const W:Op<Bit>](q:Q<Bit>)->Q<Bit>
                requires Applicable(W){{W(q)}}
            pub unitary fn probe[const U:Op<Bit>,const V:Op<Bit>](q:Q<{basis}>)->Q<{basis}>
                requires {premises}{{demand[type({basis}),{description}](q)}}"
        );
        (text, description, available)
    })
}

#[test]
fn constructor_paths_are_checked_independently_through_opaque_forwarding() {
    for (text, description, available) in constructor_sources() {
        if available {
            common_source_valid(&text);
        } else {
            let selected = selected(&text).unwrap_err();
            assert_eq!(selected.code(), "access", "{text}\n{selected}");
            let finite = finite(&text);
            assert_eq!(finite.code, "capability", "{text}\n{finite:?}");
            assert_eq!(finite.message, selected.message(), "{text}");
            assert_eq!(finite.primary.unwrap().span, selected.span(), "{text}");
            // In particular adjoint(U) may fail its construction premise
            // before the enclosing demand. Keep that genuine original site.
            assert!(description.contains(&text[selected.span().start..selected.span().end]));
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_constructor_paths_keep_the_checked_conditional_contracts() {
    for (text, _, _) in constructor_sources().filter(|(_, _, available)| *available) {
        ordinary_source_valid(&text);
    }
}

#[test]
fn apply_only_wrapper_does_not_gain_inverse_or_control() {
    missing_path(&source!("apply-only-inverse"), "Adjointable", "forwards[V]");
    missing_path(
        &source!("apply-only-controlled"),
        "Controllable",
        "forwards[V]",
    );
}

#[test]
fn reversing_an_adjoint_only_wrapper_needs_the_original_apply_path() {
    // backwards[V] computes V†. Its forward invocation uses the available
    // Adjointable(V); reversing that whole wrapper would compute V, whose Apply
    // is absent. Checking only the argument's Adjoint would miss this case.
    missing_path(
        &source!("adjoint-only-backwards-inverse"),
        "Adjointable",
        "backwards[V]",
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn declared_paths_support_forward_inverse_and_control_in_ordinary_checks() {
    for source in [
        source!("apply-only-forward"),
        source!("adjoint-only-backwards-forward"),
        source!("all-paths-inverse"),
        source!("all-paths-controlled"),
    ] {
        ordinary_source_valid(&source);
    }
}

#[test]
fn unused_actual_operations_still_constrain_the_conservative_wrapper() {
    missing_path(&source!("unused-op-inverse"), "Adjointable", "ignored[V]");
    missing_path(
        &source!("unused-op-controlled"),
        "Controllable",
        "ignored[V]",
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn closed_transparent_provider_keeps_its_conditional_control_path() {
    ordinary_source_valid(&source!("closed-provider-controlled"));
}
