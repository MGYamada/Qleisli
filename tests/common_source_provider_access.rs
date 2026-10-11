//! Independent permission counterexamples through both public source paths.
//! No fixture is instantiated, emitted, simulated or submitted to a native child.
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
    // Every fixture has an explicit finite eligibility barrier after common
    // checking. Even an erroneous advance to native checking cannot execute
    // this deliberately absent path.
    let absent = root.0.join("must-not-be-executed-native-kernel");
    assert!(!absent.exists());
    check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent)).unwrap_err()
}

fn common_source_valid(source: &str, finite_message: &str, finite_source: &str) {
    let prepared = selected(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    assert_eq!(
        prepared.function_effect("main::probe").unwrap().inferred(),
        Effect::Unitary
    );
    let error = finite(source);
    assert_eq!(error.code, "unsupported", "{source}\n{error:?}");
    assert_eq!(error.message, finite_message, "{error:?}");
    let location = error.primary.unwrap();
    assert!(location.path.ends_with("main.qli"));
    assert_eq!(
        &source[location.span.start..location.span.end],
        finite_source
    );
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
    // Finite eligibility follows complete original checking, so the capability
    // failure must precede every unsupported lowering form in these projects.
    assert_eq!(finite.code, "capability", "{source}\n{finite:?}");
    assert!(finite.message.contains(capability), "{finite:?}");
    let location = finite.primary.unwrap();
    assert!(location.path.ends_with("main.qli"));
    assert_eq!(
        &source[location.span.start..location.span.end],
        supplied_wrapper
    );
}

#[test]
fn constructor_paths_are_checked_independently_through_opaque_forwarding() {
    // Curated source-contract cases, not a copy of the implementation's mask
    // functions. The demand's opaque basis deliberately stops finite lowering
    // after original checking; every case uses an absent native executable.
    // A true row is source-valid, not executable evidence for an opaque U.
    for (description, basis, premises, requested, available) in [
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
    ] {
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
        if available {
            common_source_valid(
                &text,
                "finite profile does not support opaque Basis parameters",
                "B",
            );
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

#[test]
fn apply_only_wrapper_retains_forward_use_without_inverse_or_control() {
    common_source_valid(
        &source!("apply-only-forward"),
        "finite profile does not support opaque Basis parameters",
        "A",
    );
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
    common_source_valid(
        &source!("adjoint-only-backwards-forward"),
        "finite profile does not support opaque Basis parameters",
        "A",
    );
    missing_path(
        &source!("adjoint-only-backwards-inverse"),
        "Adjointable",
        "backwards[V]",
    );
}

#[test]
fn declared_paths_support_the_inverse_and_control_positive_controls() {
    common_source_valid(
        &source!("all-paths-inverse"),
        "finite profile does not support opaque Basis parameters",
        "A",
    );
    common_source_valid(
        &source!("all-paths-controlled"),
        "finite profile does not support opaque Basis parameters",
        "A",
    );
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

#[test]
fn closed_transparent_provider_keeps_its_conditional_control_path() {
    common_source_valid(
        &source!("closed-provider-controlled"),
        "finite profile does not support opaque Basis parameters",
        "A",
    );
}
