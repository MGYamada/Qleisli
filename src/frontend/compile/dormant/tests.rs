//! Zero-qubit checks of original association, budget failure and revisits.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::project::{ModuleOrigin, SourceModule};

fn project() -> Project {
    let source = "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
        unitary fn hold[const U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Applicable(U){U(q)}
        unitary fn unused[const V:Op<Unit>](q:Q<Unit>)->Q<Unit>{hold[identity](q)}";
    Project {
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: source.into(),
                ast: crate::frontend::parser::parse_module(source).unwrap(),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn exhausted_dormant_visit_restores_context_and_never_registers_an_instance() {
    let project = project();
    let mut failed_after_owner_switch = false;
    for allowance in (8..=128).step_by(8) {
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let identity = compiler
            .source
            .resolution
            .qualified("main::identity")
            .unwrap();
        compiler.checking = Some(identity);
        compiler.work = MAX_WORK - allowance;
        let before = compiler.work;
        let error = compiler.check_dormant_operations().unwrap_err();
        assert!(compiler.work >= before && compiler.work <= MAX_WORK);
        assert_eq!(compiler.checking, Some(identity));
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
        if error.code == ErrorCode::Limit && error.message.contains("while checking main::unused") {
            failed_after_owner_switch = true;
            assert!(compiler.work > before);
            break;
        }
    }
    assert!(
        failed_after_owner_switch,
        "exercise failure after changing the active owner"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn a_registry_revisit_keeps_native_body_checking_separate_from_ordinary_roots() {
    let project = project();
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let (kernel, decisions) = compiler.kernel.recording();
    compiler.kernel = kernel;
    let identity = compiler
        .source
        .resolution
        .qualified("main::identity")
        .unwrap();
    let hold = compiler.source.resolution.qualified("main::hold").unwrap();
    let program = lower::lower_function(&mut compiler, &identity).unwrap();
    compiler.checked.insert(identity, program);
    compiler.check_dormant_operations().unwrap();
    assert_eq!(compiler.instances.len(), 1);
    let before = compiler.work;
    let before_decisions = decisions.summary().decisions();
    compiler.check_dormant_operations().unwrap();
    assert_eq!(compiler.instances.len(), 1);
    assert!(compiler.work > before);
    // The provider descriptor is already cached. A fresh decision protects the
    // actual concrete body gate from being replaced with a registry hit.
    assert!(decisions.summary().decisions() > before_decisions);
    assert!(!compiler.checked.contains_key(&hold));
    assert_eq!(compiler.checked.len(), 1);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_original_borrow_refuses_another_owner_and_missing_node() {
    let project = project();
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let identity = compiler
        .source
        .resolution
        .qualified("main::identity")
        .unwrap();
    let call = compiler
        .source
        .static_calls
        .values()
        .find(|p| !p.arguments.is_empty())
        .unwrap();
    let owner = call.owner;
    let mut operation = (*call.arguments[0].value).clone();
    assert!(
        compiler
            .original_operation(owner, "main", &operation)
            .is_ok()
    );
    assert_eq!(
        compiler
            .original_operation(identity, "main", &operation)
            .unwrap_err()
            .code,
        ErrorCode::TypeMismatch
    );
    operation.node = None;
    assert_eq!(
        compiler
            .original_operation(owner, "main", &operation)
            .unwrap_err()
            .code,
        ErrorCode::TypeMismatch
    );
    assert!(compiler.providers.is_empty());
    assert!(compiler.instances.is_empty());
}
