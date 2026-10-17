//! Original primitive Ctrl actions in otherwise uninstantiated Op-only bodies.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, check_project_report_with_kernel};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_primitive_x_refuses_at_its_original_action_like_a_direct_call() {
    for source in [
        "use std::gate::x;
         unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
         requires Applicable(U){x(ctrl q);U(q)}",
        "use std::gate::x;
         unitary fn direct(q:Q<Bit>)->Q<Bit>{x(ctrl q);q}",
    ] {
        let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
        assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
        assert!(failure.message.contains("sector preservation"), "{failure}");
        assert_eq!(&source[failure.span.start..failure.span.end], "x(ctrl q)");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_zero_width_primitive_actions_each_require_a_fresh_native_request() {
    let kernel = Kernel::selected().unwrap();
    for basis in ["Unit", "(Unit,Unit)"] {
        let source = |actions: &str| {
            format!(
                "
                 unitary fn unused[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}>
                 requires Applicable(U){{{actions}U(q)}}"
            )
        };
        let check = |actions: &str| {
            check_project_report_with_kernel(
                &SourceRoot::new(&source(actions)).0,
                SourcePolicy::default(),
                &kernel,
            )
            .unwrap()
        };
        let before = check("").native_decisions().requests_checked();
        for (actions, expected) in [
            ("global_phase_eighth(ctrl q);", 1),
            (
                "global_phase_eighth(ctrl q);global_phase_eighth(ctrl q);",
                2,
            ),
        ] {
            let report = check(actions);
            assert_eq!(
                report.native_decisions().requests_checked(),
                before + expected
            );
            assert_eq!(report.entry_request_checked(), None);
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_primitive_owner_type_comes_from_the_referenced_parameter_identity() {
    let positive = "
        unitary fn unused[const U:Op<Unit>](bit:Q<Bit>,scalar:Q<Unit>)->(Q<Bit>,Q<Unit>)
        requires Applicable(U){global_phase_eighth(ctrl scalar);(bit,U(scalar))}";
    let kernel = Kernel::selected().unwrap();
    let report = check_project_report_with_kernel(
        &SourceRoot::new(positive).0,
        SourcePolicy::default(),
        &kernel,
    )
    .unwrap();
    assert!(report.native_decisions().requests_checked() > 0);
    let negative = "use std::gate::x;
        unitary fn unused[const U:Op<Unit>](scalar:Q<Unit>,bit:Q<Bit>)->(Q<Unit>,Q<Bit>)
        requires Applicable(U){x(ctrl bit);(U(scalar),bit)}";
    let failure = check_project(&SourceRoot::new(negative).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
    assert_eq!(
        &negative[failure.span.start..failure.span.end],
        "x(ctrl bit)"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_primitive_action_does_not_restore_a_spent_source_parameter() {
    let source = "
        unitary fn unused[const U:Op<Unit>](q:Q<Unit>)->Q<Unit>
        requires Applicable(U){let moved=q;global_phase_eighth(ctrl q);U(moved)}";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Ownership, "{failure}");
    assert_eq!(&source[failure.span.start..failure.span.end], "q");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn a_same_spelled_user_declaration_keeps_its_original_callee_category() {
    let source = "unitary fn x(q:Q<Bit>)->Q<Bit>{q}
        unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
        requires Applicable(U){x(ctrl q);U(q)}";
    check_project(&SourceRoot::new(source).0).unwrap();
}
