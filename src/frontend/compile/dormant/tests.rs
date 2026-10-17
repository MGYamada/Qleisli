//! Zero-qubit checks of original association, budget failure and revisits.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::exact::Exact;
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_original_region_restores_the_complete_instance_on_every_result() {
    let mut project = project();
    let source = "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
        unitary fn unused[const n:Nat](q:Q<Unit>)->Q<Unit>{
            if static n>=1 {identity(q)} else {q}}
        unitary fn guard(q:Q<Unit>)->Q<Unit>{q}";
    let module = project.modules.get_mut("main").unwrap();
    module.ast = crate::frontend::parser::parse_module(source).unwrap();
    module.source = source.into();
    for outcome in 0..3 {
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let owner = compiler
            .source
            .resolution
            .qualified("main::unused")
            .unwrap();
        let guard = compiler.source.resolution.qualified("main::guard").unwrap();
        let key = compiler.source.interfaces[&owner].statics[0].key.clone();
        let environment = Arc::clone(
            &compiler
                .source
                .static_calls
                .values()
                .find(|plan| plan.owner == owner && !plan.environment.regions.is_empty())
                .unwrap()
                .environment,
        );
        let span = compiler.declarations[&owner].span;
        let instance = compiler
            .prepare_instance(
                owner,
                BTreeMap::new(),
                BTreeMap::from([(key.clone(), 0)]),
                Bindings::new(),
                "main",
                span,
            )
            .unwrap();
        compiler.checking = Some(guard);
        let frame = compiler
            .enter_instance(Arc::clone(&instance), "main", span)
            .unwrap();
        let before = compiler.work;
        let exact_before = compiler.exact_work.remaining();
        let result =
            compiler.visit_dormant_environment(&environment, "main", span, |compiler, inactive| {
                assert!(inactive);
                assert_eq!(compiler.current_instance_owner(), Some(owner));
                assert!(Arc::ptr_eq(
                    compiler.concrete_context.current.as_ref().unwrap(),
                    &instance
                ));
                assert_eq!(compiler.concrete_context.naturals.get(&key), Some(&0));
                let check::plans::StaticRegion::Predicate { left, .. } = &environment.regions[0]
                else {
                    panic!("original predicate region")
                };
                assert_eq!(
                    compiler.evaluate_plan_natural_partial(left, &environment)?,
                    None,
                    "conditional arithmetic cannot reuse concrete Nat values"
                );
                match outcome {
                    0 => Ok(()),
                    1 => Err(compiler.dormant_error(
                        "main",
                        span,
                        ErrorCode::TypeMismatch,
                        "private inactive-region refusal",
                    )?),
                    _ => compiler.charge("main", span, MAX_WORK),
                }
            });
        assert_eq!(compiler.checking, Some(owner));
        assert_eq!(compiler.current_instance_owner(), Some(owner));
        assert!(Arc::ptr_eq(
            compiler.concrete_context.current.as_ref().unwrap(),
            &instance
        ));
        assert_eq!(compiler.concrete_context.naturals.get(&key), Some(&0));
        assert!(compiler.work >= before && compiler.work <= MAX_WORK);
        assert_eq!(compiler.exact_work.remaining(), exact_before);
        assert!(compiler.checked.is_empty());
        assert!(matches!(
            compiler.instances[instance.record.unwrap()].body,
            instances::BodyState::Unprepared
        ));
        match outcome {
            0 => assert!(result.is_ok()),
            1 => assert_eq!(result.unwrap_err().code, ErrorCode::TypeMismatch),
            _ => assert_eq!(result.unwrap_err().code, ErrorCode::Limit),
        }
        compiler.leave_instance(frame);
        assert_eq!(compiler.checking, Some(guard));
        assert_eq!(compiler.current_instance_owner(), None);
        assert!(compiler.concrete_context.current.is_none());
        assert!(compiler.concrete_context.naturals.is_empty());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_carry_checks_bound_ops_with_the_actual_original_nat_owner_type() {
    for gate in ["x", "z"] {
        let mut project = project();
        let source = format!(
            "use std::quantum::{gate};use std::registers::{{take_bit,put_bit}};
            unitary fn actual(q:Q<Bits<1>>)->Q<Bits<1>>{{
                let(b,empty)=take_bit[1,0](q);put_bit[1,0]({gate}(b),empty)}}
            unitary fn unused[const n:Nat,const U:Op<Bits<n>>](q:Q<Bits<n>>)->Q<Bits<n>>
              requires Applicable(U){{qfor static i in 0..0 carry r=q{{U(ctrl r);yield r;}}}}"
        );
        let module = project.modules.get_mut("main").unwrap();
        module.ast = crate::frontend::parser::parse_module(&source).unwrap();
        module.source = source;
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let actual = compiler
            .source
            .resolution
            .qualified("main::actual")
            .unwrap();
        let owner = compiler
            .source
            .resolution
            .qualified("main::unused")
            .unwrap();
        let span = compiler.declarations[&owner].span;
        let provider = compiler
            .prepare_instance(
                actual,
                BTreeMap::new(),
                BTreeMap::new(),
                Bindings::new(),
                "main",
                span,
            )
            .unwrap();
        let operation = compiler
            .provider_instance(provider, None, "main", span)
            .unwrap();
        let statics = &compiler.source.interfaces[&owner].statics;
        let n = statics[0].key.clone();
        let op = statics[1].key.clone();
        let instance = compiler
            .prepare_instance(
                owner,
                BTreeMap::new(),
                BTreeMap::from([(n, 1)]),
                BTreeMap::from([(op, operation)]),
                "main",
                span,
            )
            .unwrap();
        let (kernel, decisions) = compiler.kernel.recording();
        compiler.kernel = kernel;
        compiler.checking = Some(actual);
        let before = compiler.work;
        let result = compiler.check_dormant_instance(instance, "main", span);
        if gate == "x" {
            let failure = result.unwrap_err();
            assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
            assert!(failure.message.contains("sector preservation"));
            assert_eq!(
                &project.modules["main"].source[failure.span.start..failure.span.end],
                "U(ctrl r)"
            );
        } else {
            result.unwrap();
            assert!(
                decisions.summary().requests_checked() > 0,
                "a preserving actual still reaches a fresh native action gate"
            );
        }
        assert_eq!(compiler.checking, Some(actual));
        assert_eq!(compiler.current_instance_owner(), None);
        assert!(compiler.concrete_context.current.is_none());
        assert!(compiler.concrete_context.naturals.is_empty());
        assert!(compiler.work > before);
        assert!(compiler.checked.is_empty());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_basis_carry_retains_distinct_zero_width_actual_owner_trees() {
    for basis in ["Unit", "Bits<0>"] {
        let mut project = project();
        let source = format!(
            "use std::quantum::phase_eighth;
            unitary fn actual(q:Q<{basis}>)->Q<{basis}>{{phase_eighth(q)}}
            unitary fn unused[const A:Basis,const U:Op<A>](q:Q<A>)->Q<A>
              requires Applicable(U){{qfor static i in 0..0 carry r=q{{U(ctrl r);yield r;}}}}"
        );
        let module = project.modules.get_mut("main").unwrap();
        module.ast = crate::frontend::parser::parse_module(&source).unwrap();
        module.source = source;
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let actual = compiler
            .source
            .resolution
            .qualified("main::actual")
            .unwrap();
        let owner = compiler
            .source
            .resolution
            .qualified("main::unused")
            .unwrap();
        let span = compiler.declarations[&owner].span;
        let provider = compiler
            .prepare_instance(
                actual,
                BTreeMap::new(),
                BTreeMap::new(),
                Bindings::new(),
                "main",
                span,
            )
            .unwrap();
        let operation = compiler
            .provider_instance(provider, None, "main", span)
            .unwrap();
        let closed_basis = if basis == "Unit" {
            Ty::unit()
        } else {
            Ty::bits(0)
        };
        assert_eq!(operation.basis, closed_basis);
        let statics = &compiler.source.interfaces[&owner].statics;
        let a = statics[0].key.clone();
        let op = statics[1].key.clone();
        let instance = compiler
            .prepare_instance(
                owner,
                BTreeMap::from([(a, closed_basis)]),
                BTreeMap::new(),
                BTreeMap::from([(op, operation)]),
                "main",
                span,
            )
            .unwrap();
        let (kernel, decisions) = compiler.kernel.recording();
        compiler.kernel = kernel;
        compiler
            .check_dormant_instance(instance, "main", span)
            .unwrap();
        assert!(
            decisions.summary().requests_checked() > 0,
            "zero physical axes retain a logical owner and actual native request"
        );
        assert_eq!(compiler.current_instance_owner(), None);
        assert!(compiler.concrete_context.current.is_none());
        assert!(compiler.checked.is_empty());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn unused_original_static_roots_cannot_hide_closed_u32_overflow() {
    for body in [
        "static let unused=4294967295+1;q",
        "static let unused=n+(4294967295+1);q",
        "if static 4294967295+1==0 {q} else {q}",
        "qfor static i in 0..4294967295+1 carry r=q {yield r;}",
    ] {
        let mut project = project();
        let source = format!("unitary fn unused[const n:Nat](q:Q<Unit>)->Q<Unit>{{{body}}}");
        let module = project.modules.get_mut("main").unwrap();
        module.ast = crate::frontend::parser::parse_module(&source).unwrap();
        module.source = source;
        // Common symbolic checking admits these i128 affine expressions. The
        // original ordinary execution contract still requires u32 arithmetic.
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        assert!(compiler.source.static_calls.is_empty());
        let before = compiler.work;
        let error = compiler.check_dormant_operations().unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit, "{error}");
        assert!(error.message.contains("concrete natural arithmetic"));
        assert!(matches!(
            &project.modules["main"].source[error.span.start..error.span.end],
            "4294967295+1" | "(4294967295+1)"
        ));
        assert!(compiler.work > before);
        assert_eq!(compiler.checking, None);
        assert_eq!(compiler.current_instance_owner(), None);
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_guarded_owner_subtraction_stays_conditional_without_losing_valid_phase() {
    let mut project = project();
    let source = "use std::registers::{take_bit,put_bit};use std::quantum::phase_eighth;
        unitary fn guarded[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{
            if static n==0 {q} else {
                let(b,r)=take_bit[n,0](q);phase_eighth(ctrl r);put_bit[n,0](b,r)}}";
    let module = project.modules.get_mut("main").unwrap();
    module.ast = crate::frontend::parser::parse_module(source).unwrap();
    module.source = source.into();
    for n in [0, 1] {
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let owner = compiler
            .source
            .resolution
            .qualified("main::guarded")
            .unwrap();
        let formal = compiler.source.interfaces[&owner].statics[0].key.clone();
        let span = compiler.declarations[&owner].span;
        let instance = compiler
            .prepare_instance(
                owner,
                BTreeMap::new(),
                BTreeMap::from([(formal, n)]),
                Bindings::new(),
                "main",
                span,
            )
            .unwrap();
        let body = compiler
            .materialize_instance(instance, "main", span)
            .unwrap();
        let matrix = crate::contract::function::verified_meaning(
            &body,
            &crate::contract::BasisType::Bits(n),
            &mut compiler.exact_work,
        )
        .unwrap();
        let dimension = 1usize << n;
        for row in 0..dimension {
            for column in 0..dimension {
                let expected = if row != column {
                    Exact::zero()
                } else if n == 0 {
                    Exact::one()
                } else {
                    Exact::phase(1)
                };
                assert_eq!(matrix.get(row, column), Some(expected));
            }
        }
        assert_eq!(compiler.current_instance_owner(), None);
        assert!(compiler.concrete_context.current.is_none());
        assert!(compiler.concrete_context.naturals.is_empty());
    }
}
