//! Regression checks for the finite adapter's original Nat evaluation.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::check::plans::{ResolvedStaticKind, StaticCallPlan};
use crate::frontend::check::{self, SourceLimits};
use std::cell::Cell;
use std::path::PathBuf;
use std::sync::Arc;

fn error(span: Span, code: ErrorCode, message: &'static str) -> CompileError {
    CompileError {
        code,
        path: PathBuf::from("<test>"),
        span,
        line: 1,
        column: 1,
        message: message.into(),
    }
}

fn calls(source: &str) -> Vec<StaticCallPlan> {
    let module = crate::frontend::parser::parse_module(source).unwrap();
    let program = check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap()
    .0;
    let target = program.resolution.qualified("main::keep").unwrap();
    program
        .static_calls
        .into_values()
        .filter(|call| call.target == target)
        .collect()
}

fn call(body: &str) -> StaticCallPlan {
    calls(&format!(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{{q}}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{{{body}}}"
    ))
    .remove(0)
}

fn formal(call: &StaticCallPlan) -> BinderKey {
    call.environment
        .naturals
        .keys()
        .find(|key| key.name == "n")
        .unwrap()
        .clone()
}

fn evaluate_actual(
    call: &StaticCallPlan,
    values: &BTreeMap<BinderKey, u32>,
) -> Result<NaturalValue, CompileError> {
    let mut charge = |_: Span, _: usize| Ok(());
    let mut helper_call = |_: Span| Ok(());
    match &call.arguments[0].value.kind {
        ResolvedStaticKind::Natural(original) => evaluate(
            original,
            &call.environment,
            values,
            &mut charge,
            &mut helper_call,
            &error,
        ),
        ResolvedStaticKind::Name(reference) => evaluate_reference(
            reference,
            call.arguments[0].value.span,
            &call.environment,
            values,
            &mut charge,
            &mut helper_call,
            &error,
        ),
        other => panic!("expected a retained natural actual: {other:?}"),
    }
}

#[test]
fn original_u32_intermediate_overflow_survives_normalized_cancellation_and_alias_cache() {
    let call = call("static let a=(n+4294967295)-4294967295;keep[a](q)");
    let n = formal(&call);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(n.clone(), 0)])).unwrap(),
        NaturalValue::Closed(0)
    );
    let alias = call
        .environment
        .local_naturals
        .keys()
        .next()
        .unwrap()
        .clone();
    // The supplied normalized alias value is not permission to skip its tree.
    let values = BTreeMap::from([(n, 1), (alias, 1)]);
    assert_eq!(
        evaluate_actual(&call, &values).unwrap_err().code,
        ErrorCode::Limit
    );
}

#[test]
fn zero_product_still_evaluates_its_original_overflowing_operand() {
    let call = call("keep[0*((3000000000+3000000000)-3000000000)](q)");
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap_err().code,
        ErrorCode::Limit
    );
}

#[test]
fn deferred_sibling_never_erases_an_independent_concrete_counterexample() {
    let overflowing = call("keep[n+((4294967295+1)-1)](q)");
    assert_eq!(
        evaluate_actual(&overflowing, &BTreeMap::new())
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
    let deferred = call("keep[0*n](q)");
    assert_eq!(
        evaluate_actual(&deferred, &BTreeMap::new()).unwrap(),
        NaturalValue::Deferred
    );
}

#[test]
fn original_helper_uses_signed_template_intermediates_and_ordered_arguments() {
    let call = calls(
        "static fn subtract[const a:Nat,const b:Nat]()->Nat requires a<=b {b-a}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f(q:Q<Bit>)->Q<Bit>{keep[subtract[3,5]()](q)}",
    )
    .remove(0);
    let ResolvedStaticKind::Natural(ResolvedNatural {
        kind: ResolvedNaturalKind::Helper { template, .. },
        ..
    }) = &call.arguments[0].value.kind
    else {
        panic!("helper template");
    };
    assert_eq!(template.result.terms.first_key_value().unwrap().1, &-1);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap(),
        NaturalValue::Closed(2)
    );

    let ordered = calls(
        "static fn pack[const a:Nat,const b:Nat]()->Nat{10*a+b}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[pack[n+1,n+2]()](q)}",
    )
    .remove(0);
    let values = BTreeMap::from([(formal(&ordered), 1)]);
    assert_eq!(
        evaluate_actual(&ordered, &values).unwrap(),
        NaturalValue::Closed(23)
    );
}

#[test]
fn helper_premise_is_rechecked_against_actual_original_arguments() {
    let call = calls(
        "static fn previous[const a:Nat]()->Nat requires a>=1 {a-1}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit> requires n>=1 {keep[previous[n]()](q)}",
    )
    .remove(0);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap(),
        NaturalValue::Deferred
    );
    let invalid = BTreeMap::from([(formal(&call), 0)]);
    assert_eq!(
        evaluate_actual(&call, &invalid).unwrap_err().code,
        ErrorCode::Contract
    );
    let valid = BTreeMap::from([(formal(&call), 1)]);
    assert_eq!(
        evaluate_actual(&call, &valid).unwrap(),
        NaturalValue::Closed(0)
    );
}

#[test]
fn deferred_helper_argument_keeps_a_constant_template_deferred() {
    let call = calls(
        "static fn zero[const a:Nat]()->Nat{a-a}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[zero[n]()](q)}",
    )
    .remove(0);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap(),
        NaturalValue::Deferred
    );
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(formal(&call), 7)])).unwrap(),
        NaturalValue::Closed(0)
    );
}

#[test]
fn an_earlier_deferred_helper_argument_keeps_a_later_concrete_overflow() {
    let call = calls(
        "static fn first[const a:Nat,const b:Nat]()->Nat{a}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[first[n,((4294967295+1)-1)]()](q)}",
    )
    .remove(0);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap_err().code,
        ErrorCode::Limit
    );
}

#[test]
fn helper_result_must_still_be_a_nonnegative_u32() {
    let call = calls(
        "static fn large[const a:Nat]()->Nat{a+4294967295}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[large[n]()](q)}",
    )
    .remove(0);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(formal(&call), 1)]))
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
}

#[test]
fn helper_i128_template_arithmetic_remains_checked() {
    let call = calls(
        "static fn huge[const a:Nat]()->Nat{170141183460469231731687303715884105727+a}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[huge[n]()](q)}",
    )
    .remove(0);
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(formal(&call), 1)]))
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
}

#[test]
fn deferred_helper_actual_does_not_hide_a_false_closed_premise() {
    let call = calls(
        "static fn first[const a:Nat,const b:Nat]()->Nat requires b>=1 {a}
         unitary fn keep[const p:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat,const m:Nat](q:Q<Bit>)->Q<Bit> requires m>=1 {keep[first[n,m]()](q)}",
    ).remove(0);
    let m = call
        .environment
        .naturals
        .keys()
        .find(|key| key.name == "m")
        .unwrap()
        .clone();
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(m, 0)]))
            .unwrap_err()
            .code,
        ErrorCode::Contract
    );
}

#[test]
fn malformed_original_helper_callee_is_an_error_instead_of_deferred() {
    let call = calls(
        "static fn zero[const a:Nat]()->Nat{a-a}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[zero[n]()](q)}",
    )
    .remove(0);
    let ResolvedStaticKind::Natural(original) = &call.arguments[0].value.kind else {
        panic!("helper");
    };
    let mut corrupted = original.clone();
    let ResolvedNaturalKind::Helper { callee, .. } = &mut corrupted.kind else {
        panic!("callee");
    };
    let key = formal(&call);
    callee.target = ResolvedUse::Local(key.id);
    callee.local = Some(key);
    assert_eq!(
        evaluate(
            &corrupted,
            &call.environment,
            &BTreeMap::new(),
            &mut |_, _| Ok(()),
            &mut |_| Ok(()),
            &error,
        )
        .unwrap_err()
        .code,
        ErrorCode::TypeMismatch
    );
}

#[test]
fn foreign_same_spelling_cannot_supply_an_original_formal() {
    let mut plans = calls(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[n](q)}
         unitary fn g[const n:Nat](q:Q<Bit>)->Q<Bit>{keep[n](q)}",
    );
    let other = plans.pop().unwrap();
    let original = plans.pop().unwrap();
    let foreign = formal(&other);
    assert_ne!(foreign, formal(&original));
    let values = BTreeMap::from([(foreign.clone(), 9)]);
    assert_eq!(
        evaluate_actual(&original, &values).unwrap(),
        NaturalValue::Deferred
    );
    let ResolvedStaticKind::Name(reference) = &original.arguments[0].value.kind else {
        panic!("name");
    };
    let mut corrupted = reference.clone();
    corrupted.target = ResolvedUse::Local(foreign.id);
    corrupted.local = Some(foreign);
    assert_eq!(
        evaluate_reference(
            &corrupted,
            original.arguments[0].value.span,
            &original.environment,
            &values,
            &mut |_, _| Ok(()),
            &mut |_| Ok(()),
            &error,
        )
        .unwrap_err()
        .code,
        ErrorCode::TypeMismatch
    );
}

#[test]
fn a_non_natural_category_is_an_error_instead_of_deferred() {
    let call = calls(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f[const A:Basis,const n:Nat](q:Q<Bit>)->Q<Bit>{keep[n](q)}",
    )
    .remove(0);
    let ResolvedStaticKind::Name(reference) = &call.arguments[0].value.kind else {
        panic!("name");
    };
    let mut corrupted = reference.clone();
    let basis = call.environment.bases.keys().next().unwrap().clone();
    corrupted.target = ResolvedUse::Local(basis.id);
    corrupted.local = Some(basis.clone());
    assert_eq!(
        evaluate_reference(
            &corrupted,
            call.arguments[0].value.span,
            &call.environment,
            &BTreeMap::from([(basis, 0)]),
            &mut |_, _| Ok(()),
            &mut |_| Ok(()),
            &error,
        )
        .unwrap_err()
        .code,
        ErrorCode::TypeMismatch
    );
}

#[test]
fn retained_alias_cycles_are_refused() {
    let mut call = call("static let a=n;static let b=a;keep[b](q)");
    let ResolvedStaticKind::Name(reference) = &call.arguments[0].value.kind else {
        panic!("name");
    };
    let b = reference.clone();
    let environment = Arc::make_mut(&mut call.environment);
    let a = environment
        .local_naturals
        .keys()
        .find(|key| key.name == "a")
        .unwrap()
        .clone();
    let NaturalBindingPlan::Initializer(initializer) = &environment.local_naturals[&a] else {
        panic!("initializer");
    };
    let mut cyclic = (**initializer).clone();
    cyclic.kind = ResolvedNaturalKind::Name(b);
    environment
        .local_naturals
        .insert(a, NaturalBindingPlan::Initializer(Arc::new(cyclic)));
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap_err().code,
        ErrorCode::RecursiveCall
    );
}

#[test]
fn fold_index_requires_a_real_value_within_original_bounds() {
    let call = calls(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f(q:Q<Bit>)->Q<Bit>{qfor static i in 2..4 carry r=q {yield keep[i](r);}}",
    )
    .remove(0);
    let ResolvedStaticKind::Name(reference) = &call.arguments[0].value.kind else {
        panic!("index");
    };
    let index = reference.local.clone().unwrap();
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::new()).unwrap(),
        NaturalValue::Deferred
    );
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(index.clone(), 3)])).unwrap(),
        NaturalValue::Closed(3)
    );
    assert_eq!(
        evaluate_actual(&call, &BTreeMap::from([(index, 4)]))
            .unwrap_err()
            .code,
        ErrorCode::Contract
    );
}

#[test]
fn helper_allocation_is_charged_before_any_actual_is_visited() {
    let call = calls(
        "static fn pack[const a:Nat,const b:Nat]()->Nat{a+b}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         unitary fn f(q:Q<Bit>)->Q<Bit>{keep[pack[2,3]()](q)}",
    )
    .remove(0);
    let ResolvedStaticKind::Natural(original) = &call.arguments[0].value.kind else {
        panic!("helper");
    };
    let called = Cell::new(false);
    let allocated = Cell::new(false);
    let mut charge = |span, amount| {
        if called.get() {
            assert_eq!(
                span, original.span,
                "actual visited before its allocation reservation"
            );
            assert_eq!(amount, 2);
            allocated.set(true);
            return Err(error(span, ErrorCode::Limit, "test allocation reservation"));
        }
        Ok(())
    };
    let mut helper_call = |_| {
        called.set(true);
        Ok(())
    };
    assert_eq!(
        evaluate(
            original,
            &call.environment,
            &BTreeMap::new(),
            &mut charge,
            &mut helper_call,
            &error,
        )
        .unwrap_err()
        .code,
        ErrorCode::Limit
    );
    assert!(called.get());
    assert!(allocated.get());
}

#[test]
fn finite_depth_limit_does_not_depend_on_the_selected_adapter_limit() {
    let call = call("keep[n+0](q)");
    let ResolvedStaticKind::Natural(original) = &call.arguments[0].value.kind else {
        panic!("natural");
    };
    let mut nested = original.clone();
    for _ in 0..MAX_DEPTH {
        nested = ResolvedNatural {
            node: original.node,
            span: original.span,
            kind: ResolvedNaturalKind::Add(
                Box::new(nested),
                Box::new(ResolvedNatural {
                    node: original.node,
                    span: original.span,
                    kind: ResolvedNaturalKind::Number(0),
                }),
            ),
        };
    }
    assert_eq!(
        evaluate(
            &nested,
            &call.environment,
            &BTreeMap::new(),
            &mut |_, _| Ok(()),
            &mut |_| Ok(()),
            &error,
        )
        .unwrap_err()
        .code,
        ErrorCode::Limit
    );
}
