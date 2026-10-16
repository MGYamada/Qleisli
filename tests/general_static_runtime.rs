//! Small ordinary-source static instances, without selected-profile routing.
//! These conformance checks are distinct from a general preservation theorem.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::RawOp;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn outcomes(source: &str) -> BTreeMap<Vec<bool>, f64> {
    let accepted = compile_project(&SourceRoot::new(source).0).unwrap();
    run_closed(&accepted, SimulationLimits::default()).unwrap()
}

// Simulation is a numerical regression oracle. Exact phase/coefficients are
// checked separately by the native matrix tests in derived_gate_source.
fn assert_outcomes(source: &str, expected: BTreeMap<Vec<bool>, f64>) {
    let actual = outcomes(source);
    assert_distribution(&actual, &expected);
}

fn assert_distribution(actual: &BTreeMap<Vec<bool>, f64>, expected: &BTreeMap<Vec<bool>, f64>) {
    for label in actual.keys().chain(expected.keys()) {
        let got = actual.get(label).copied().unwrap_or(0.0);
        let want = expected.get(label).copied().unwrap_or(0.0);
        assert!(
            (got - want).abs() < 1e-12,
            "{label:?}: {got}, expected {want}; {actual:?}"
        );
    }
    assert!((actual.values().sum::<f64>() - 1.0).abs() < 1e-12);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn bound_local_operation_keeps_apply_adjoint_power_and_coherent_control() {
    let source = "use std::quantum::{t,h,x,init0};use std::observe::measure_z;
        unitary fn eighth(q:Q<Bit>)->Q<Bit>{t(q)}
        unitary fn transform[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
        requires Applicable(U),Adjointable(U),Controllable(U) {
            let q=U(q);let q=adjoint(U)(q);let q=power(U,2)(q);
            controlled(U)(c,q)
        }
        pub observe fn main()->(Bit,Bit){
            let(c,q)=transform[eighth](h(init0()),x(init0()));
            (measure_z(h(c)),measure_z(q))
        }";
    let high = (2.0 + std::f64::consts::SQRT_2) / 4.0;
    assert_outcomes(
        source,
        BTreeMap::from([(vec![false, true], high), (vec![true, true], 1.0 - high)]),
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_basis_instances_keep_unit_empty_register_bit_and_word_distinct() {
    let declarations = "use std::quantum::{unit,finish,init0};
        use std::registers::{empty,consume_empty,put_bit,take_bit};use std::observe::measure_z;
        unitary fn identity[const A:Basis](q:Q<A>)->Q<A>{q}";
    let source = format!(
        "{declarations}
        pub observe fn main()->(Bit,Bit){{
          finish(identity[type(Unit)](unit(())));
          consume_empty(identity[type(Bits<0>)](empty()));
          let bit=identity[type(Bit)](init0());
          let word=identity[type(Bits<1>)](put_bit[1,0](init0(),empty()));
          let(other,z)=take_bit[1,0](word);consume_empty(z);
          (measure_z(bit),measure_z(other))
        }}"
    );
    assert_outcomes(&source, BTreeMap::from([(vec![false, false], 1.0)]));
    for wrong in [
        "finish(identity[type(Bits<0>)](unit(())))",
        "finish(identity[type(Unit)](empty()))",
    ] {
        let source = format!("{declarations}pub unitary fn main()->Unit{{{wrong}}}");
        assert!(check_project(&SourceRoot::new(&source).0).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn static_fold_initializes_once_and_uses_original_index_in_selected_arm() {
    for count in [0, 1, 2] {
        let source = format!(
            "use std::quantum::{{init0,x}};use std::observe::measure_z;
          unitary fn run[const n:Nat](q:Q<Bit>)->Q<Bit>{{
            qfor static i in 0..n carry q=q {{
              let q=if static i==0 {{x(q)}} else {{q}};yield q;
            }}
          }}
          pub observe fn main()->Bit{{measure_z(run[{count}](init0()))}}"
        );
        let accepted = compile_project(&SourceRoot::new(&source).0).unwrap();
        assert_eq!(
            accepted
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op, RawOp::Init0 { .. }))
                .count(),
            1
        );
        assert_distribution(
            &run_closed(&accepted, SimulationLimits::default()).unwrap(),
            &BTreeMap::from([(vec![count != 0], 1.0)]),
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn generic_provider_forwarding_keeps_distinct_nat_instances() {
    let source = "use std::quantum::{init0,x};use std::observe::measure_z;
      unitary fn flip[const n:Nat](q:Q<Bit>)->Q<Bit>{
        qfor static i in 0..n carry q=q {yield x(q);}
      }
      unitary fn apply[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){V(q)}
      unitary fn forward[const n:Nat](q:Q<Bit>)->Q<Bit>{apply[flip[n]](q)}
      pub observe fn main()->(Bit,Bit){
        (measure_z(forward[1](init0())),measure_z(forward[2](init0())))
      }";
    assert_outcomes(source, BTreeMap::from([(vec![true, false], 1.0)]));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_register_repartition_preserves_axis_order_and_reference_correlations() {
    let source = "use std::quantum::{init0,h,x,cnot};use std::observe::measure_z;
      use std::registers::{empty,consume_empty,take_bit,put_bit};
      pub observe fn main()->(Bit,Bit,Bit){
        let(a,r)=cnot(h(init0()),init0());
        let q=put_bit[1,0](a,empty());let q=put_bit[2,1](x(init0()),q);
        let(b,q)=take_bit[2,1](q);let q=put_bit[2,0](b,q);
        let(first,q)=take_bit[2,0](q);let(second,z)=take_bit[1,0](q);consume_empty(z);
        (measure_z(first),measure_z(second),measure_z(r))
      }";
    let actual = outcomes(source);
    let expected = BTreeMap::from([
        (vec![true, false, false], 0.5),
        (vec![true, true, true], 0.5),
    ]);
    assert_distribution(&actual, &expected);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn closed_words_keep_order_and_small_unrepresentable_phase_refuses() {
    let source = "use std::classical::{empty_bits,prepend_bit};
      pub unitary fn main()->Bits<2>{prepend_bit[1](0,prepend_bit[0](1,empty_bits()))}";
    // The outer bit is prepended at the lowest axis: 0 before the existing 1.
    assert_outcomes(source, BTreeMap::from([(vec![false, true], 1.0)]));
    let source = "use std::quantum::{init0,h,phase};use std::observe::measure_z;
      pub observe fn main()->Bit{measure_z(h(phase[1,4](h(init0()))))}";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Unsupported, "{failure}");
    assert!(failure.message.contains("exact multiple"), "{failure}");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_static_region_defers_formal_arithmetic_but_not_closed_counterexamples() {
    let source = "use std::quantum::{init0,x};use std::observe::measure_z;
      unitary fn flip[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry q=q{yield x(q);}}
      unitary fn apply[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){V(q)}
      unitary fn run[const n:Nat](q:Q<Bit>)->Q<Bit>{
        if static n>=1 {apply[flip[n-1]](q)} else {q}
      }
      pub observe fn main()->(Bit,Bit){(measure_z(run[0](init0())),measure_z(run[2](init0())))}";
    assert_outcomes(source, BTreeMap::from([(vec![false, true], 1.0)]));

    for body in [
        "if static 0==1 {x(ctrl q);q} else {q}",
        "qfor static i in 0..0 carry q=q{x(ctrl q);yield q;}",
    ] {
        let source = format!("use std::quantum::x;pub unitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
        let failure = check_project(&SourceRoot::new(&source).0).unwrap_err();
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
fn original_local_owner_and_partial_nat_actual_cannot_hide_closed_refusals() {
    let source = "use std::quantum::x;
      unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){
        let alias=q;x(ctrl alias);U(alias)
      }";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
    assert_eq!(
        &source[failure.span.start..failure.span.end],
        "x(ctrl alias)"
    );

    let source="use std::quantum::x;
      classical fn identity(b:Bit)->Bit{b}
      meaning Identity:Bit=permutation_by(identity);
      unitary fn bad(q:Q<Bit>)->Q<Bit>{x(q)}
      unitary fn demand[const n:Nat,const V:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit> requires Applicable(V){V(q)}
      unitary fn unused[const n:Nat](q:Q<Bit>)->Q<Bit>{demand[n,bad](q)}";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn classical_static_headers_keep_their_existing_source_contract() {
    let source = "use std::classical::{empty_bits,prepend_bit};
      classical fn identity[const A:Basis](a:A)->A{a}
      pub unitary fn main()->Bits<1>{identity[type(Bits<1>)](prepend_bit[0](1,empty_bits()))}";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Project, "{failure}");
    assert!(
        failure.message.contains("classical functions cannot"),
        "{failure}"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn inactive_closed_self_call_does_not_reenter_its_already_active_instance() {
    let source = "use std::quantum::init0;use std::observe::measure_z;
      unitary fn stop[const n:Nat](q:Q<Bit>)->Q<Bit>{
        if static n>=1 {stop[0](q)} else {q}
      }
      pub observe fn main()->(Bit,Bit){(measure_z(stop[0](init0())),measure_z(stop[1](init0())))}";
    assert_outcomes(source, BTreeMap::from([(vec![false, false], 1.0)]));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn specialized_direct_transforms_preserve_groups_axis_order_phase_and_zero_width_owners() {
    let declarations = "use std::quantum::{init0,x,t,unit,finish};use std::observe::measure_z;
      unitary fn action[const n:Nat](a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){
        let a=qfor static i in 0..n carry a=a{yield x(a);};(a,b)
      }
      unitary fn with_unit[const n:Nat](q:Q<Bit>,u:Q<Unit>)->(Q<Bit>,Q<Unit>){
        let q=qfor static i in 0..n carry q=q{yield x(q);};(q,u)
      }";
    for transform in [
        "power(action[1],2)",
        "adjoint(action[1])",
        "power(action[1],0)",
    ] {
        let source = format!(
            "{declarations}pub observe fn main()->(Bit,Bit){{
          let(a,b)={transform}((init0(),x(init0())));(measure_z(a),measure_z(b))}}"
        );
        let expected = transform == "adjoint(action[1])";
        assert_outcomes(&source, BTreeMap::from([(vec![expected, true], 1.0)]));
    }
    let source = format!(
        "{declarations}pub observe fn main()->(Bit,Bit,Bit){{
      let(c,(a,b))=controlled(action[1])(x(init0()),(init0(),x(init0())));
      (measure_z(c),measure_z(a),measure_z(b))}}"
    );
    assert_outcomes(&source, BTreeMap::from([(vec![true, true, true], 1.0)]));
    let source = format!(
        "{declarations}pub observe fn main()->Bit{{
      let(q,u)=adjoint(with_unit[1])((init0(),unit(())));finish(u);measure_z(q)}}"
    );
    assert_outcomes(&source, BTreeMap::from([(vec![true], 1.0)]));

    let source =
        "use std::quantum::{init0,h,tdg,phase_eighth,unit,finish};use std::observe::measure_z;
      unitary fn scalar(u:Q<Unit>)->Q<Unit>{phase_eighth(u)}
      unitary fn scalar_group[const n:Nat](q:Q<Bit>,u:Q<Unit>)->(Q<Bit>,Q<Unit>){
        let u=power(scalar,n)(u);(q,u)
      }
      pub observe fn main()->(Bit,Bit){
        let(c,(q,u))=controlled(scalar_group[1])(h(init0()),(init0(),unit(())));
        finish(u);(measure_z(h(tdg(c))),measure_z(q))
      }";
    assert_outcomes(source, BTreeMap::from([(vec![false, false], 1.0)]));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn direct_symbolic_counts_and_specialized_adjoint_retain_exact_phase() {
    let source = "use std::quantum::{init0,h,t};use std::observe::measure_z;
      unitary fn flip(q:Q<Bit>)->Q<Bit>{h(power(t,4)(h(q)))}
      unitary fn run[const n:Nat](q:Q<Bit>)->Q<Bit>{power(flip,n)(q)}
      unitary fn eighth(q:Q<Bit>)->Q<Bit>{t(q)}
      unitary fn phase[const n:Nat](q:Q<Bit>)->Q<Bit>{power(eighth,n)(q)}
      pub observe fn main()->(Bit,Bit){
        (measure_z(run[2](init0())),measure_z(h(adjoint(phase[1])(t(h(init0()))))))
      }";
    assert_outcomes(source, BTreeMap::from([(vec![false, false], 1.0)]));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn concrete_fold_index_calls_recheck_bound_ctrl_inside_their_empty_callee_fold() {
    let source="use std::quantum::x;use std::registers::{take_bit,put_bit};
      unitary fn flip_word(q:Q<Bits<1>>)->Q<Bits<1>>{
        let(b,z)=take_bit[1,0](q);put_bit[1,0](x(b),z)
      }
      unitary fn empty[const n:Nat,const U:Op<Bits<n>>](q:Q<Bits<n>>)->Q<Bits<n>> requires Applicable(U){
        qfor static j in 0..0 carry q=q{U(ctrl q);yield q;}
      }
      pub unitary fn outer(q:Q<Bits<1>>)->Q<Bits<1>>{
        qfor static i in 1..2 carry q=q{yield empty[i,flip_word](q);}
      }";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Contract, "{failure}");
    assert_eq!(&source[failure.span.start..failure.span.end], "U(ctrl q)");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn outer_zero_repetition_does_not_hide_an_invalid_inner_count() {
    let source = "unitary fn target[const n:Nat](q:Q<Bit>)->Q<Bit>{q}
      unitary fn unused[const n:Nat](q:Q<Bit>)->Q<Bit>{power(power(target[1],4097),0)(q)}";
    let failure = check_project(&SourceRoot::new(source).0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Limit, "{failure}");
    assert_eq!(&source[failure.span.start..failure.span.end], "4097");
}
