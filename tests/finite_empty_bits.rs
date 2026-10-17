//! Exact zero-register types through the ordinary finite compiler.
//! Native acceptance and requested finite equations do not prove source preservation.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{
    ErrorCode, check_project, check_project_report_with_kernel, compile_project,
    compile_project_with_kernel,
};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::{Effect, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};

fn report(source: &str) -> qleisli::frontend::compile::ProjectCheckReport {
    let root = SourceRoot::new(source);
    check_project_report_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"))
}

fn nested_equation_decisions(source: &str) {
    let checked = report(source);
    assert!(checked.native_decisions().complete());
    assert_eq!(checked.entry_request_checked(), Some(false));
    // FunctionEvidence is a reachable dependency of an ordinarily checked
    // QIRF root. Its fresh native equation check has no separate root request.
    // Counts alone do not prove that equation; the phase/type faults below
    // exercise its actual independent rejection boundary.
    assert_eq!(checked.native_decisions().requests_checked(), 0);
    assert!(
        checked.native_decisions().decisions()
            > checked.concrete_local_roots() + checked.concrete_bundled_roots()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn unused_closed_empty_register_root_is_checked_without_polluting_a_bit_client() {
    let baseline = report("fn main()->Bit{1}");
    let extra = report(
        "pub unitary fn identity(q:Q<Bits<0>>)->Q<Bits<0>>{q}
         fn main()->Bit{1}",
    );
    assert_eq!(
        extra.concrete_local_roots(),
        baseline.concrete_local_roots() + 1
    );
    assert_eq!(
        extra.concrete_bundled_roots(),
        baseline.concrete_bundled_roots()
    );
    assert!(extra.concrete_bundled_roots() > 0);
    assert!(extra.native_decisions().complete());
    assert!(extra.native_decisions().decisions() > baseline.native_decisions().decisions());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn ordinary_empty_register_constructor_classical_calls_and_branch_results_keep_their_type() {
    let source = "
        classical fn empty_label()->Bits<0>{empty_bits()}
        unitary fn choose(c:Bit,x:Bits<0>)->Bits<0>{if c{x}else{empty_label()}}
        fn main()->(Bits<0>,Unit,Bit){(choose(1,empty_label()),(),1)}";
    let root = SourceRoot::new(source);
    let accepted = compile_project(&root.0).unwrap_or_else(|error| panic!("{error}"));
    assert!(accepted.raw().quantum_inputs.is_empty());
    assert!(accepted.raw().quantum_outputs.is_empty());
    assert_eq!(accepted.raw().classical_outputs.len(), 1);
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 1);
    assert_eq!(distribution[&vec![true]], 1.0);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn normalized_zero_sizes_and_closed_static_helpers_remain_exact_empty_registers() {
    let checked = report(
        "static fn zero()->Nat{2-2}
         pub unitary fn arithmetic(q:Q<Bits<2-2>>)->Q<Bits<0>>{q}
         pub unitary fn helper(q:Q<Bits<zero()>>)->Q<Bits<0>>{q}
         fn main()->Unit{()}",
    );
    assert_eq!(checked.concrete_local_roots(), 3);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn exact_empty_basis_meaning_and_phase_fault_use_the_actual_native_contract() {
    let prefix = "
        classical fn phase_labels(x:Bits<0>)->(Bit,(Bit,Bit)){(1,(0,0))}
        meaning Scalar:Bits<0> = phase_by(phase_labels);";
    let suffix = "unitary fn audited(q:Q<Bits<0>>)->Q<Bits<0>>{
            apply_contract(implementation,Scalar,q)
        }
        fn main()->Unit{()}";
    let correct = format!(
        "{prefix}
        unitary fn implementation(q:Q<Bits<0>>)->Q<Bits<0>>{{global_phase_eighth(q)}}
        {suffix}"
    );
    nested_equation_decisions(&correct);
    let erased = format!(
        "{prefix}
        unitary fn implementation(q:Q<Bits<0>>)->Q<Bits<0>>{{q}}
        {suffix}"
    );
    let root = SourceRoot::new(&erased);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Contract, "{error}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn empty_register_operation_formal_checks_its_actual_provider_and_exact_ports() {
    let source = "unitary fn identity(q:Q<Bits<0>>)->Q<Bits<0>>{q}
        unitary fn apply[const U:Op<Bits<0>>](q:Q<Bits<0>>)->Q<Bits<0>>
          requires Applicable(U){U(q)}
        unitary fn audited(q:Q<Bits<0>>)->Q<Bits<0>>{apply[identity](q)}
        fn main()->Unit{()}";
    nested_equation_decisions(source);
    let wrong = source.replace(
        "unitary fn identity(q:Q<Bits<0>>)->Q<Bits<0>>{q}",
        "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}",
    );
    let root = SourceRoot::new(&wrong);
    assert_eq!(
        check_project(&root.0).unwrap_err().code,
        ErrorCode::TypeMismatch
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn exact_zero_register_product_meaning_keeps_unit_nodes_and_axis_order() {
    nested_equation_decisions(
        "classical fn labels(x:(Bits<0>,(Bit,Unit)))->(Bits<0>,(Bit,Unit)){x}
         meaning Identity:(Bits<0>,(Bit,Unit))=permutation_by(labels);
         unitary fn identity(q:Q<(Bits<0>,(Bit,Unit))>)->Q<(Bits<0>,(Bit,Unit))>{q}
         unitary fn audited(q:Q<(Bits<0>,(Bit,Unit))>)->Q<(Bits<0>,(Bit,Unit))>{
             apply_contract(identity,Identity,q)
         }
         fn main()->Unit{()}",
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn zero_width_quantum_branch_phi_retains_an_owner_through_explicit_basis_maps() {
    let source = "
        
        unitary fn choose(c:Bit,q:Q<Bits<0>>)->Q<Bits<0>>{
            if c{global_phase_eighth(q)}else{q}
        }
        fn main()->Unit{
            let q=basis unit(()) as () {empty_bits()};
            let q=choose(1,q);
            finish(basis q as _ {()})
        }";
    let root = SourceRoot::new(source);
    let accepted = compile_project(&root.0).unwrap_or_else(|error| panic!("{error}"));
    let phis = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::ClassicalBranch { quantum_phis, .. } => Some(quantum_phis),
            _ => None,
        })
        .expect("the original runtime branch remains present");
    assert_eq!(phis.len(), 1);
    assert!(phis[0].output_wires.is_empty());
    assert_ne!(phis[0].output, phis[0].then_token);
    assert_ne!(phis[0].output, phis[0].else_token);
    assert_eq!(accepted.raw().declared_effect, Effect::Unitary);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn controlled_empty_register_scalar_preserves_the_exact_relative_phase() {
    let source = "
        
        classical fn labels(q:Bit)->(Bit,(Bit,Bit)){(q,(0,0))}
        meaning T:Bit=phase_by(labels);
        unitary fn scalar(q:Q<Bits<0>>)->Q<Bits<0>>{global_phase_eighth(q)}
        unitary fn gate(q:Q<Bit>)->Q<Bit>{
            let e=basis unit(()) as () {empty_bits()};
            let (q,e)=controlled(scalar)(q,e);
            finish(basis e as _ {()});
            q
        }
        unitary fn audited(q:Q<Bit>)->Q<Bit>{apply_contract(gate,T,q)}
        fn main()->Unit{()}";
    nested_equation_decisions(source);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn observing_empty_register_result_reaches_the_complete_instrument_schema() {
    let source = "
        
        
        observe fn actual(q:Q<Bits<0>>)->Bits<0>{discard(q);empty_bits()}
        observe fn reference(q:Q<Bits<0>>)->Bits<0>{discard(q);empty_bits()}
        observe fn main()->Bits<0>{
            let q=basis unit(()) as () {empty_bits()};
            apply_contract(actual,reference,q)
        }";
    let checked = report(source);
    assert!(checked.native_decisions().requests_checked() >= 2);
}

#[test]
fn zero_width_does_not_allow_type_coercions_owner_loss_or_duplicate_owners() {
    for (source, expected) in [
        (
            "
          unitary fn bad(q:Q<Bits<0>>)->Unit{finish(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn bad(q:Q<(Bits<0>,Bit)>)->Q<(Unit,Bit)>{q}",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn bad(q:Q<Bits<0>>)->Unit{()}",
            ErrorCode::Ownership,
        ),
        (
            "unitary fn bad(q:Q<Bits<0>>)->(Q<Bits<0>>,Q<Bits<0>>){(q,q)}",
            ErrorCode::Ownership,
        ),
        (
            "
          fn bad()->Bits<0>{empty_bits(())}",
            ErrorCode::Arity,
        ),
        (
            "
          classical fn bad()->Bits<0>{empty_bits(())}",
            ErrorCode::Arity,
        ),
    ] {
        let root = SourceRoot::new(source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, expected, "{error}\n{source}");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn nonzero_and_generic_register_declarations_reach_finite_checking() {
    // Uninstantiated generic bodies remain conditional common-checked families;
    // these declaration-only sources execute no selected concrete instance.
    for source in [
        "pub unitary fn f(q:Q<Bits<1>>)->Q<Bits<1>>{q}",
        "pub unitary fn f(q:Q<Bits<0+1>>)->Q<Bits<1>>{q}",
        "pub unitary fn f[const n:Nat](q:Q<Bits<n-n>>)->Q<Bits<0>>{q}",
        "pub unitary fn f[const A:Basis](q:Q<A>)->Q<A>{q}",
    ] {
        let root = SourceRoot::new(source);
        check_project(&root.0).unwrap_or_else(|error| panic!("{error}\n{source}"));
    }
}

#[test]
fn missing_native_checker_cannot_accept_a_newly_eligible_empty_register_root() {
    let root =
        SourceRoot::new("pub unitary fn identity(q:Q<Bits<0>>)->Q<Bits<0>>{q} fn main()->Unit{()}");
    let kernel = Kernel::new(root.0.join("absent-native-checker"));
    let error = compile_project_with_kernel(&root.0, SourcePolicy::Legacy, &kernel).unwrap_err();
    assert_eq!(error.code, "project", "{error:?}");
}
