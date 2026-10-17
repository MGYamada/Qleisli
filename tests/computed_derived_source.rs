//! Exact native equations for ordinary source in a protected computed body.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::frontend::compile::{ErrorCode, compile_project};
use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
use qleisli::interchange::native::Proposal;
use qleisli::interchange::{RootInterface, Version};
use qleisli::ir::{CircuitAction, ProtectedUse, QuantumPort, RawOp, RawProgram, SingleGate};

fn phase_matrix(phases: &[u8]) -> Matrix {
    let dimension = phases.len();
    Matrix::new(
        dimension,
        dimension,
        (0..dimension * dimension)
            .map(|index| {
                if index / dimension == index % dimension {
                    Exact::phase(i32::from(phases[index / dimension]))
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap()
}

fn probe(source: &str) -> (qleisli::interchange::native::AcceptedProgram, RawProgram) {
    let accepted = compile_project(&SourceRoot::new(source).0).unwrap();
    let actual = accepted
        .raw()
        .operations
        .iter()
        .find_map(|operation| {
            let RawOp::ApplyUnitary { steps, .. } = operation else {
                return None;
            };
            steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. }
                    if evidence.identity().implementation == "main::probe" =>
                {
                    Some(evidence.implementation().clone())
                }
                _ => None,
            })
        })
        .expect("actual ordinary probe body");
    (accepted, actual)
}

fn request(actual: &RawProgram, basis: BasisType, expected: &Matrix) {
    let [input] = actual.quantum_inputs.as_slice() else {
        panic!("single exact owner");
    };
    let [output] = actual.quantum_outputs.as_slice() else {
        panic!("single exact owner");
    };
    let boundary = UnitaryBoundary::new(
        basis.clone(),
        input.clone(),
        QuantumPort {
            token: *output,
            wires: input.wires.clone(),
            shape: input.shape,
        },
    )
    .unwrap();
    let proposal = Proposal::from_raw(
        actual,
        Some(&RootInterface {
            input: basis.clone(),
            output: basis,
        }),
        Version::V2,
        None,
    )
    .unwrap();
    check_unitary(
        proposal.artifact(),
        &boundary,
        expected,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
}

fn source(body: &str, wrapper: &str) -> String {
    format!(
        "use std::gate::{{z,t}};
        use std::state::init0;
        classical fn predicate(b:Bit)->Bit{{b}}
        {wrapper}
        unitary fn probe(q:Q<Bit>)->Q<Bit>{{with_computed(q,predicate){{|a|{body}}}}}
        pub observe fn main()->Bit{{measure_z(apply_contract(probe,probe,init0()))}}"
    )
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_z_t_and_unrelated_wrappers_use_native_normalization() {
    for (body, wrapper, phase, gate) in [
        ("z(a)", "", 4, SingleGate::Z),
        ("t(a)", "", 1, SingleGate::T),
        (
            "turnstile(a)",
            "unitary fn turnstile(q:Q<Bit>)->Q<Bit>{t(q)}",
            1,
            SingleGate::T,
        ),
    ] {
        let text = source(body, wrapper);
        let (accepted, actual) = probe(&text);
        request(&actual, BasisType::Bit, &phase_matrix(&[0, phase]));
        let receipts: Vec<_> = accepted
            .source_computed_normalizations()
            .iter()
            .filter(|receipt| receipt.names().0.contains("main::probe::with_computed["))
            .collect();
        assert!(!receipts.is_empty());
        for receipt in receipts {
            assert!(
                receipt
                    .sources()
                    .iter()
                    .any(|(module, bytes)| module == "main" && bytes == &text)
            );
            assert!(
                receipt
                    .sources()
                    .iter()
                    .any(|(module, bytes)| module == "std::gate"
                        && bytes == include_str!("../stdlib/src/gate.qli"))
            );
            request(
                receipt.implementation().program().raw(),
                BasisType::Bit,
                &phase_matrix(&[0, phase]),
            );
            request(
                receipt.specification().program().raw(),
                BasisType::Bit,
                &phase_matrix(&[0, phase]),
            );
        }
        let RawOp::ComputeUseUncompute {
            use_ops,
            ancilla_wires,
            ..
        } = &actual.operations[0]
        else {
            panic!("one existing protected compute representation");
        };
        assert_eq!(ancilla_wires.len(), 1);
        assert!(use_ops.iter().any(|operation| matches!(operation,
            ProtectedUse::ProtectedGate { gate: actual_gate, .. } if *actual_gate == gate)));
        // Canonical T is an actual nonempty operation; the optimization receipt
        // preserves the proposed derived body separately from realized work.
        assert!(!use_ops.is_empty());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn scalar_on_the_zero_predicate_is_preserved_on_unit_data() {
    let text = "use std::gate::z;
        classical fn zero(u:Unit)->Bit{0}
        unitary fn probe(q:Q<Unit>)->Q<Unit>{
            with_computed(q,zero){|a|global_phase_eighth(z(a))}}
        pub unitary fn main()->Unit{finish(apply_contract(probe,probe,unit(())))}";
    let (accepted, actual) = probe(text);
    request(&actual, BasisType::Unit, &phase_matrix(&[1]));
    let receipt = accepted
        .source_computed_normalizations()
        .iter()
        .find(|receipt| receipt.names().0.contains("main::probe::with_computed["))
        .unwrap();
    request(
        receipt.implementation().program().raw(),
        BasisType::Bit,
        &phase_matrix(&[1, 5]),
    );
    let RawOp::ComputeUseUncompute { use_ops, .. } = &actual.operations[0] else {
        unreachable!();
    };
    assert!(use_ops.iter().any(|usage| matches!(usage,
        ProtectedUse::ControlledPhase { controls, .. } if controls.is_empty())));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn non_diagonal_and_false_meaning_and_outer_reference_are_refused() {
    let non_diagonal = source("h(a)", "");
    let error = compile_project(&SourceRoot::new(&non_diagonal).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(error.message.contains("diagonal"));
    assert!(
        error
            .message
            .contains("with_computed(source, predicate, logical)")
    );
    assert!(error.message.contains("return both owners"));
    assert!(error.message.contains("does not bypass cleanup checking"));
    let false_meaning = "use std::gate::z;use std::state::init0;
        
        classical fn keep(b:Bit)->Bit{b} classical fn zero(b:Bit)->Bit{0}
        meaning Identity:Bit=permutation_by(keep);
        unitary fn wrong(q:Q<Bit>)->Q<Bit>{with_computed(q,zero){|a|global_phase_eighth(z(a))}}
        unitary fn demand[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub observe fn main()->Bit{measure_z(demand[wrong](init0()))}";
    let error = compile_project(&SourceRoot::new(false_meaning).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Contract);
    let hidden_reference = "
        classical fn zero(u:Unit)->Bit{0}
        pub unitary fn subject(q:Q<Unit>,r:Q<Bit>)->(Q<Unit>,Q<Bit>){
            let q=with_computed(q,zero){|a|let r=h(r);a};(q,r)}";
    let error = compile_project(&SourceRoot::new(hidden_reference).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Ownership);
    assert!(error.message.contains("capture"));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn normalized_scalar_survives_named_power_adjoint_and_coherent_control() {
    for (body, phase) in [("power(scalar,2)(q)", 2), ("adjoint(scalar)(q)", 7)] {
        let text = format!(
            "use std::state::init0;
            classical fn zero(b:Bit)->Bit{{0}}
            unitary fn scalar(q:Q<Bit>)->Q<Bit>{{with_computed(q,zero){{|a|global_phase_eighth(a)}}}}
            unitary fn probe(q:Q<Bit>)->Q<Bit>{{{body}}}
            pub observe fn main()->Bit{{measure_z(apply_contract(probe,probe,init0()))}}"
        );
        let (_, actual) = probe(&text);
        request(&actual, BasisType::Bit, &phase_matrix(&[phase, phase]));
    }
    // Unit data plus one coherent control and one computed ancilla is two
    // physical qubits. The scalar becomes a relative phase on that control.
    let text = "use std::state::init0;
        classical fn zero(u:Unit)->Bit{0}
        unitary fn scalar(q:Q<Unit>)->Q<Unit>{with_computed(q,zero){|a|global_phase_eighth(a)}}
        unitary fn probe(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{
            let(c,u)=split(q);let(c,u)=controlled(scalar)(c,u);join(c,u)}
        pub observe fn main()->Bit{let(c,u)=split(apply_contract(probe,probe,join(init0(),unit(()))));
            finish(u);measure_z(c)}";
    let (_, actual) = probe(text);
    request(
        &actual,
        BasisType::pair(BasisType::Bit, BasisType::Unit),
        &phase_matrix(&[0, 1]),
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn existing_canonical_t_chain_keeps_its_raw_length_profile() {
    // 1025 is above the separate function-equation step cap, far below the
    // ordinary source work bound. This is two physical qubits, no dense request.
    let text = format!("use std::gate::t; use std::state::init0;
        classical fn predicate(b:Bit)->Bit{{b}}
        pub observe fn main()->Bit{{let q=with_computed(init0(),predicate){{|a|{}a}};measure_z(q)}}",
        "let a=t(a);".repeat(1025));
    let accepted = compile_project(&SourceRoot::new(&text).0).unwrap();
    let uses = accepted
        .raw()
        .operations
        .iter()
        .find_map(|operation| {
            let RawOp::ComputeUseUncompute { use_ops, .. } = operation else {
                return None;
            };
            Some(use_ops)
        })
        .unwrap();
    assert_eq!(uses.len(), 1025);
    assert!(uses.iter().all(|usage| matches!(
        usage,
        ProtectedUse::ProtectedGate {
            gate: SingleGate::T,
            ..
        }
    )));
    assert!(accepted.source_computed_normalizations().is_empty());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn compact_205_ordinary_t_actions_bind_complete_body_to_exact_emitted_use() {
    // Each ordinary T expands to five Raw operations: 205 reaches 1025, above
    // the separate FunctionEvidence root preflight. The original compact 257
    // experiment and its later eager-stdlib source-work refusal are retained;
    // neither that nor the expanded 257/1025 work limits is claimed repaired.
    // There are only two physical qubits in this source program.
    let text = "use std::gate::t;use std::state::init0;
        classical fn predicate(b:Bit)->Bit{b}
        pub observe fn main()->Bit{
            let q=with_computed(init0(),predicate){|a|
                qfor static i in 0..205 carry r=a {yield t(r);}
            };measure_z(q)}";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let receipt = accepted
        .source_computed_normalizations()
        .iter()
        .find(|receipt| receipt.names().0.contains("main::main::with_computed["))
        .expect("inert whole-original normalization receipt");
    let actual = receipt.implementation();
    let canonical = receipt.specification();
    assert!(actual.program().raw().operations.len() > qleisli::contract::MAX_CONTRACT_STEPS);
    assert_eq!(actual.meaning(), &phase_matrix(&[0, 5]));
    assert_eq!(canonical.meaning(), actual.meaning());
    assert!(
        receipt
            .sources()
            .iter()
            .any(|(module, bytes)| module == "main" && bytes == text)
    );
    assert!(
        receipt
            .sources()
            .iter()
            .any(|(module, bytes)| module == "std::gate"
                && bytes == include_str!("../stdlib/src/gate.qli"))
    );
    let RawOp::ComputeUseUncompute {
        use_ops: emitted, ..
    } = accepted
        .raw()
        .operations
        .iter()
        .find(|operation| matches!(operation, RawOp::ComputeUseUncompute { .. }))
        .unwrap()
    else {
        unreachable!()
    };
    let canonical_raw = canonical.program().raw();
    let [
        RawOp::ComputeUseUncompute {
            source,
            source_out,
            ancilla_wires,
            function,
            use_ops: witnessed,
            ..
        },
    ] = canonical_raw.operations.as_slice()
    else {
        panic!("exact protected canonical witness")
    };
    assert_eq!(witnessed, emitted);
    assert_eq!(function, &[0, 1]);
    assert_ne!(source, source_out);
    assert_eq!(ancilla_wires.len(), 1);
    assert_ne!(canonical_raw.quantum_inputs[0].wires[0], ancilla_wires[0]);
    assert!(emitted.iter().any(|usage| matches!(
        usage,
        ProtectedUse::ProtectedGate {
            gate: SingleGate::T,
            ..
        }
    )));
    // Independent requests exercise the complete retained bytes, not only the
    // producer's matrix proposal or source/receipt strings.
    for leaf in [actual, canonical] {
        check_unitary(
            leaf.payload(),
            leaf.boundary(),
            &phase_matrix(&[0, 5]),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        assert!(
            check_unitary(
                leaf.payload(),
                leaf.boundary(),
                &phase_matrix(&[0, 0]),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
        );
        assert!(
            check_unitary(
                leaf.payload(),
                leaf.boundary(),
                &phase_matrix(&[4, 1]),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn consecutive_proposal_chunks_compose_in_source_order() {
    // The first 1024 flattened actions mean H*T^5, and the final [H,T]
    // mean T*H. Their source composition is T^6; reversing the two chunks
    // would instead be the non-diagonal H*T^6*H. Full original bytes still
    // require a fresh native equation independent of this host proposal.
    let text = "use std::gate::t;use std::state::init0;
        classical fn predicate(b:Bit)->Bit{b}
        pub observe fn main()->Bit{
            let q=with_computed(init0(),predicate){|a|
                let a=qfor static i in 0..509 carry r=a {yield h(h(r));};
                let a=t(t(t(t(t(a)))));let a=h(a);t(h(a))
            };measure_z(q)}";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let receipt = accepted
        .source_computed_normalizations()
        .iter()
        .find(|receipt| receipt.names().0.contains("main::main::with_computed["))
        .unwrap();
    assert_eq!(receipt.implementation().meaning(), &phase_matrix(&[0, 6]));
    assert_eq!(
        receipt.specification().meaning(),
        receipt.implementation().meaning()
    );
    assert!(
        receipt.implementation().program().raw().operations.len()
            > qleisli::contract::MAX_CONTRACT_STEPS
    );
    assert!(
        receipt
            .sources()
            .iter()
            .any(|(module, bytes)| module == "main" && bytes == text)
    );
}
