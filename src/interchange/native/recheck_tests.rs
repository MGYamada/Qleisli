//! Rechecking must bind the original subject to the retained execution data.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::contract::BasisType;
use crate::ir::{Effect, RawOp, SingleGate, WireId};

const ARTIFACT: &[u8] =
    include_bytes!("../../../tests/fixtures/verification_v022/finite/t.v2.qirf");
const REQUEST: &[u8] = br#"{"format":"qleisli.request","version":1,"signature":{"tag":"bit"},"meaning":{"tag":"phase8","table":[0,1]},"source_snapshot":null}"#;

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn recheck_retains_original_request_interface_and_graph_allocations() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let original = kernel
        .check(ARTIFACT, Some(REQUEST))
        .unwrap()
        .into_program();
    let checked = kernel.check_program(&original).unwrap();
    let rebound = checked.program();
    assert_eq!(checked.artifact(), original.artifact());
    assert_eq!(checked.request(), Some(REQUEST));
    assert!(checked.imported().request_checked);
    assert_eq!(rebound.root_interface(), original.root_interface());
    assert_eq!(rebound.derived_effect(), original.derived_effect());
    assert_eq!(rebound.output_ports(), original.output_ports());
    assert_eq!(
        rebound.execution_view_description().unwrap(),
        original.execution_view_description().unwrap(),
    );
    assert!(Arc::ptr_eq(&rebound.decoded, &original.decoded));
    assert!(Arc::ptr_eq(
        &rebound.decoded.programs[rebound.decoded.root],
        &original.decoded.programs[original.decoded.root],
    ));
    assert!(!Arc::ptr_eq(&rebound.native, &original.native));
    assert!(!Arc::ptr_eq(
        &rebound.native.subject,
        &original.native.subject,
    ));
    assert_eq!(rebound.native.mode(), "--qirf-native");
    assert_eq!(
        rebound.native.context.scope(),
        crate::interchange::native_packet::Scope::Execution,
    );
    assert_eq!(log.summary().decisions(), 2);
    assert_eq!(log.summary().requests_checked(), 2);
    assert!(log.summary().complete());

    // An old accepted handle cannot replace a new invocation of this checker.
    let missing = Kernel::new("/missing-explicit-recheck-kernel", Edition::E2026);
    assert_eq!(missing.check_program(&original).unwrap_err().code, "io");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn recheck_rejects_divergent_retained_graph_and_metadata() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for mutation in 0..4 {
        let mut original = kernel
            .check(ARTIFACT, Some(REQUEST))
            .unwrap()
            .into_program();
        match mutation {
            0 => {
                let graph = Arc::get_mut(&mut original.decoded).unwrap();
                let root = Arc::make_mut(&mut graph.programs[graph.root]);
                let RawOp::Gate { gate, .. } = &mut root.operations[0] else {
                    panic!("the recheck fixture must retain its gate")
                };
                assert_eq!(*gate, SingleGate::T);
                // Z is valid Raw too. Raw-only reserialization therefore
                // misses its disagreement with the retained original T bytes.
                *gate = SingleGate::Z;
            }
            1 => original.derived_effect = Effect::Observe,
            2 => {
                // Equal physical widths do not identify the original type tree.
                original.interface = Some(RootInterface {
                    input: BasisType::Bits(1),
                    output: BasisType::Bits(1),
                });
            }
            _ => original.output_ports[0].wires[0] = WireId(8),
        }
        // These unchanged original bytes/request remain independently valid.
        kernel
            .inspect(original.artifact(), original.request())
            .unwrap();
        assert_eq!(
            kernel.check_program(&original).unwrap_err().code,
            "decoded_view",
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn recheck_refuses_contract_handle_without_ordinary_fallback() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let raw = kernel.check(ARTIFACT, None).unwrap().into_program();
    let boundary = crate::interchange::finite_leaf::UnitaryBoundary::new(
        BasisType::Bit,
        raw.raw().quantum_inputs[0].clone(),
        raw.output_ports()[0].clone(),
    )
    .unwrap();
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    let meaning = crate::contract::meaning::FiniteMeaning::phase(BasisType::Bit, vec![0, 1])
        .unwrap()
        .matrix(&mut budget)
        .unwrap();
    let contract = kernel.check_leaf(ARTIFACT, &boundary, &meaning).unwrap();
    assert_eq!(contract.native.mode(), "--qirf-contract");
    assert!(contract.request().is_some());
    let before = log.summary();
    assert_eq!(kernel.check_program(&contract).unwrap_err().code, "kernel");
    assert_eq!(log.summary().decisions(), before.decisions());
    assert_eq!(log.summary().requests_checked(), before.requests_checked());
}
