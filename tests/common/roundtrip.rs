//! Exact accepted-view checks shared by example and corpus execution tests.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use qleisli::AcceptedProgram;
use qleisli::contract::exact::Budget;
use qleisli::contract::{DEFAULT_EXACT_WORK, FunctionEvidence};
use qleisli::interchange::Version;
use qleisli::interchange::native::{Kernel, Proposal};
use qleisli::ir::{CircuitAction, CircuitStep, RawOp, RawProgram};
use std::collections::BTreeSet;
use std::sync::Arc;

/// Every reachable receipt, including both implementation and specification.
pub(super) fn receipts(program: &RawProgram) -> Vec<Arc<FunctionEvidence>> {
    fn steps(steps: &[CircuitStep], out: &mut Vec<Arc<FunctionEvidence>>) {
        for step in steps {
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                out.push(Arc::clone(evidence));
            }
        }
    }
    fn ops(list: &[RawOp], out: &mut Vec<Arc<FunctionEvidence>>) {
        for op in list {
            match op {
                RawOp::ApplyUnitary { steps: s, .. } => steps(s, out),
                RawOp::CertifiedCompute {
                    use_steps,
                    logical_steps,
                    ..
                } => {
                    steps(use_steps, out);
                    steps(logical_steps, out);
                }
                RawOp::ClassicalBranch {
                    then_ops, else_ops, ..
                } => {
                    ops(then_ops, out);
                    ops(else_ops, out);
                }
                _ => {}
            }
        }
    }
    let (mut seen, mut found, mut pending) = (BTreeSet::new(), Vec::new(), Vec::new());
    ops(&program.operations, &mut pending);
    while let Some(receipt) = pending.pop() {
        if seen.insert(Arc::as_ptr(&receipt) as usize) {
            ops(&receipt.implementation().operations, &mut pending);
            ops(&receipt.specification().operations, &mut pending);
            found.push(receipt);
        }
    }
    found
}

/// Compare every decoded execution cache with the implementation Lean checked.
pub(super) fn assert_cache_matches_implementation(
    program: &AcceptedProgram,
    context: &str,
) -> usize {
    let found = receipts(program.raw());
    for receipt in &found {
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let implementation = receipt.circuit().matrix(&mut budget).unwrap();
        assert_eq!(
            &implementation,
            receipt.meaning(),
            "{context}: cached execution matrix differs from the implementation"
        );
    }
    found.len()
}

pub(super) fn encode(program: &AcceptedProgram) -> Vec<u8> {
    Proposal::from_raw(program.raw(), program.root_interface(), Version::V2, None)
        .unwrap()
        .artifact()
        .to_vec()
}

/// Obtain a fresh native decision before checking the decoded view's exact bytes.
pub(super) fn assert_roundtrip(program: &AcceptedProgram, kernel: &Kernel, context: &str) -> usize {
    let first = encode(program);
    let checked = kernel.check(&first, None).unwrap();
    assert_eq!(
        first,
        encode(checked.program()),
        "{context}: decode/encode changed the proposal"
    );
    assert_cache_matches_implementation(checked.program(), context)
}
