//! Typed target context, literal bytes, ordered gates and retained graphs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::AcceptedProgram;
use crate::interchange::engineering_openqasm::EngineeringOpenQasmRequest;

pub(in crate::interchange) fn complete(
    request: &EngineeringOpenQasmRequest,
    target: &[u8],
    gates: &[&str],
    actual: Graph<'_>,
    ideal: &AcceptedProgram,
) -> Result<Vec<u8>> {
    let ideal_text = std::str::from_utf8(ideal.artifact())
        .map_err(|_| Error::format("engineering ideal artifact requires UTF-8"))?;
    let indices = BTreeMap::new();
    let mut writer = Writer {
        bytes: b"QDV1".to_vec(),
        limit: MAX_BYTES,
        depth: 0,
    };
    let mut view = View {
        writer: &mut writer,
        dependencies: &indices,
    };
    view.record("engineering-openqasm", 5, |w| {
        w.record("engineering-openqasm-request", 14, |w| {
            w.writer.text("qleisli.engineering-openqasm-request")?;
            w.n(1)?;
            for text in [
                "engineering-target-instrument-bound",
                "complete-adjoint-euclidean-operator-norm-v1",
                "canonical-target-choi-l1-r8-v1",
                "openqasm3-canonical-one-qubit-terminal-r8-v1",
                "single-component-v1",
                "implementation-distance",
            ] {
                w.writer.text(text)?;
            }
            let contract = request.contract();
            w.signature(contract.actual_signature().inner())?;
            w.signature(contract.expected_signature().inner())?;
            let identity = contract.identity();
            w.identity((
                &identity.implementation,
                &identity.specification,
                crate::contract::function::SourceView::Flat(&identity.sources),
            ))?;
            let dyadic =
                |w: &mut View<'_>, bound: crate::interchange::engineering_pure::DyadicBound| {
                    w.record("dyadic", 2, |w| {
                        w.writer.text(&bound.numerator().to_string())?;
                        w.n(bound.denominator_bits() as usize)
                    })
                };
            dyadic(w, contract.epsilon())?;
            w.list(contract.majorants(), |w, bound| dyadic(w, *bound))?;
            w.writer.text(ideal_text)
        })?;
        w.list(target, |w, byte| w.n(usize::from(*byte)))?;
        w.list(gates, |w, gate| w.writer.text(gate))?;
        actual.write(w.writer)?;
        ideal.execution_view_graph().write(w.writer)
    })?;
    Ok(writer.bytes)
}
