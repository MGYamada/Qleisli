//! Independently walk typed instrument requests and both retained graphs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::AcceptedProgram;
use crate::interchange::engineering_instrument::EngineeringInstrumentRequest;

pub(in crate::interchange) fn complete(
    request: &EngineeringInstrumentRequest,
    actual: &AcceptedProgram,
    expected: &AcceptedProgram,
) -> Result<Vec<u8>> {
    let expected_text = std::str::from_utf8(expected.artifact())
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
    view.record("engineering-instrument", 3, |w| {
        w.record("engineering-instrument-request", 14, |w| {
            w.writer.text("qleisli.engineering-instrument-request")?;
            w.n(1)?;
            for text in [
                "engineering-instrument-bound",
                "complete-adjoint-euclidean-operator-norm-v1",
                "choi-l1-r8-instrument-v1",
                "qirf-r8-instrument-v1",
                "single-component-v1",
                "implementation-distance",
            ] {
                w.writer.text(text)?;
            }
            w.signature(request.actual_signature().inner())?;
            w.signature(request.expected_signature().inner())?;
            let identity = request.identity();
            w.identity((
                &identity.implementation,
                &identity.specification,
                crate::contract::function::SourceView::Flat(&identity.sources),
            ))?;
            let dyadic =
                |w: &mut View<'_>, q: crate::interchange::engineering_pure::DyadicBound| {
                    w.record("dyadic", 2, |w| {
                        w.writer.text(&q.numerator().to_string())?;
                        w.n(q.denominator_bits() as usize)
                    })
                };
            dyadic(w, request.epsilon())?;
            w.list(request.majorants(), |w, q| dyadic(w, *q))?;
            w.writer.text(expected_text)
        })?;
        actual.execution_view_graph().write(w.writer)?;
        expected.execution_view_graph().write(w.writer)
    })?;
    Ok(writer.bytes)
}
