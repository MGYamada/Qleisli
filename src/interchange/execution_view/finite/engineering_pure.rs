//! Typed engineering context and both retained graphs, independent of JSON.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::AcceptedProgram;
use crate::interchange::engineering_pure::EngineeringPureRequest;

pub(in crate::interchange) fn complete(
    request: &EngineeringPureRequest,
    ideal: &AcceptedProgram,
    actual: &AcceptedProgram,
) -> Result<Vec<u8>> {
    let expected_artifact = std::str::from_utf8(ideal.artifact())
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
    view.record("engineering-pure", 3, |w| {
        w.record("engineering-pure-request", 14, |w| {
            w.writer.text("qleisli.engineering-pure-request")?;
            w.n(1)?;
            for text in [
                "engineering",
                "pure-euclidean-operator-norm-v1",
                "frobenius-r8-pure-leaf-v1",
                "qirf-r8-pure-v1",
                "single-component-v1",
                "implementation-distance",
            ] {
                w.writer.text(text)?;
            }
            w.basis(request.actual_boundary().domain())?;
            w.basis(request.actual_boundary().codomain())?;
            for (boundary, matrix) in [
                (request.actual_boundary(), request.actual_meaning()),
                (request.ideal_boundary(), request.ideal_meaning()),
            ] {
                w.record("leaf", 3, |w| {
                    w.port(boundary.input())?;
                    w.port(boundary.output())?;
                    w.matrix(matrix)
                })?;
            }
            w.record("dyadic", 2, |w| {
                w.writer.text(&request.epsilon().numerator().to_string())?;
                w.n(request.epsilon().denominator_bits() as usize)
            })?;
            w.writer.text(expected_artifact)
        })?;
        actual.execution_view_graph().write(w.writer)?;
        ideal.execution_view_graph().write(w.writer)
    })?;
    Ok(writer.bytes)
}
