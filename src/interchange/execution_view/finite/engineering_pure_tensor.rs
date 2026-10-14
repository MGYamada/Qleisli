//! Typed tensor context and all six retained graphs, independent of JSON.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::AcceptedProgram;
use crate::interchange::engineering_pure::EngineeringPureRequest;
use crate::interchange::engineering_pure_tensor::EngineeringPureTensorRequest;

fn leaf(
    w: &mut View<'_>,
    boundary: &crate::interchange::pure_leaf::PureBoundary,
    matrix: &Matrix,
) -> Result<()> {
    w.record("leaf", 3, |w| {
        w.port(boundary.input())?;
        w.port(boundary.output())?;
        w.matrix(matrix)
    })
}

fn epsilon(w: &mut View<'_>, request: &EngineeringPureRequest) -> Result<()> {
    w.record("dyadic", 2, |w| {
        w.writer.text(&request.epsilon().numerator().to_string())?;
        w.n(request.epsilon().denominator_bits() as usize)
    })
}

fn artifact(program: &AcceptedProgram) -> Result<&str> {
    std::str::from_utf8(program.artifact())
        .map_err(|_| Error::format("engineering tensor artifacts require UTF-8"))
}

fn component(
    w: &mut View<'_>,
    request: &EngineeringPureRequest,
    actual: &AcceptedProgram,
    ideal: &AcceptedProgram,
) -> Result<()> {
    w.record("engineering-pure-component", 7, |w| {
        w.basis(request.actual_boundary().domain())?;
        w.basis(request.actual_boundary().codomain())?;
        leaf(w, request.actual_boundary(), request.actual_meaning())?;
        leaf(w, request.ideal_boundary(), request.ideal_meaning())?;
        epsilon(w, request)?;
        w.writer.text(artifact(actual)?)?;
        w.writer.text(artifact(ideal)?)
    })
}

pub(in crate::interchange) fn complete(
    request: &EngineeringPureTensorRequest,
    programs: [&AcceptedProgram; 6],
) -> Result<Vec<u8>> {
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
    view.record("engineering-pure-tensor", 7, |w| {
        w.record("engineering-pure-tensor-request", 16, |w| {
            w.writer.text("qleisli.engineering-pure-tensor-request")?;
            w.n(1)?;
            for text in [
                "engineering-pure-tensor-bound",
                "pure-euclidean-operator-norm-v1",
                "tensor-additive-r8-pure-leaf-v1",
                "qirf-r8-pure-v1",
                "ordered-tensor-two-v1",
                "implementation-distance",
            ] {
                w.writer.text(text)?;
            }
            w.basis(request.parent().actual_boundary().domain())?;
            w.basis(request.parent().actual_boundary().codomain())?;
            leaf(
                w,
                request.parent().actual_boundary(),
                request.parent().actual_meaning(),
            )?;
            leaf(
                w,
                request.parent().ideal_boundary(),
                request.parent().ideal_meaning(),
            )?;
            epsilon(w, request.parent())?;
            component(w, request.left(), programs[2], programs[3])?;
            component(w, request.right(), programs[4], programs[5])?;
            w.writer.text(artifact(programs[1])?)
        })?;
        for program in programs {
            program.execution_view_graph().write(w.writer)?;
        }
        Ok(())
    })?;
    Ok(writer.bytes)
}
