//! Typed gate comparison and resource limits for independent native replay.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::interchange::engineering_openqasm_gate::{
    CHECKER_PROFILE, CLAIM_KIND, CONTROLLED, Contract, ERROR_CATEGORY, FORMAT, Ideal, METRIC,
    RESOURCE_MODEL, Request, SEQUENTIAL, TARGET_PROFILE, Target,
};
use crate::interchange::engineering_pure::DyadicBound;

fn bound(view: &mut View<'_>, value: DyadicBound) -> Result<()> {
    view.record("dyadic", 2, |w| {
        w.writer.text(&value.numerator().to_string())?;
        w.n(value.denominator_bits() as usize)
    })
}

fn ideal(view: &mut View<'_>, value: &Ideal) -> Result<()> {
    let original = std::str::from_utf8(value.program.artifact())
        .map_err(|_| Error::format("engineering ideal artifact requires UTF-8"))?;
    view.record("ideal", 2, |w| {
        w.record("leaf", 3, |w| {
            w.port(&value.input)?;
            w.port(&value.output)?;
            w.matrix(&value.matrix)
        })?;
        w.writer.text(original)
    })
}

fn contract(view: &mut View<'_>, value: &Contract) -> Result<()> {
    match value {
        Contract::Sequential {
            split,
            epsilons,
            ideals,
        } => view.record(SEQUENTIAL, 3, |w| {
            w.n(*split)?;
            for (value, epsilon) in ideals.iter().zip(epsilons) {
                w.record("component", 2, |w| {
                    ideal(w, value)?;
                    bound(w, *epsilon)
                })?;
            }
            Ok(())
        }),
        Contract::Controlled(value) => view.record(CONTROLLED, 1, |w| ideal(w, value)),
    }
}

pub(in crate::interchange) fn complete(request: &Request, target: &Target<'_>) -> Result<Vec<u8>> {
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
    view.record("engineering-openqasm-gate", 3, |w| {
        w.record("engineering-openqasm-gate-request", 10, |w| {
            w.writer.text(FORMAT)?;
            w.n(1)?;
            for value in [
                CLAIM_KIND,
                METRIC,
                CHECKER_PROFILE,
                TARGET_PROFILE,
                ERROR_CATEGORY,
            ] {
                w.writer.text(value)?;
            }
            bound(w, request.epsilon)?;
            contract(w, &request.contract)?;
            w.record("resource-limits", 3, |w| {
                w.writer.text(RESOURCE_MODEL)?;
                w.n(request.limits.gates)?;
                w.n(request.limits.t_gates)
            })
        })?;
        w.record("gate-tape", 3, |w| {
            w.list(target.bytes, |w, byte| w.n(usize::from(*byte)))?;
            w.basis(&target.basis)?;
            w.list(&target.gates, |w, gate| {
                w.record("gate", 2, |w| {
                    w.writer.text(gate.name)?;
                    w.axes(gate.wires)
                })
            })
        })?;
        w.list(request.contract.ideals(), |w, value| {
            value.program.execution_view_graph().write(w.writer)
        })
    })?;
    Ok(writer.bytes)
}
