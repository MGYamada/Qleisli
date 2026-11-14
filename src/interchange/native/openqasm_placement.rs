//! Transport a retained source request and the final emitted target in one bounded check.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::{AcceptedProgram, Error, Kernel, Result};
use crate::edition::Edition;
use crate::interchange::execution_view::finite::qmatch_v5;
use crate::interchange::native_context::{self, Mode, Reply};
use crate::interchange::native_packet::{Scope, View};
use crate::interop::OpenQasmResources;
use std::time::Duration;

impl AcceptedProgram {
    pub(crate) fn check_openqasm_placement(
        &self,
        target: &[u8],
        alignment: &[u8],
    ) -> Result<OpenQasmResources> {
        let request = self.qmatch_result.as_deref().ok_or_else(|| {
            Error::new(
                "unsupported",
                "placement checking requires a retained v5 source request",
            )
        })?;
        let graph = qmatch_v5::complete(self.execution_view_graph(), request)?;
        let (source, _) = Kernel::encode_subject(
            &self.native.subject,
            Some(View {
                graph: &graph,
                caller: None,
            }),
        )?;
        let packet = packet(&source, target, alignment)?;
        crate::interchange::process::invoke(
            self.native.checker(),
            packet,
            Mode::OpenQasmPlacement.argument(),
            Duration::from_secs(60),
            256,
            |bytes| response(bytes, self.edition()),
        )
    }
}

fn packet(source: &[u8], target: &[u8], alignment: &[u8]) -> Result<Vec<u8>> {
    let size = 16 + source.len() + target.len() + alignment.len();
    if size > 64 << 20 || target.len() > 1 << 20 || alignment.len() > 1 << 20 {
        return Err(Error::limit(
            "OpenQASM placement packet exceeds component limits",
        ));
    }
    let mut packet = Vec::with_capacity(size);
    packet.extend_from_slice(b"QTP1");
    for part in [source, target, alignment] {
        packet.extend_from_slice(&(part.len() as u32).to_le_bytes());
    }
    for part in [source, target, alignment] {
        packet.extend_from_slice(part);
    }
    Ok(packet)
}

fn count(value: &str, max: usize) -> Result<usize> {
    if value.is_empty()
        || value.len() > 8
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(Error::format("noncanonical OpenQASM resource count"));
    }
    value
        .parse::<usize>()
        .ok()
        .filter(|value| *value <= max)
        .ok_or_else(|| Error::format("OpenQASM resource count exceeds profile"))
}

fn response(bytes: &[u8], edition: Edition) -> Result<OpenQasmResources> {
    let payload =
        match native_context::parse(bytes, edition, Mode::OpenQasmPlacement, Scope::Execution)? {
            Reply::Checked { payload, .. } => payload,
            Reply::Rejected(code) => {
                if let Some(error) = Error::workspace_restoration(code) {
                    return Err(error);
                }
                return Err(Error::new(
                    if code == "version" { "kernel" } else { code },
                    "Lean OpenQASM placement checker rejected the source, target or alignment",
                ));
            }
        };
    let [work, qubits, resets, gates, swaps, t_gates, measurements] = payload.as_slice() else {
        return Err(Error::format("malformed OpenQASM placement response"));
    };
    let qubits = count(qubits, crate::interop::MAX_QUBITS)?;
    let gates = count(gates, crate::interop::MAX_GATES)?;
    Ok(OpenQasmResources {
        exact_work: count(work, crate::contract::DEFAULT_EXACT_WORK)?,
        qubits,
        resets: count(resets, qubits)?,
        gates,
        swaps: count(swaps, gates)?,
        t_gates: count(t_gates, gates)?,
        measurements: count(measurements, qubits)?,
    })
}
