//! Transport a retained source request and the final emitted target in one bounded check.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::{AcceptedProgram, Error, Kernel, Result};
use crate::edition::Edition;
use crate::interchange::execution_view::finite::qmatch_v5;
use crate::interchange::native_context::{self, Mode, Reply};
use crate::interchange::native_packet::{Scope, View};
use crate::interop::OpenQasmResources;
use std::ops::Range;
use std::time::Duration;

#[derive(Debug)]
pub(crate) struct PlacementFailure {
    pub(crate) error: Error,
    pub(crate) workspace: Option<WorkspaceRejection>,
}

#[derive(Debug)]
pub(crate) struct WorkspaceRejection {
    pub(crate) operations: Range<usize>,
    pub(crate) fresh: bool,
}

impl From<Error> for PlacementFailure {
    fn from(error: Error) -> Self {
        Self {
            error,
            workspace: None,
        }
    }
}

impl AcceptedProgram {
    pub(crate) fn check_openqasm_placement(
        &self,
        target: &[u8],
        alignment: &[u8],
    ) -> std::result::Result<OpenQasmResources, PlacementFailure> {
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
        let mut workspace = None;
        crate::interchange::process::invoke(
            self.native.checker(),
            packet,
            Mode::OpenQasmPlacement.argument(),
            Duration::from_secs(60),
            256,
            |bytes| {
                if let Some((error, located)) =
                    located_rejection(bytes, self.edition(), self.raw().operations.len())?
                {
                    workspace = Some(located);
                    return Err(error);
                }
                response(bytes, self.edition())
            },
        )
        .map_err(|error| PlacementFailure { error, workspace })
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

fn located_rejection(
    bytes: &[u8],
    edition: Edition,
    operations: usize,
) -> Result<Option<(Error, WorkspaceRejection)>> {
    let Some(payload) = bytes.strip_prefix(b"qleisli.native-result 3\nerror\n") else {
        return Ok(None);
    };
    let payload =
        std::str::from_utf8(payload).map_err(|_| Error::format("invalid native response UTF-8"))?;
    let fields: Vec<_> = payload.split('\n').collect();
    if matches!(fields.as_slice(), [_, ""]) {
        return Ok(None);
    }
    let [
        code,
        actual_edition,
        product,
        mode,
        "execution",
        start,
        length,
        "",
    ] = fields.as_slice()
    else {
        return Err(Error::format("malformed OpenQASM placement rejection"));
    };
    if *actual_edition != edition.as_str()
        || *product != env!("CARGO_PKG_VERSION")
        || *mode != Mode::OpenQasmPlacement.argument()
    {
        return Err(Error::format(
            "OpenQASM placement rejection context differs",
        ));
    }
    let (code, fresh) = match *code {
        "clean_workspace" => ("clean_workspace", true),
        "dirty_workspace" => ("dirty_workspace", false),
        _ => return Err(Error::format("unexpected located OpenQASM rejection")),
    };
    let start = count(start, operations)?;
    let length = count(length, operations)?;
    if length == 0 || length > operations - start {
        return Err(Error::format(
            "OpenQASM workspace location exceeds the Raw root",
        ));
    }
    let location = WorkspaceRejection {
        operations: start..start + length,
        fresh,
    };
    Ok(Error::workspace_restoration(code).map(|error| (error, location)))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_a_context_bound_nonempty_raw_interval_locates_a_workspace_rejection() {
        let prefix = "qleisli.native-result 3\nerror\n";
        let reply = |code: &str, context: &str, start: &str, length: &str| {
            format!(
                "{prefix}{code}\n2026\n{}\n--openqasm-placement-check\n{context}\n{start}\n{length}\n",
                env!("CARGO_PKG_VERSION")
            )
        };
        let clean = reply("clean_workspace", "execution", "7", "1");
        let (error, workspace) = located_rejection(clean.as_bytes(), Edition::E2026, 8)
            .unwrap()
            .unwrap();
        assert_eq!(error.code, "contract");
        assert!(workspace.fresh);
        assert_eq!(workspace.operations, 7..8);
        let dirty = reply("dirty_workspace", "execution", "2", "3");
        let (_, workspace) = located_rejection(dirty.as_bytes(), Edition::E2026, 8)
            .unwrap()
            .unwrap();
        assert!(!workspace.fresh);
        assert_eq!(workspace.operations, 2..5);

        assert!(
            located_rejection(
                b"qleisli.native-result 3\nerror\nlimit\n",
                Edition::E2026,
                8
            )
            .unwrap()
            .is_none()
        );
        for invalid in [
            reply("limit", "execution", "7", "1"),
            reply("clean_workspace", "inspection", "7", "1"),
            reply("clean_workspace", "execution", "07", "1"),
            reply("clean_workspace", "execution", "7", "0"),
            reply("clean_workspace", "execution", "7", "2"),
            clean.replace("--openqasm-placement-check", "--qmatch-source-v5-check"),
            format!("{clean}extra\n"),
        ] {
            assert_eq!(
                located_rejection(invalid.as_bytes(), Edition::E2026, 8)
                    .unwrap_err()
                    .code,
                "format"
            );
        }
    }
}
