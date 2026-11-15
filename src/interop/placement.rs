//! Placement proposals describe the gate word actually emitted by the exporter.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::export::GateBoundaries;
use super::profile::TerminalCircuit;
use super::{InteropError, InteropErrorKind, MAX_OPERATIONS};
use crate::interchange::qmatch::{ContextSubject, WorkspaceInterval};
use crate::ir::{RawOp, RawProgram};

pub(super) fn workspace_intervals(
    root: &ContextSubject,
    length: usize,
) -> Result<Vec<WorkspaceInterval>, InteropError> {
    let mut intervals = Vec::new();
    let mut pending = vec![(0, length, root)];
    let mut visits = 0;
    while let Some((base, length, context)) = pending.pop() {
        visits += 1;
        if visits + pending.len() + context.calls.len() + context.workspace_intervals.len()
            > MAX_OPERATIONS
        {
            return Err(InteropError::limit(
                "workspace alignment context exceeds operation limit",
            ));
        }
        for interval in &context.workspace_intervals {
            if interval.count == 0 || interval.start + interval.count > length {
                return Err(invalid_alignment());
            }
            intervals.push(WorkspaceInterval {
                start: base + interval.start,
                ..*interval
            });
        }
        for (position, child) in &context.calls {
            let start = position.start as usize;
            let count = position.count as usize;
            if start + count > length {
                return Err(invalid_alignment());
            }
            pending.push((base + start, count, child.as_ref()));
        }
    }
    intervals.sort_by_key(|interval| interval.start);
    if intervals
        .windows(2)
        .any(|pair| pair[0].start + pair[0].count > pair[1].start)
    {
        return Err(invalid_alignment());
    }
    Ok(intervals)
}

#[derive(Debug, PartialEq, Eq)]
enum Match {
    Original,
    Decomposed(usize, Vec<usize>),
    Optimized(usize, usize, Vec<usize>),
}

#[derive(Debug, PartialEq, Eq)]
struct Workspace {
    prefix: Vec<Match>,
    gates: usize,
    scratch: Option<usize>,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Alignment {
    capacity: usize,
    scratch: Option<usize>,
    synthesis: Vec<usize>,
    workspaces: Vec<Workspace>,
    suffix: Vec<Match>,
}

impl Alignment {
    pub(super) fn encode(&self) -> Vec<u8> {
        fn append(bytes: &mut Vec<u8>, words: &[usize]) {
            for &word in words {
                bytes.extend_from_slice(
                    &u32::try_from(word)
                        .expect("bounded placement word")
                        .to_le_bytes(),
                );
            }
        }

        fn append_list(bytes: &mut Vec<u8>, words: &[usize]) {
            append(bytes, &[words.len()]);
            append(bytes, words);
        }

        fn append_matches(bytes: &mut Vec<u8>, matches: &[Match]) {
            append(bytes, &[matches.len()]);
            for action in matches {
                match action {
                    Match::Original => append(bytes, &[0]),
                    Match::Decomposed(gates, scratch) if scratch.is_empty() => {
                        append(bytes, &[2, *gates])
                    }
                    Match::Decomposed(gates, scratch) => {
                        append(bytes, &[3, *gates]);
                        append_list(bytes, scratch);
                    }
                    Match::Optimized(raw, gates, scratch) => {
                        append(bytes, &[4, *raw, *gates]);
                        append_list(bytes, scratch);
                    }
                }
            }
        }

        let mut bytes = Vec::new();
        // This exporter has no physical routing requests. A Raw SWAP stays
        // attached to its original action, rather than gaining a routing tag.
        append(&mut bytes, &[self.capacity, 0]);
        append_list(&mut bytes, self.scratch.as_slice());
        append_list(&mut bytes, &self.synthesis);
        append(&mut bytes, &[self.workspaces.len()]);
        for workspace in &self.workspaces {
            append_matches(&mut bytes, &workspace.prefix);
            append(
                &mut bytes,
                &[
                    workspace.gates,
                    workspace.scratch.unwrap_or(super::MAX_QUBITS),
                ],
            );
        }
        append_matches(&mut bytes, &self.suffix);
        bytes
    }
}

pub(super) struct AlignmentBuilder<'a> {
    intervals: &'a [WorkspaceInterval],
    next_boundary: usize,
    gate_offsets: Vec<usize>,
}

fn invalid_alignment() -> InteropError {
    InteropError::new(
        InteropErrorKind::InvalidIr,
        "workspace alignment differs from target emission",
    )
}

impl<'a> AlignmentBuilder<'a> {
    pub(super) fn new(intervals: &'a [WorkspaceInterval], length: usize) -> Self {
        Self {
            intervals,
            next_boundary: 0,
            gate_offsets: if intervals.is_empty() {
                vec![]
            } else {
                Vec::with_capacity(length + 1)
            },
        }
    }

    pub(super) fn record(&mut self, index: usize, gates: usize, barriers: &mut [bool]) {
        if self.intervals.is_empty() {
            return;
        }
        self.gate_offsets.push(gates);
        // A source workspace boundary can share the same gate position as its
        // neighbor, for example when a scope emits the identity word.
        while let Some(interval) = self.intervals.get(self.next_boundary / 2) {
            let cut = if self.next_boundary % 2 == 0 {
                interval.start
            } else {
                interval.start + interval.count
            };
            if cut != index {
                break;
            }
            barriers[gates] = true;
            self.next_boundary += 1;
        }
    }

    pub(super) fn finish(
        self,
        raw: &RawProgram,
        circuit: &TerminalCircuit,
        boundaries: &GateBoundaries,
        scratch: Option<usize>,
        synthesis: Vec<usize>,
    ) -> Result<Alignment, InteropError> {
        if self.next_boundary != 2 * self.intervals.len() {
            return Err(invalid_alignment());
        }
        let mut workspaces = Vec::with_capacity(self.intervals.len());
        let mut start = 0;
        let matches = |mut index: usize, end: usize| {
            let mut result = Vec::new();
            while index < end {
                let gate_start = boundaries
                    .get(self.gate_offsets[index])
                    .ok_or_else(invalid_alignment)?;
                let mut next = index + 1;
                while next < end && boundaries.get(self.gate_offsets[next]).is_none() {
                    next += 1;
                }
                let gate_end = boundaries
                    .get(self.gate_offsets[next])
                    .ok_or_else(invalid_alignment)?;
                let gates = gate_end - gate_start;
                let relevant_scratch = || {
                    synthesis
                        .iter()
                        .copied()
                        .filter(|wire| {
                            circuit.gates[gate_start..gate_end]
                                .iter()
                                .any(|gate| gate.wires.contains(wire))
                        })
                        .collect()
                };
                let action = if next > index + 1 {
                    Match::Optimized(next - index, gates, relevant_scratch())
                } else if matches!(raw.operations[index], RawOp::ApplyUnitary { .. }) {
                    Match::Decomposed(gates, relevant_scratch())
                } else {
                    Match::Original
                };
                result.push(action);
                index = next;
            }
            Ok::<_, InteropError>(result)
        };
        if !self.intervals.is_empty() {
            for interval in self.intervals {
                let end = interval.start + interval.count;
                let first = boundaries
                    .get(self.gate_offsets[interval.start])
                    .ok_or_else(invalid_alignment)?;
                let last = boundaries
                    .get(self.gate_offsets[end])
                    .ok_or_else(invalid_alignment)?;
                workspaces.push(Workspace {
                    prefix: matches(start, interval.start)?,
                    gates: last - first,
                    scratch: if interval.fresh {
                        Some(scratch.ok_or_else(invalid_alignment)?)
                    } else {
                        None
                    },
                });
                start = end;
            }
        }
        let suffix = if self.intervals.is_empty() {
            Vec::new()
        } else {
            let pure = raw.operations[start..]
                .iter()
                .position(|op| matches!(op, RawOp::MeasureZ { .. } | RawOp::Discard { .. }))
                .map_or(raw.operations.len(), |offset| start + offset);
            matches(start, pure)?
        };
        Ok(Alignment {
            capacity: circuit.qubits,
            scratch,
            synthesis,
            workspaces,
            suffix,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edition::Edition;
    use crate::frontend::{
        parser::parse_module,
        project::{ModuleOrigin, Project, SourceModule},
    };
    use crate::interchange::native::Kernel;

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn native_rejects_swapped_workspace_and_spectator_wires() {
        let source = "#![no_implicit_prelude]\n\
            isometry fn zero()->Q<Bit>{basis unit(()) as _ {0}}\n\
            unitary fn mark(q:Q<Bit>)->Q<Bit>{clean(q,h){|data,scratch|(h(data),scratch)}}\n\
            unitary fn mark_twice(q:Q<Bit>)->Q<Bit>{mark(mark(q))}\n\
            observe fn main()->(Bit,Bit){\n\
                let held=h(zero()); let q=mark_twice(zero());\n\
                let a=measure_z(held); let b=measure_z(q); (b,a)}";
        let root = std::path::PathBuf::from("/workspace-check");
        let module = SourceModule {
            name: "main".into(),
            path: root.join("main.qli"),
            source: source.into(),
            ast: parse_module(source).unwrap(),
            imports: Default::default(),
            origin: ModuleOrigin::Local,
        };
        let program = Project::from_modules(root, [("main".into(), module)].into(), Edition::E2026)
            .compile_with_kernel(&Kernel::selected(Edition::E2026).unwrap())
            .unwrap();
        let intervals = workspace_intervals(
            program.source_context().unwrap(),
            program.raw().operations.len(),
        )
        .unwrap();
        let (circuit, alignment) =
            super::super::profile::extract_with_alignment(&program, &intervals).unwrap();
        let target = super::super::openqasm::write(&circuit);
        let encoded = alignment.encode();
        assert_eq!(alignment.workspaces.len(), 2);
        assert_eq!(
            program
                .check_openqasm_placement(target.as_bytes(), &encoded)
                .unwrap()
                .gates,
            3
        );

        let original_gates = "h q[0];\nh q[1];\nh q[1];";
        let original_readout = "c[0] = measure q[1];\nc[1] = measure q[0];";
        for (original, wrong) in [
            // The spare location is used only during clean scopes.
            ("qubit[3] q;", "qubit[2] q;"),
            (original_gates, "h q[1];\nh q[0];\nh q[1];"),
            (original_gates, "h q[0];\nh q[1];\nh q[0];"),
            (original_gates, "h q[0];\nh q[2];\nh q[1];"),
            (
                original_readout,
                "c[0] = measure q[0];\nc[1] = measure q[1];",
            ),
        ] {
            let changed = target.replace(original, wrong);
            assert_ne!(changed, target);
            let refusal = program
                .check_openqasm_placement(changed.as_bytes(), &encoded)
                .unwrap_err();
            assert!(
                matches!(refusal.code, "contract" | "invalid_ir"),
                "{refusal}: {changed}"
            );
        }

        let mut shifted = alignment;
        shifted.workspaces[0].gates = 0;
        shifted.workspaces[1].gates = 2;
        assert_eq!(
            program
                .check_openqasm_placement(target.as_bytes(), &shifted.encode())
                .unwrap_err()
                .code,
            "contract"
        );
    }
}
