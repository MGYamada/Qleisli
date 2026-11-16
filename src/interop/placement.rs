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
    intervals: Option<&'a [WorkspaceInterval]>,
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
    pub(super) fn new(intervals: Option<&'a [WorkspaceInterval]>, length: usize) -> Self {
        Self {
            intervals,
            next_boundary: 0,
            gate_offsets: if intervals.is_some() {
                Vec::with_capacity(length + 1)
            } else {
                vec![]
            },
        }
    }

    pub(super) fn record(&mut self, index: usize, gates: usize, barriers: &mut [bool]) {
        let Some(intervals) = self.intervals else {
            return;
        };
        self.gate_offsets.push(gates);
        // A source workspace boundary can share the same gate position as its
        // neighbor, for example when a scope emits the identity word.
        while let Some(interval) = intervals.get(self.next_boundary / 2) {
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
        predicate_workspace: Vec<usize>,
        mut synthesis: Vec<usize>,
    ) -> Result<Alignment, InteropError> {
        let intervals = self.intervals.unwrap_or_default();
        if self.next_boundary != 2 * intervals.len() {
            return Err(invalid_alignment());
        }
        let mut workspaces = Vec::with_capacity(intervals.len());
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
                } else {
                    let predicate_width = match &raw.operations[index] {
                        RawOp::StructuralCompute { .. } => Some(1),
                        RawOp::ComputeUseUncompute { ancilla_wires, .. } => {
                            Some(ancilla_wires.len())
                        }
                        RawOp::ApplyUnitary { .. } => Some(0),
                        _ => None,
                    };
                    if let Some(width) = predicate_width {
                        let predicate = predicate_workspace
                            .get(..width)
                            .ok_or_else(invalid_alignment)?;
                        let work = predicate.iter().copied().chain(relevant_scratch());
                        Match::Decomposed(gates, work.collect())
                    } else {
                        Match::Original
                    }
                };
                result.push(action);
                index = next;
            }
            Ok::<_, InteropError>(result)
        };
        let suffix = if self.intervals.is_some() {
            for interval in intervals {
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
            let pure = raw.operations[start..]
                .iter()
                .position(|op| matches!(op, RawOp::MeasureZ { .. } | RawOp::Discard { .. }))
                .map_or(raw.operations.len(), |offset| start + offset);
            matches(start, pure)?
        } else {
            Vec::new()
        };
        synthesis.extend(predicate_workspace);
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

    fn native_program(source: &str) -> crate::AcceptedProgram {
        let root = std::path::PathBuf::from("/workspace-check");
        let module = SourceModule {
            name: "main".into(),
            path: root.join("main.qli"),
            source: source.into(),
            ast: parse_module(source).unwrap(),
            imports: Default::default(),
            origin: ModuleOrigin::Local,
        };
        Project::from_modules(root, [("main".into(), module)].into(), Edition::E2026)
            .compile_with_kernel(&Kernel::selected(Edition::E2026).unwrap())
            .unwrap()
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn workspace_resources_bind_the_actual_closed_natural_specialization() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/target-specialization-v030/attempt-03");
        let kernel = Kernel::selected(Edition::E2026).unwrap();
        let compile = |case| {
            Project::load(&root.join(case))
                .unwrap()
                .compile_with_kernel(&kernel)
        };
        let h = compile("n0").unwrap();
        let t = compile("n1").unwrap();
        let (h_target, h_resources) = crate::interop::export_openqasm3_with_resources(&h).unwrap();
        let (t_target, t_resources) = crate::interop::export_openqasm3_with_resources(&t).unwrap();
        assert!(h_target.contains("h q[0];"), "{h_target}");
        assert!(t_target.contains("t q[0];"), "{t_target}");
        assert_eq!((h_resources.qubits, h_resources.gates), (2, 1));
        assert_eq!((t_resources.qubits, t_resources.gates), (2, 1));
        assert_eq!((h_resources.t_gates, t_resources.t_gates), (0, 1));

        for (program, other_target) in [(&h, &t_target), (&t, &h_target)] {
            let intervals = workspace_intervals(
                program.source_context().unwrap(),
                program.raw().operations.len(),
            )
            .unwrap();
            let (_, alignment) =
                super::super::profile::extract_with_alignment(program, Some(&intervals), &mut None)
                    .unwrap();
            let error = program
                .check_openqasm_placement(other_target.as_bytes(), &alignment.encode())
                .unwrap_err();
            assert_eq!(error.code, "contract", "{error}");
        }

        let scalar = compile("n2").unwrap();
        let error = crate::interop::export_openqasm3_with_resources(&scalar).unwrap_err();
        assert_eq!(error.kind, InteropErrorKind::Unsupported);
        assert!(
            error.message.contains("uncontrolled scalar phase"),
            "{error}"
        );
        let error = compile("n3").expect_err("out-of-domain specialization");
        assert!(
            error
                .message
                .contains("callee natural premise is not implied"),
            "{error:?}"
        );
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn workspace_resources_bind_ordered_basis_and_provider_actuals() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/target-specialization-v030/attempt-05");
        let kernel = Kernel::selected(Edition::E2026).unwrap();
        let compile = |case| {
            Project::load(&root.join(case))
                .unwrap()
                .compile_with_kernel(&kernel)
        };
        let program = compile("ordered").unwrap();
        let (target, resources) =
            crate::interop::export_openqasm3_with_resources(&program).unwrap();
        assert!(target.contains("t q[0];\ntdg q[1];"), "{target}");
        assert_eq!(
            (resources.qubits, resources.gates, resources.t_gates),
            (3, 2, 2)
        );
        assert!(target.ends_with("c[0] = measure q[0];\nc[1] = measure q[1];\n"));

        let intervals = workspace_intervals(
            program.source_context().unwrap(),
            program.raw().operations.len(),
        )
        .unwrap();
        let (_, alignment) =
            super::super::profile::extract_with_alignment(&program, Some(&intervals), &mut None)
                .unwrap();
        let swapped = target.replace("t q[0];\ntdg q[1];", "t q[1];\ntdg q[0];");
        let error = program
            .check_openqasm_placement(swapped.as_bytes(), &alignment.encode())
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
        assert!(
            error.message.contains("clean workspace restoration failed"),
            "{error}"
        );

        let error =
            compile("swapped").expect_err("equal wire counts cannot substitute basis types");
        assert!(
            error
                .message
                .contains("expected `Op<Bit>`, found `Op<(Unit,Bit)>`"),
            "{error:?}"
        );
    }

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
        let program = native_program(source);
        let intervals = workspace_intervals(
            program.source_context().unwrap(),
            program.raw().operations.len(),
        )
        .unwrap();
        let (circuit, alignment) =
            super::super::profile::extract_with_alignment(&program, Some(&intervals), &mut None)
                .unwrap();
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

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn structural_predicate_report_binds_phase_axis_order_and_inverse() {
        // First CLI project: "tests/fixtures/authoring_sessions/structural-predicate-target-v030/first".
        // Procedure: "tests/fixtures/authoring_sessions/structural-predicate-target-v030/README.md".
        let first = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/structural-predicate-target-v030/first/main.qli"
        ));
        let register = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/structural-predicate-target-v030/ordered-register.qli"
        ));
        let before = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/structural-predicate-target-v030/terminal-before.stdout"
        ));
        assert!(before.contains("IR constructor outside the terminal profile at raw operation 3"));
        let standalone =
            register.replace("clean(q, h) { |data, scratch| (h(data), scratch) }", "h(q)");
        for (source, width) in [(first, 3), (standalone.as_str(), 2)] {
            let program = native_program(source);
            assert!(
                program
                    .raw()
                    .operations
                    .iter()
                    .any(|op| matches!(op, RawOp::StructuralCompute { .. }))
            );
            let intervals = workspace_intervals(
                program.source_context().unwrap(),
                program.raw().operations.len(),
            )
            .unwrap();
            let (circuit, alignment) = super::super::profile::extract_with_alignment(
                &program,
                Some(&intervals),
                &mut None,
            )
            .unwrap_or_else(|error| panic!("{error}: {:?}", program.raw().operations));
            let target = super::super::openqasm::write(&circuit);
            let encoded = alignment.encode();
            let (exported, resources) =
                crate::interop::export_openqasm3_with_resources(&program).unwrap();
            assert_eq!(exported, target);
            assert_eq!(
                (resources.qubits, resources.resets, resources.gates),
                (width, width, 5)
            );
            assert_eq!(resources.measurements, 1);

            let body = "cx q[0], q[1];\nz q[1];\ncx q[0], q[1];";
            assert!(target.contains(body), "{target}");
            for changed in [
                "cx q[0], q[1];\ns q[1];\ncx q[0], q[1];",
                "cx q[1], q[0];\nz q[1];\ncx q[1], q[0];",
                "cx q[0], q[1];\nz q[1];\nz q[1];",
            ] {
                let wrong = target.replace(body, changed);
                assert_eq!(
                    program
                        .check_openqasm_placement(wrong.as_bytes(), &encoded)
                        .unwrap_err()
                        .code,
                    "contract",
                    "{wrong}"
                );
            }
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn structural_predicate_report_counts_restored_synthesis_workspace() {
        let source = r#"#![no_implicit_prelude]
            classical fn mark(word: Bits<3>) -> Bit {
                word[0] and not word[1] and word[2]
            }
            isometry fn zero() -> Q<Bit> { basis unit(()) as _ {0} }
            observe fn main() -> Bit {
                let empty = basis unit(()) as _ {empty_bits()};
                let low = h(phase[1,1](h(zero())));
                let middle = zero();
                let high = h(zero());
                let word = put_bit[3,2](high, put_bit[2,1](middle, put_bit[1,0](low, empty)));
                let word = with_computed(word, mark) { |flag| phase[1,1](flag) };
                let (high, rest) = take_bit[3,2](word);
                let bit = measure_z(h(high));
                discard(rest);
                bit
            }"#;
        let program = native_program(source);
        let (target, resources) =
            crate::interop::export_openqasm3_with_resources(&program).unwrap();
        assert_eq!((resources.qubits, resources.resets), (5, 5));
        assert_eq!(
            resources.gates,
            target
                .lines()
                .filter(|line| {
                    ["h ", "x ", "z ", "ccx "]
                        .iter()
                        .any(|gate| line.starts_with(gate))
                })
                .count()
        );
        assert_eq!(
            target
                .lines()
                .filter(|line| line.starts_with("ccx "))
                .count(),
            8,
            "{target}"
        );
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn finite_predicate_export_binds_retained_table_and_protected_phase() {
        // CLI projects: "tests/fixtures/authoring_sessions/finite-predicate-target-v030/first"
        // and "tests/fixtures/authoring_sessions/finite-predicate-target-v030/typed".
        // Procedure: "tests/fixtures/authoring_sessions/finite-predicate-target-v030/README.md".
        let first = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/finite-predicate-target-v030/first/main.qli"
        ));
        let typed = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/finite-predicate-target-v030/typed/main.qli"
        ));
        let before = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/",
            "tests/fixtures/authoring_sessions/finite-predicate-target-v030/before.stdout"
        ));
        assert!(before.contains("checked OpenQASM resources require a source workspace"));

        let body = "cx q[0], q[1];\nz q[1];\ncx q[0], q[1];";
        let first = native_program(first);
        let text = crate::interop::export_openqasm3(&first).unwrap();
        assert!(text.contains(body), "{text}");
        let imported = crate::interop::import_openqasm3(Edition::E2026, &text).unwrap();
        let output = crate::sim::run_closed(&imported, Default::default()).unwrap();
        assert!((output[&vec![true]] - 1.0).abs() < 1e-12);
        assert_eq!(
            crate::interop::export_openqasm3_with_resources(&first)
                .unwrap_err()
                .kind,
            InteropErrorKind::Unsupported
        );

        let typed = native_program(typed);
        assert!(typed.raw().operations.iter().any(|op| matches!(op,
            RawOp::ComputeUseUncompute { function, .. } if function == &[0, 1])));
        let (target, resources) = crate::interop::export_openqasm3_with_resources(&typed).unwrap();
        assert!(target.contains(body), "{target}");
        assert_eq!(
            (resources.qubits, resources.resets, resources.gates),
            (2, 2, 3)
        );
        let (_, alignment) =
            super::super::profile::extract_with_alignment(&typed, Some(&[]), &mut None).unwrap();
        for replacement in [
            "cx q[0], q[1];\ns q[1];\ncx q[0], q[1];",
            "cx q[0], q[1];\nz q[1];\nx q[1];",
        ] {
            let wrong = target.replace(body, replacement);
            assert_eq!(
                typed
                    .check_openqasm_placement(wrong.as_bytes(), &alignment.encode())
                    .unwrap_err()
                    .code,
                "contract",
                "{wrong}"
            );
        }
    }
}
