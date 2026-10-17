//! Untrusted normalization of an original computed-ancilla body.
//!
//! Host matrix inspection proposes an eighth-root diagonal. A fresh native
//! whole-body leaf decision compares the complete checked fragment, including
//! its scalar phase and dependencies, with that proposal before protected Raw
//! lowering. The retained receipt is local provenance, not a source theorem.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::contract::{BasisType, ContractError};
use crate::frontend::resolve::locals::OriginalNode;
use crate::interchange::finite_leaf::{CheckedUnitaryLeaf, SourceUnitaryEquation, UnitaryBoundary};

enum ComputedTransport<'a> {
    Original(&'a AcceptedProgram),
    Canonical(&'a RawProgram),
}

impl Lowerer<'_, '_> {
    pub(super) fn computed_refusal(
        &mut self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: &'static str,
    ) -> Result<CompileError, CompileError> {
        self.compiler.charge(module, span, message.len() + 1)?;
        Ok(self.error(module, span, code, message))
    }

    /// The private adapter may only consume the actual checked scoped body.
    pub(super) fn original_computed_body(
        &mut self,
        module: &str,
        original: &Expr,
        function: &Ident,
        binder: &Ident,
        body: &Block,
    ) -> Result<Key, CompileError> {
        let mut work = self.compiler.work;
        let result = (|| {
            let compiler = &*self.compiler;
            macro_rules! refuse {
                () => {{
                    let message = "with_computed body differs from its original checked expression";
                    compiler.charge_at(&mut work, module, original.span, message.len() + 1)?;
                    return Err(compiler.error(
                        module,
                        original.span,
                        ErrorCode::TypeMismatch,
                        message,
                    ));
                }};
            }
            compiler.charge_at(&mut work, module, original.span, module.len() + 8)?;
            let lookup = compiler.locals();
            let Some(node) = lookup.try_node_id_expr(original) else {
                refuse!();
            };
            let owner = node.definition();
            let Some(table) = compiler.source.lexical.get(&owner) else {
                refuse!();
            };
            if compiler.checking != Some(owner)
                || !compiler.declarations.contains_key(&owner)
                || compiler.source.resolution.declaration(owner).name.0 != module
                || !lookup.original_table_is(owner, table)
            {
                refuse!();
            }
            let Some(OriginalNode::Expression(found)) = lookup
                .original_node_budgeted(node, |at, cells| {
                    compiler.charge_at(&mut work, module, at, cells)
                })?
            else {
                refuse!();
            };
            let ExprKind::WithComputed {
                function: f,
                binder: b,
                body: block,
                ..
            } = &found.kind
            else {
                refuse!();
            };
            if !std::ptr::eq(found, original)
                || !std::ptr::eq(f, function)
                || !std::ptr::eq(b, binder)
                || !std::ptr::eq(block, body)
                || lookup.try_binder(binder).is_none()
            {
                refuse!();
            }
            Ok(owner)
        })();
        self.compiler.work = work;
        result
    }

    fn computed_contract_error(
        &mut self,
        module: &str,
        span: Span,
        error: ContractError,
    ) -> Result<CompileError, CompileError> {
        // The enum's only owned diagnostic payload is charged before formatting.
        // Numeric exact errors need at most two usize values plus fixed prose.
        let payload = match &error {
            ContractError::InvalidCircuit(message) => message.len(),
            ContractError::Limit(message) | ContractError::Type(message) => message.len(),
            _ => 0,
        };
        self.compiler
            .charge(module, span, payload.saturating_add(256))?;
        Ok(self.error(
            module,
            span,
            if error.is_capacity() {
                ErrorCode::Limit
            } else {
                ErrorCode::Contract
            },
            format!("with_computed phase normalization: {error}"),
        ))
    }

    /// Charge traversal and all deep snapshot storage before cloning Raw.
    fn computed_snapshot_size(
        &mut self,
        module: &str,
        span: Span,
        start: usize,
    ) -> Result<usize, CompileError> {
        self.compiler.charge(module, span, 1)?;
        let mut pending = vec![&self.raw.operations[start..]];
        let mut size = 0usize;
        while let Some(operations) = pending.pop() {
            for operation in operations {
                self.compiler.tick(module, span)?;
                size = size.saturating_add(8);
                let extra = match operation {
                    RawOp::ApplyUnitary { steps, .. } => steps.iter().fold(0usize, |sum, step| {
                        sum.saturating_add(crate::frontend::raw_state::circuit_size(step))
                    }),
                    RawOp::CertifiedCompute {
                        ancilla_wires,
                        function,
                        use_steps,
                        logical_steps,
                        ..
                    } => ancilla_wires
                        .len()
                        .saturating_add(function.len())
                        .saturating_add(use_steps.iter().chain(logical_steps).fold(
                            0usize,
                            |sum, step| {
                                sum.saturating_add(crate::frontend::raw_state::circuit_size(step))
                            },
                        )),
                    RawOp::LiftBasis {
                        output_wires,
                        table,
                        ..
                    } => output_wires.len().saturating_add(table.len()),
                    RawOp::QuantumIf {
                        zero_ops, one_ops, ..
                    // These arms contain Copy UnitaryStep enums with at most
                    // three scalar indices, not owned CircuitStep children.
                    } => (zero_ops.len() + one_ops.len()).saturating_mul(4),
                    RawOp::ClassicalBranch {
                        then_ops,
                        else_ops,
                        quantum_phis,
                        classical_phis,
                        ..
                    } => {
                        self.compiler.charge(module, span, 2)?;
                        pending.extend([then_ops.as_slice(), else_ops.as_slice()]);
                        quantum_phis
                            .iter()
                            .fold(classical_phis.len().saturating_mul(3), |sum, phi| {
                                sum.saturating_add(phi.output_wires.len() + 3)
                            })
                    }
                    RawOp::ComputeUseUncompute {
                        targets,
                        ancilla_wires,
                        function,
                        use_ops,
                        ..
                    } => targets
                        .len()
                        .saturating_mul(2)
                        .saturating_add(ancilla_wires.len())
                        .saturating_add(function.len())
                        .saturating_add(use_ops.iter().fold(0usize, |sum, usage| {
                            sum.saturating_add(match usage {
                                ProtectedUse::ProtectedGate { .. } => 3,
                                ProtectedUse::ControlledTargetGate { controls, .. }
                                | ProtectedUse::ControlledPhase { controls, .. } => {
                                    3 + controls.len() * 3
                                }
                            })
                        })),
                    _ => 0,
                };
                size = size.saturating_add(extra);
            }
        }
        Ok(size.saturating_add(8))
    }

    /// Preserve the established exact Raw Z/T transport without importing
    /// function-equation length or source-snapshot limits into that profile.
    /// Selection precedes every equation attempt; this is never a fallback.
    fn canonical_computed_phase(
        &mut self,
        module: &str,
        span: Span,
        start: usize,
        initial: TokenId,
        output: TokenId,
    ) -> Result<Option<Vec<ProtectedUse>>, CompileError> {
        let mut expected = initial;
        for operation in &self.raw.operations[start..] {
            self.compiler.tick(module, span)?;
            match operation {
                RawOp::Gate {
                    gate,
                    input,
                    output,
                } if matches!(gate, SingleGate::Z | SingleGate::T) && *input == expected => {
                    expected = *output
                }
                _ => return Ok(None),
            }
        }
        if expected != output {
            return Ok(None);
        }
        let count = self.raw.operations.len() - start;
        self.compiler
            .charge(module, span, count.saturating_mul(4).saturating_add(1))?;
        let bit = ProtectedBit {
            region: ProtectedRegion::Ancilla,
            index: 0,
        };
        let mut use_ops = Vec::with_capacity(count);
        for operation in &self.raw.operations[start..] {
            let RawOp::Gate { gate, .. } = operation else {
                unreachable!("complete canonical chain checked");
            };
            use_ops.push(ProtectedUse::ProtectedGate { bit, gate: *gate });
        }
        Ok(Some(use_ops))
    }

    /// Normalize only this one-Bit body, independently of the data width.
    /// No data-register dense matrix or narrower computed profile is imported.
    pub(super) fn normalize_computed_phase(
        &mut self,
        module: &str,
        original: &Expr,
        owner: Key,
        input: (TokenId, WireId),
        start: usize,
        returned: Slot,
    ) -> Result<(Vec<ProtectedUse>, Option<Arc<SourceUnitaryEquation>>), CompileError> {
        let (initial, wire) = input;
        let span = original.span;
        self.compiler.charge(module, span, 5)?;
        let Some(register) = self.raw.registers.get(&returned) else {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::Ownership,
                "with_computed returned an unavailable ancilla owner",
            )?);
        };
        if register.basis != Ty::bit() || register.wires.as_slice() != [wire] {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::Ownership,
                "with_computed must return its exact ordered Bit ancilla frame",
            )?);
        }
        let output = register.token;
        if let Some(use_ops) =
            self.canonical_computed_phase(module, span, start, initial, output)?
        {
            // The unchanged constructor-for-constructor protected chain still
            // requires the enclosing native Raw acceptance and cleanup gate.
            // It has no optimization equation or fabricated normalization receipt.
            return Ok((use_ops, None));
        }
        let size = self.computed_snapshot_size(module, span, start)?;
        self.compiler.charge(module, span, size.saturating_mul(2))?;
        let implementation = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: initial,
                wires: vec![wire],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations: self.raw.operations[start..].to_vec(),
            quantum_outputs: vec![output],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        // First inspect the complete actual fragment, including its original
        // dependencies. Outer classical references or quantum frame escapes
        // cannot become assumed inputs of this private one-ancilla function.
        let checked = match self
            .compiler
            .kernel
            .accept_raw_with_budget(implementation.clone(), &mut self.compiler.exact_work)
        {
            Ok(checked) => checked,
            Err(failure) => {
                self.compiler.charge(
                    module,
                    span,
                    failure.code.len() + failure.message.len() + failure.json_pointer.len() + 96,
                )?;
                let code = if failure.code == "limit" {
                    ErrorCode::Limit
                } else if matches!(failure.code, "io" | "kernel") {
                    ErrorCode::Project
                } else {
                    ErrorCode::InvalidIr
                };
                return Err(self.error(
                    module,
                    span,
                    code,
                    format!("with_computed actual ancilla fragment: {failure}"),
                ));
            }
        };
        let matrix = self.computed_phase_proposal(module, span, &checked)?;
        // This inspection is merely the untrusted optimization proposal. Both
        // entries, including the global scalar, participate in native equality.
        self.compiler.charge(module, span, 22)?;
        let phases = if matrix.rows() == 2
            && matrix.cols() == 2
            && matrix.get(0, 1) == Some(crate::contract::exact::Exact::zero())
            && matrix.get(1, 0) == Some(crate::contract::exact::Exact::zero())
        {
            let a = (0u8..8).find(|&k| {
                matrix.get(0, 0) == Some(crate::contract::exact::Exact::phase(i32::from(k)))
            });
            let b = (0u8..8).find(|&k| {
                matrix.get(1, 1) == Some(crate::contract::exact::Exact::phase(i32::from(k)))
            });
            a.zip(b).map(|(a, b)| [a, b])
        } else {
            None
        };
        let Some(phases) = phases else {
            return Err(self.computed_refusal(module, span, ErrorCode::Unsupported,
                "with_computed requires an exact eighth-root diagonal ancilla action; non-diagonal and unrepresentable phases have no protected normalization. For other unitary bodies, use with_computed(source, predicate, logical) { |data, ancilla| ... } and return both owners. The logical operation must satisfy the exact computed-relation contract; adding it does not bypass cleanup checking")?);
        };
        self.check_computed_phase_equation(module, original, owner, &checked, phases)
            .map(|(use_ops, evidence)| (use_ops, Some(evidence)))
    }

    /// Chunking only constructs an untrusted exact matrix proposal. The
    /// subsequent native request always reconstructs the whole original Raw.
    fn computed_phase_proposal(
        &mut self,
        module: &str,
        span: Span,
        checked: &AcceptedProgram,
    ) -> Result<crate::contract::exact::Matrix, CompileError> {
        let steps = super::super::circuit::flatten(self.compiler, module, span, checked)?;
        self.compiler.charge(module, span, 4)?;
        if let Err(error) = self.compiler.exact_work.charge(4) {
            return Err(self.computed_contract_error(module, span, error.into())?);
        }
        let mut accumulated: Result<crate::contract::exact::Matrix, ContractError> =
            crate::contract::exact::Matrix::identity(2).map_err(ContractError::from);
        for chunk in steps.chunks(crate::contract::MAX_CONTRACT_STEPS) {
            let cost = chunk.iter().fold(chunk.len(), |sum, step| {
                sum.saturating_add(crate::frontend::raw_state::circuit_size(step))
            });
            self.compiler.charge(module, span, cost)?;
            let next = crate::contract::Circuit::new(BasisType::Bit, chunk.to_vec())
                .and_then(|circuit| circuit.matrix(&mut self.compiler.exact_work));
            accumulated = match (next, accumulated) {
                (Ok(next), Ok(previous)) => next
                    .compose(&previous, &mut self.compiler.exact_work)
                    .map_err(ContractError::from),
                (Err(error), _) | (_, Err(error)) => {
                    return Err(self.computed_contract_error(module, span, error)?);
                }
            };
        }
        match accumulated {
            Ok(matrix) => Ok(matrix),
            Err(error) => Err(self.computed_contract_error(module, span, error)?),
        }
    }

    fn computed_native_error(
        &mut self,
        module: &str,
        span: Span,
        stage: &'static str,
        failure: crate::interchange::Error,
    ) -> Result<CompileError, CompileError> {
        self.compiler.charge(
            module,
            span,
            failure.code.len()
                + failure.message.len()
                + failure.json_pointer.len()
                + stage.len()
                + 96,
        )?;
        let code = match failure.code {
            "limit" => ErrorCode::Limit,
            "io" | "kernel" => ErrorCode::Project,
            "contract" => ErrorCode::Contract,
            _ => ErrorCode::InvalidIr,
        };
        Ok(self.error(
            module,
            span,
            code,
            format!("with_computed {stage}: {failure}"),
        ))
    }

    fn computed_unitary_leaf(
        &mut self,
        module: &str,
        span: Span,
        transport: ComputedTransport<'_>,
        meaning: &crate::contract::exact::Matrix,
    ) -> Result<Arc<CheckedUnitaryLeaf>, CompileError> {
        self.compiler.charge(module, span, 6)?;
        let (raw, bytes, exact_size) = match transport {
            ComputedTransport::Original(checked) => {
                if checked.root_interface().is_some() {
                    return Err(self.computed_refusal(
                        module,
                        span,
                        ErrorCode::InvalidIr,
                        "computed original transport already has an unexpected interface",
                    )?);
                }
                // The same immutable checked Raw/dependencies use the same
                // V2 codec. Only root_interface changes: null (4 bytes) becomes
                // these two Bit tags (46 bytes). This is storage accounting.
                const BIT_INTERFACE: &str = r#"{"input":{"tag":"bit"},"output":{"tag":"bit"}}"#;
                (
                    checked.raw(),
                    checked
                        .artifact()
                        .len()
                        .saturating_add(BIT_INTERFACE.len() - 4),
                    true,
                )
            }
            ComputedTransport::Canonical(raw) => (
                raw,
                self.computed_canonical_transport_bound(module, span, raw)?,
                false,
            ),
        };
        // Reserve before encoding or leaf copies. Native equation work uses
        // the same monotone budget; refusals never refund either allocation.
        if let Err(error) = self
            .compiler
            .exact_work
            .charge(bytes.saturating_mul(2).saturating_add(8))
        {
            return Err(self.computed_contract_error(module, span, error.into())?);
        }
        let ([input], [output]) = (
            raw.quantum_inputs.as_slice(),
            raw.quantum_outputs.as_slice(),
        ) else {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::InvalidIr,
                "computed leaf lacks its single exact Bit input and output",
            )?);
        };
        if input.shape != BasisShape::BIT || input.wires.len() != 1 {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::InvalidIr,
                "computed leaf input is not the exact original Bit owner",
            )?);
        }
        self.compiler
            .charge(module, span, input.wires.len().saturating_mul(2) + 8)?;
        let boundary = match UnitaryBoundary::new(
            BasisType::Bit,
            input.clone(),
            QuantumPort {
                token: *output,
                wires: input.wires.clone(),
                shape: BasisShape::BIT,
            },
        ) {
            Ok(boundary) => boundary,
            Err(failure) => {
                return Err(self.computed_native_error(module, span, "leaf boundary", failure)?);
            }
        };
        let interface = crate::interchange::RootInterface {
            input: BasisType::Bit,
            output: BasisType::Bit,
        };
        let proposal = match crate::interchange::native::Proposal::from_raw(
            raw,
            Some(&interface),
            crate::interchange::Version::V2,
            None,
        ) {
            Ok(proposal) => proposal,
            Err(failure) => {
                return Err(self.computed_native_error(module, span, "leaf proposal", failure)?);
            }
        };
        if proposal.artifact().len() > bytes || (exact_size && proposal.artifact().len() != bytes) {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::InvalidIr,
                "computed transport exceeds its pre-reserved original codec size",
            )?);
        }
        self.compiler.charge(module, span, 1)?;
        match crate::interchange::finite_leaf::check_with_kernel(
            &self.compiler.kernel,
            proposal.artifact(),
            &boundary,
            meaning,
            &mut self.compiler.exact_work,
        ) {
            Ok(leaf) => Ok(Arc::new(leaf)),
            Err(failure) => Err(self.computed_native_error(
                module,
                span,
                "whole-body exact equation",
                failure,
            )?),
        }
    }

    /// Narrow storage bound for the dependency-free witness produced below.
    /// The 1024-byte header allowance includes every fixed V2/Raw/port field
    /// and six u32 occurrences (at most ten digits each); each permitted action
    /// is below 128 bytes in the explicit codec. Arbitrary Raw cannot use this.
    fn computed_canonical_transport_bound(
        &mut self,
        module: &str,
        span: Span,
        raw: &RawProgram,
    ) -> Result<usize, CompileError> {
        self.compiler.charge(module, span, 12)?;
        macro_rules! refuse {
            () => {
                return Err(self.computed_refusal(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "computed canonical transport is outside its bounded witness shape",
                )?);
            };
        }
        let (
            [input],
            [output],
            [
                RawOp::ComputeUseUncompute {
                    source,
                    source_out,
                    targets,
                    ancilla_wires,
                    function,
                    use_ops,
                },
            ],
        ) = (
            raw.quantum_inputs.as_slice(),
            raw.quantum_outputs.as_slice(),
            raw.operations.as_slice(),
        )
        else {
            refuse!();
        };
        if input.shape != BasisShape::BIT
            || input.wires.len() != 1
            || *source != input.token
            || source_out != output
            || source == source_out
            || !raw.classical_inputs.is_empty()
            || !raw.classical_outputs.is_empty()
            || raw.declared_effect != Effect::Unitary
            || !targets.is_empty()
            || function.as_slice() != [0, 1]
            || ancilla_wires.len() != 1
            || ancilla_wires[0] == input.wires[0]
            || use_ops.len() > 8
        {
            refuse!();
        }
        self.compiler.charge(module, span, use_ops.len())?;
        for usage in use_ops {
            match usage {
                ProtectedUse::ProtectedGate { bit, gate }
                    if bit.region == ProtectedRegion::Ancilla
                        && bit.index == 0
                        && matches!(gate, SingleGate::Z | SingleGate::T) => {}
                ProtectedUse::ControlledPhase {
                    controls,
                    phase: ScalarPhase::MinusOne | ScalarPhase::EighthTurn,
                } if controls.is_empty() => {}
                _ => {
                    refuse!();
                }
            }
        }
        Ok(1024 + use_ops.len() * 128)
    }

    fn computed_use_ops(
        &mut self,
        module: &str,
        span: Span,
        phases: [u8; 2],
    ) -> Result<Vec<ProtectedUse>, CompileError> {
        self.compiler.charge(module, span, 2)?;
        if phases.iter().any(|phase| *phase >= 8) {
            return Err(self.computed_refusal(
                module,
                span,
                ErrorCode::InvalidIr,
                "computed normalization phase is outside the exact eighth-root range",
            )?);
        }
        let scalar = phases[0];
        let relative = (phases[1] + 8 - phases[0]) % 8;
        let count = usize::from(scalar / 4 + scalar % 4 + relative / 4 + relative % 4);
        self.compiler
            .charge(module, span, count.saturating_mul(4).saturating_add(1))?;
        let mut use_ops = Vec::with_capacity(count);
        if scalar >= 4 {
            use_ops.push(ProtectedUse::ControlledPhase {
                controls: vec![],
                phase: ScalarPhase::MinusOne,
            });
        }
        for _ in 0..scalar % 4 {
            use_ops.push(ProtectedUse::ControlledPhase {
                controls: vec![],
                phase: ScalarPhase::EighthTurn,
            });
        }
        let bit = ProtectedBit {
            region: ProtectedRegion::Ancilla,
            index: 0,
        };
        if relative >= 4 {
            use_ops.push(ProtectedUse::ProtectedGate {
                bit,
                gate: SingleGate::Z,
            });
        }
        for _ in 0..relative % 4 {
            use_ops.push(ProtectedUse::ProtectedGate {
                bit,
                gate: SingleGate::T,
            });
        }
        Ok(use_ops)
    }

    /// The canonical mathematical witness executes the exact emitted use list
    /// under identity computation. It adds no source AST or named privilege.
    fn computed_canonical_witness(
        &mut self,
        module: &str,
        span: Span,
        use_ops: &[ProtectedUse],
    ) -> Result<RawProgram, CompileError> {
        let cost = use_ops.iter().fold(24usize, |sum, usage| {
            sum.saturating_add(match usage {
                ProtectedUse::ProtectedGate { .. } => 3,
                ProtectedUse::ControlledPhase { controls, .. }
                | ProtectedUse::ControlledTargetGate { controls, .. } => 3 + controls.len() * 3,
            })
        });
        self.compiler.charge(module, span, cost)?;
        let input = self.token();
        let output = self.token();
        let data = self.wire();
        let ancilla = self.wire();
        Ok(RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: input,
                wires: vec![data],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ComputeUseUncompute {
                source: input,
                source_out: output,
                targets: vec![],
                ancilla_wires: vec![ancilla],
                function: vec![0, 1],
                use_ops: use_ops.to_vec(),
            }],
            quantum_outputs: vec![output],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        })
    }

    fn check_computed_phase_equation(
        &mut self,
        module: &str,
        original: &Expr,
        owner: Key,
        implementation: &AcceptedProgram,
        phases: [u8; 2],
    ) -> Result<(Vec<ProtectedUse>, Arc<SourceUnitaryEquation>), CompileError> {
        let span = original.span;
        let use_ops = self.computed_use_ops(module, span, phases)?;
        let specification = self.computed_canonical_witness(module, span, &use_ops)?;
        self.compiler.charge(module, span, 4)?;
        if let Err(error) = self.compiler.exact_work.charge(4) {
            return Err(self.computed_contract_error(module, span, error.into())?);
        }
        let matrix = match crate::contract::exact::Matrix::new(
            2,
            2,
            vec![
                crate::contract::exact::Exact::phase(i32::from(phases[0])),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::phase(i32::from(phases[1])),
            ],
        ) {
            Ok(matrix) => matrix,
            Err(error) => return Err(self.computed_contract_error(module, span, error.into())?),
        };
        // Both native decisions consume complete encoded Raw, exact ordered Bit
        // ports and the same matrix. No host chunk-composition claim is a seal.
        let implementation = self.computed_unitary_leaf(
            module,
            span,
            ComputedTransport::Original(implementation),
            &matrix,
        )?;
        let specification = self.computed_unitary_leaf(
            module,
            span,
            ComputedTransport::Canonical(&specification),
            &matrix,
        )?;
        let declaration = self.compiler.source.resolution.declaration(owner);
        let name_size = declaration
            .name
            .0
            .len()
            .saturating_add(declaration.name.1.len());
        self.compiler.charge(
            module,
            span,
            name_size.saturating_mul(3).saturating_add(256),
        )?;
        let path = self.compiler.source.resolution.path(owner);
        let names = (
            format!(
                "{path}::with_computed[{}..{}]::original",
                span.start, span.end
            ),
            format!(
                "{path}::with_computed[{}..{}]::diagonal[{},{}]",
                span.start, span.end, phases[0], phases[1]
            ),
        );
        let sources = self.compiler.retained_sources(
            module,
            span,
            &[owner],
            &self.bindings,
            &[
                implementation.program().raw(),
                specification.program().raw(),
            ],
        )?;
        self.compiler.charge(module, span, 1)?;
        let equation =
            match SourceUnitaryEquation::bind(implementation, specification, names, sources) {
                Ok(equation) => equation,
                Err(failure) => {
                    return Err(self.computed_native_error(
                        module,
                        span,
                        "normalization provenance",
                        failure,
                    )?);
                }
            };
        // Resources count the canonical physical use_ops; both receipts retain
        // original proposed work and the exact same canonical protected use.
        Ok((use_ops, Arc::new(equation)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project() -> Project {
        project_source(
            "use std::gate::z;classical fn predicate(b:Bit)->Bit{b}
            unitary fn f(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|h(z(a))}}",
        )
    }

    fn project_source(text: &str) -> Project {
        Project {
            root: PathBuf::from("main.qli"),
            modules: BTreeMap::from([(
                "main".into(),
                SourceModule {
                    name: "main".into(),
                    path: PathBuf::from("main.qli"),
                    source: text.into(),
                    ast: crate::frontend::parser::parse_module(text).unwrap(),
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            )]),
        }
    }

    fn lowerer<'c, 'p>(compiler: &'c mut Compiler<'p>) -> Lowerer<'c, 'p> {
        Lowerer {
            compiler,
            raw: RawState::new(),
            operation_sources: BTreeMap::new(),
            instrument_calls: Vec::new(),
            tuple_binding_origins: vec![BTreeMap::new()],
            access_updates: vec![BTreeSet::new()],
            effect: Effect::Observe,
            contract_effect: Effect::Observe,
            effect_source: Some(("main".into(), Span::default())),
            depth: 0,
            bindings: BTreeMap::new(),
        }
    }

    fn expression(project: &Project) -> &Expr {
        let FnBody::Quantum(body) = &project.modules["main"].ast.decls[1].body else {
            unreachable!()
        };
        &body.result
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn original_computed_body_refuses_foreign_same_span_fields_before_native_use() {
        let project = project();
        let original = expression(&project);
        let ExprKind::WithComputed {
            function,
            binder,
            body,
            ..
        } = &original.kind
        else {
            unreachable!()
        };
        let foreign = original.clone();
        let foreign_function = function.clone();
        let foreign_body = body.clone();
        for (supplied, function, body) in [
            (&foreign, function, body),
            (original, &foreign_function, body),
            (original, function, &foreign_body),
        ] {
            let mut compiler = super::super::call_state_tests::checked_compiler(&project);
            let owner = compiler.source.resolution.qualified("main::f").unwrap();
            compiler.checking = Some(owner);
            let (kernel, log) = compiler.kernel.recording();
            compiler.kernel = kernel;
            let mut lower = lowerer(&mut compiler);
            let before = lower.compiler.work;
            let failure = lower
                .original_computed_body("main", supplied, function, binder, body)
                .unwrap_err();
            assert_eq!(failure.code, ErrorCode::TypeMismatch);
            assert_eq!(failure.span, original.span);
            assert!(lower.compiler.work > before);
            assert_eq!(lower.compiler.checking, Some(owner));
            assert!(lower.compiler.computed_normalizations.is_empty());
            assert!(lower.raw.operations.is_empty());
            assert_eq!(log.summary().decisions(), 0);
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn native_normalization_rejects_same_relative_phase_with_wrong_global_scalar() {
        let project = project_source(
            "use std::gate::z;classical fn predicate(b:Bit)->Bit{b}
            unitary fn f(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|z(a)}}",
        );
        let original = expression(&project);
        let ExprKind::WithComputed { binder, body, .. } = &original.kind else {
            unreachable!()
        };
        let mut compiler = super::super::call_state_tests::checked_compiler(&project);
        let owner = compiler.source.resolution.qualified("main::f").unwrap();
        compiler.checking = Some(owner);
        let mut lower = lowerer(&mut compiler);
        lower.effect = Effect::Unitary;
        lower.contract_effect = Effect::Unitary;
        let wire = lower.wire();
        let ancilla = lower.register(Ty::bit(), vec![wire]);
        let input_slot = lower
            .quantum("main", original.span, &ancilla, true)
            .unwrap();
        let input = lower.raw.registers[&input_slot].token;
        let mut local = Env::new();
        lower.bind_env(binder, Binding::Live(ancilla), &mut local);
        let returned = lower.block("main", body, &mut local).unwrap();
        let returned = lower
            .quantum("main", original.span, &returned, true)
            .unwrap();
        let actual = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: input,
                wires: vec![wire],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations: lower.raw.operations.clone(),
            quantum_outputs: vec![lower.raw.registers[&returned].token],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let checked = lower
            .compiler
            .kernel
            .accept_raw_with_budget(actual, &mut lower.compiler.exact_work)
            .unwrap();
        let before = lower.compiler.exact_work.remaining();
        let error = lower
            .check_computed_phase_equation("main", original, owner, &checked, [4, 0])
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::Contract);
        assert!(error.message.contains("exact equation"));
        assert!(lower.compiler.exact_work.remaining() < before);
        assert!(lower.compiler.computed_normalizations.is_empty());
        assert!(lower.compiler.checked.is_empty());
        assert_eq!(lower.compiler.checking, Some(owner));

        // A source-bound actual body is not enough to bypass shared transport
        // retention/equation work. Refusal precedes a fresh native leaf request
        // and does not restore spent work or produce an inert success receipt.
        let (kernel, log) = lower.compiler.kernel.recording();
        lower.compiler.kernel = kernel;
        lower.compiler.exact_work = crate::contract::exact::Budget::new(0);
        let host_work = lower.compiler.work;
        let error = lower
            .computed_unitary_leaf(
                "main",
                original.span,
                ComputedTransport::Original(&checked),
                &crate::contract::exact::Matrix::identity(2).unwrap(),
            )
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit);
        assert_eq!(lower.compiler.exact_work.remaining(), 0);
        assert!(lower.compiler.work > host_work);
        assert_eq!(log.summary().decisions(), 0);
        assert!(lower.compiler.computed_normalizations.is_empty());
        assert!(lower.compiler.checked.is_empty());
        assert_eq!(lower.compiler.checking, Some(owner));
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn native_canonical_witness_refuses_altered_use_and_owner_frame() {
        let project = project();
        let original = expression(&project);
        let mut compiler = super::super::call_state_tests::checked_compiler(&project);
        let owner = compiler.source.resolution.qualified("main::f").unwrap();
        compiler.checking = Some(owner);
        let mut lower = lowerer(&mut compiler);
        let use_ops = lower
            .computed_use_ops("main", original.span, [1, 1])
            .unwrap();
        let witness = lower
            .computed_canonical_witness("main", original.span, &use_ops)
            .unwrap();
        let required = crate::contract::exact::Matrix::new(
            2,
            2,
            vec![
                crate::contract::exact::Exact::phase(1),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::phase(1),
            ],
        )
        .unwrap();
        for frame_fault in [false, true] {
            let mut altered = witness.clone();
            let RawOp::ComputeUseUncompute {
                ancilla_wires,
                use_ops,
                ..
            } = &mut altered.operations[0]
            else {
                unreachable!()
            };
            if frame_fault {
                ancilla_wires[0] = altered.quantum_inputs[0].wires[0];
            } else {
                use_ops.clear();
            }
            let before = lower.compiler.exact_work.remaining();
            assert!(
                lower
                    .computed_unitary_leaf(
                        "main",
                        original.span,
                        ComputedTransport::Canonical(&altered),
                        &required
                    )
                    .is_err()
            );
            assert!(lower.compiler.exact_work.remaining() <= before);
            if !frame_fault {
                assert!(lower.compiler.exact_work.remaining() < before);
            }
            assert_eq!(lower.compiler.checking, Some(owner));
            assert!(lower.compiler.computed_normalizations.is_empty());
            assert!(lower.compiler.checked.is_empty());
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn canonical_transport_bound_covers_all_eight_actions_and_u32_ids() {
        let project = project();
        let original = expression(&project);
        let mut compiler = super::super::call_state_tests::checked_compiler(&project);
        let owner = compiler.source.resolution.qualified("main::f").unwrap();
        compiler.checking = Some(owner);
        let mut lower = lowerer(&mut compiler);
        let use_ops = lower
            .computed_use_ops("main", original.span, [7, 6])
            .unwrap();
        assert_eq!(use_ops.len(), 8);
        let mut witness = lower
            .computed_canonical_witness("main", original.span, &use_ops)
            .unwrap();
        let input = TokenId(u32::MAX);
        let output = TokenId(u32::MAX - 1);
        witness.quantum_inputs[0].token = input;
        witness.quantum_inputs[0].wires[0] = WireId(u32::MAX);
        witness.quantum_outputs[0] = output;
        let RawOp::ComputeUseUncompute {
            source,
            source_out,
            ancilla_wires,
            ..
        } = &mut witness.operations[0]
        else {
            unreachable!()
        };
        *source = input;
        *source_out = output;
        ancilla_wires[0] = WireId(u32::MAX - 1);
        let meaning = crate::contract::exact::Matrix::new(
            2,
            2,
            vec![
                crate::contract::exact::Exact::phase(7),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::zero(),
                crate::contract::exact::Exact::phase(6),
            ],
        )
        .unwrap();
        let bound = lower
            .computed_canonical_transport_bound("main", original.span, &witness)
            .unwrap();
        let before = lower.compiler.exact_work.remaining();
        let checked = lower
            .computed_unitary_leaf(
                "main",
                original.span,
                ComputedTransport::Canonical(&witness),
                &meaning,
            )
            .unwrap();
        assert!(checked.payload().len() <= bound);
        assert_eq!(checked.program().raw(), &witness);
        assert!(lower.compiler.exact_work.remaining() < before);
        assert_eq!(lower.compiler.checking, Some(owner));
        assert!(lower.compiler.computed_normalizations.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn computed_budget_and_non_diagonal_refusals_restore_effect_frame_without_rewinding() {
        let project = project();
        let original = expression(&project);
        let ExprKind::WithComputed {
            function,
            binder,
            body,
            ..
        } = &original.kind
        else {
            unreachable!()
        };
        let mut allocated_limit = false;
        let mut unsupported = false;
        for allowance in [0, 64, 128, 256, 512, 1024, 2048, 4096, 16384] {
            let mut compiler = super::super::call_state_tests::checked_compiler(&project);
            let owner = compiler.source.resolution.qualified("main::f").unwrap();
            let predicate = compiler
                .source
                .resolution
                .qualified("main::predicate")
                .unwrap();
            let checked_predicate = compiler.compile_basis(&predicate).unwrap();
            compiler.basis.insert(predicate, checked_predicate);
            compiler.checking = Some(owner);
            compiler.work = MAX_WORK - allowance;
            let started = compiler.work;
            let mut lower = lowerer(&mut compiler);
            let source_wire = lower.wire();
            let source = lower.register(Ty::bit(), vec![source_wire]);
            let source_slot = lower
                .quantum("main", original.span, &source, false)
                .unwrap();
            let token = lower.raw.registers[&source_slot].token;
            let origin = lower.effect_source.clone();
            let error = lower
                .computed(
                    "main",
                    original.span,
                    source,
                    function,
                    binder,
                    body,
                    &Env::new(),
                    original,
                )
                .unwrap_err();
            assert_eq!(lower.effect, Effect::Observe);
            assert_eq!(lower.contract_effect, Effect::Observe);
            assert_eq!(lower.effect_source, origin);
            assert_eq!(lower.compiler.checking, Some(owner));
            assert_eq!(lower.depth, 0);
            assert_eq!(lower.access_updates.len(), 1);
            assert_eq!(lower.tuple_binding_origins.len(), 1);
            assert!(lower.compiler.work >= started);
            assert_eq!(lower.raw.registers[&source_slot].token, token);
            assert!(lower.compiler.computed_normalizations.is_empty());
            match error.code {
                ErrorCode::Limit => allocated_limit |= lower.raw.registers.len() > 1,
                ErrorCode::Unsupported => {
                    unsupported = true;
                    assert!(error.message.contains("diagonal"));
                }
                other => panic!("unexpected refusal: {other:?}: {}", error.message),
            }
            let maximum = lower
                .raw
                .registers
                .values()
                .map(|owner| owner.token.0)
                .max()
                .unwrap();
            assert!(lower.token().0 > maximum);
        }
        assert!(
            allocated_limit,
            "exercise refusal after a private ancilla allocation"
        );
        assert!(
            unsupported,
            "exercise full native-checked non-diagonal refusal"
        );
    }
}
