//! Source-bound finite proposals. This adapter supplies no acceptance decision.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::primitive::Primitive;
use super::{ElaboratedProgram, Error, Result, SourceType, SourceValue, Span};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
use crate::frontend::raw_state::{RawState, Slot};
use crate::frontend::types::Kind;
use crate::interchange::finite_leaf::{self, CheckedUnitaryLeaf, UnitaryBoundary};
use crate::interchange::{RootInterface, Version, native};
use crate::ir::{BasisShape, ClassicalId, Effect, QuantumPort, RawProgram, SingleGate};
use std::collections::{BTreeMap, BTreeSet};

mod preservation;

const MAX_OPERATIONS: usize = 10_000;
const MAX_CALLS: usize = 1_024;
const MAX_DEPTH: usize = 16;
const MAX_CELLS: usize = 100_000;
const MAX_LIVE_QUBITS: usize = 16;

/// An immutable finite transport proposal alongside its exact source instance.
///
/// The current adapter supports Unit/Bit/`Q<Unit>`/`Q<Bit>`/products, specialized ordinary
/// calls and the explicitly supported finite primitives. Native Raw validity
/// and source-step correspondence are distinct checks; neither proves source
/// elaboration preserves meaning. Whole argument/result trees remain beside
/// the separate classical SSA and quantum-owner transport interfaces.
#[derive(Clone, Debug)]
pub struct RawSourceProposal {
    source: ElaboratedProgram,
    subject: usize,
    binding: Option<(usize, String)>,
    proposal: native::Proposal,
    finite_boundary: Option<UnitaryBoundary>,
}

/// A fresh native finite equation with replay of these retained source steps.
/// The borrowed immutable source/target identities cannot be substituted.
/// This does not prove original AST-to-step preservation or generic binding.
#[derive(Debug)]
pub struct SourceMeaningCheck<'a> {
    source: &'a RawSourceProposal,
    required: &'a FiniteMeaning,
    leaf: CheckedUnitaryLeaf,
}
impl SourceMeaningCheck<'_> {
    pub fn source(&self) -> &RawSourceProposal {
        self.source
    }
    pub fn required(&self) -> &FiniteMeaning {
        self.required
    }
    pub fn leaf(&self) -> &CheckedUnitaryLeaf {
        &self.leaf
    }
    /// Emit a hierarchy whose actual use of this original binding embeds the
    /// same checked provider bytes and required matrix. The returned artifact
    /// is an untrusted proposal and still requires fresh native checking.
    /// This neither checks all bindings nor enables Meaning-refined admission.
    pub fn lower_hierarchy(&self) -> Result<super::HierarchyProposal> {
        super::lower::lower_with_checked_operation(self)
    }
}
impl RawSourceProposal {
    /// Check the requested exact operator on this actual source-bound artifact,
    /// then independently replay its ordered steps. Only Lean issues the leaf.
    /// Unsupported interfaces reject before any native invocation. This gate
    /// neither enables generic providers nor proves source elaboration sound.
    pub fn check_finite_meaning<'a>(
        &'a self,
        kernel: &native::Kernel,
        required: &'a FiniteMeaning,
        budget: &mut Budget,
    ) -> Result<SourceMeaningCheck<'a>> {
        let root = self.definition();
        let error = |code, message: String| {
            let path = root.path();
            Error::new(code, root.span(), message)
                .in_module(path.rsplit_once("::").map_or(path, |(module, _)| module))
        };
        let boundary = self.finite_boundary.as_ref().ok_or_else(|| {
            error("unsupported", "source Meaning checking requires a unary exact Unit/Bit quantum endomorphism with Unitary effect".into())
        })?;
        if required.signature() != boundary.signature() {
            return Err(error(
                "type",
                "source and requested Meaning have different exact basis trees".into(),
            ));
        }
        if budget.remaining() > DEFAULT_EXACT_WORK {
            return Err(error(
                "limit",
                "source Meaning budget exceeds the shared exact-work ceiling".into(),
            ));
        }
        let matrix = required.matrix(budget).map_err(|e| {
            error(
                if e.is_capacity() { "limit" } else { "meaning" },
                e.to_string(),
            )
        })?;
        let leaf =
            finite_leaf::check_with_kernel(kernel, self.payload(), boundary, &matrix, budget)
                .map_err(|e| error(e.code, e.to_string()))?;
        if leaf.payload() != self.payload() {
            return Err(error(
                "preservation",
                "checked leaf differs from actual source artifact".into(),
            ));
        }
        self.replay(leaf.program().raw())?;
        Ok(SourceMeaningCheck {
            source: self,
            required,
            leaf,
        })
    }
    pub fn source(&self) -> &ElaboratedProgram {
        &self.source
    }
    pub fn proposal(&self) -> &native::Proposal {
        &self.proposal
    }
    pub fn payload(&self) -> &[u8] {
        self.proposal.artifact()
    }
    /// Underlying original definition within the retained caller's source graph.
    /// For a repeated binding, operation() retains the complete wrapper.
    /// The caller's instantiation metadata is never rewritten as leaf metadata.
    pub fn definition(&self) -> &super::SourceDefinition {
        &self.source.definitions()[self.subject]
    }
    pub fn definition_index(&self) -> usize {
        self.subject
    }
    pub fn operation_binding(&self) -> Option<(usize, &str)> {
        self.binding.as_ref().map(|(id, name)| (*id, name.as_str()))
    }
    pub fn operation(&self) -> Option<&super::SourceOperation> {
        let (id, name) = self.operation_binding()?;
        self.source.definitions()[id].operations().get(name)
    }
    fn replay(&self, raw: &RawProgram) -> Result<()> {
        let operation = if let Some((id, name)) = self.operation_binding() {
            Some(
                self.source
                    .definitions()
                    .get(id)
                    .and_then(|d| d.operations().get(name))
                    .ok_or_else(|| {
                        invalid(
                            Span::default(),
                            "original operation binding is absent during replay",
                        )
                    })?,
            )
        } else {
            None
        };
        preservation::validate_subject(&self.source, self.subject, operation, raw)
    }
    /// Compare the actual native-accepted artifact with retained ordered source
    /// steps. This issues no execution handle and proves no AST-to-step theorem.
    /// No independent general source meaning is requested by Raw validity.
    pub fn validate_source_steps(&self, accepted: &native::AcceptedProgram) -> Result<()> {
        if accepted.artifact() != self.payload() || accepted.request().is_some() {
            return Err(Error::new(
                "preservation",
                Span::default(),
                "native accepted artifact differs from the source-bound Raw proposal",
            ));
        }
        self.replay(accepted.raw())
    }
}

fn located(source: &ElaboratedProgram, id: usize, span: Span, message: &str) -> Error {
    let path = source.definitions()[id].path();
    Error::new("unsupported", span, message)
        .in_module(path.rsplit_once("::").map_or(path, |(module, _)| module))
}
fn supported(ty: &SourceType) -> bool {
    match &ty.kind {
        Kind::Unit | Kind::Bit => true,
        Kind::Q(basis) => matches!(basis.kind, Kind::Unit | Kind::Bit),
        Kind::Tuple(fields) => fields.iter().all(supported),
        Kind::Bits(_) | Kind::Parameter(_) => false,
    }
}
fn atom_count(ty: &SourceType) -> usize {
    match &ty.kind {
        Kind::Unit => 0,
        Kind::Bit | Kind::Q(_) => 1,
        Kind::Tuple(fields) => fields.iter().map(atom_count).sum(),
        Kind::Bits(_) | Kind::Parameter(_) => unreachable!("preflighted closed finite source type"),
    }
}
fn effect(source: &ElaboratedProgram, subject: usize) -> Effect {
    match source.definitions()[subject].effect() {
        "unitary" => Effect::Unitary,
        "iso" => Effect::Iso,
        "observe" => Effect::Observe,
        _ => unreachable!("private source effect"),
    }
}
// Exact existing dyadic phase exp(2*pi*i*j/2^k). The source already requires
// canonical j and k <= 8. Raw T realizes only integral multiples of pi/4;
// never round a smaller angle or obtain it by retrying another native request.
fn eighths(ns: &[u32]) -> Option<usize> {
    let [j, k] = ns else {
        return None;
    };
    if *k > 8 {
        return None;
    }
    let denominator = 1u32 << k;
    if *j >= denominator || (j * 8) % denominator != 0 {
        return None;
    }
    Some((j * 8 / denominator) as usize)
}
// Capability selection precedes every emission and native decision.
fn check_profile(source: &ElaboratedProgram, selected: Option<&BTreeSet<usize>>) -> Result<()> {
    for (id, definition) in source.definitions().iter().enumerate() {
        if selected.is_some_and(|selected| !selected.contains(&id)) {
            continue;
        }
        if !definition.operations().is_empty() {
            return Err(located(
                source,
                id,
                definition.span(),
                "finite source lowering does not yet support operation providers",
            ));
        }
        for value in definition.inputs().iter().chain([definition.output()]) {
            if !supported(value.ty()) {
                return Err(located(
                    source,
                    id,
                    definition.span(),
                    "finite source lowering requires Unit, Bit, Q<Unit>, Q<Bit> or exact products; Bits and other quantum bases need explicit target support",
                ));
            }
        }
        for step in definition.steps() {
            if step
                .inputs()
                .iter()
                .chain([step.output()])
                .any(|v| !supported(v.ty()))
            {
                return Err(located(
                    source,
                    id,
                    step.span(),
                    "finite source lowering requires supported intermediate value types",
                ));
            }
            if step.boolean().is_some() {
                continue;
            }
            if step.called_definition().is_some()
                && step.operation_bindings().is_some_and(BTreeMap::is_empty)
            {
                continue;
            }
            match step.primitive_kind() {
                Some(
                    Primitive::H
                    | Primitive::X
                    | Primitive::Cnot
                    | Primitive::Init0
                    | Primitive::MeasureZ
                    | Primitive::PhaseEighth,
                ) => {}
                Some(Primitive::Phase) if eighths(step.natural_arguments()).is_some() => {}
                Some(Primitive::Phase) => {
                    return Err(located(
                        source,
                        id,
                        step.span(),
                        "finite source lowering requires an exact integral eighth-turn phase; this dyadic phase needs its explicit target support",
                    ));
                }
                _ => {
                    return Err(located(
                        source,
                        id,
                        step.span(),
                        "finite source lowering does not yet support this primitive or operation capability",
                    ));
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Atom {
    Classical(ClassicalId),
    Quantum(Slot),
}
type Values = BTreeMap<u32, Atom>;

fn invalid(span: Span, message: &str) -> Error {
    Error::new("preservation", span, message)
}
fn read(value: &SourceValue, values: &mut Values, span: Span) -> Result<Vec<Atom>> {
    match &value.ty().kind {
        Kind::Unit => Ok(vec![]),
        Kind::Bit | Kind::Q(_) => {
            let id = value.identity().expect("source atom identity");
            let atom = if value.ty().is_quantum() {
                values.remove(&id)
            } else {
                values.get(&id).copied()
            }
            .ok_or_else(|| {
                invalid(
                    span,
                    "source atom is absent or its quantum owner was consumed",
                )
            })?;
            Ok(vec![atom])
        }
        Kind::Tuple(_) => {
            let mut atoms = Vec::new();
            for field in value.fields() {
                atoms.extend(read(field, values, span)?);
            }
            Ok(atoms)
        }
        _ => unreachable!("preflighted finite source type"),
    }
}
fn bind(value: &SourceValue, atoms: &[Atom], values: &mut Values, span: Span) -> Result<()> {
    if atoms.len() != atom_count(value.ty()) {
        return Err(invalid(span, "source value changes its exact leaf count"));
    }
    match &value.ty().kind {
        Kind::Unit => {}
        Kind::Bit | Kind::Q(_) => {
            if !matches!(
                (&value.ty().kind, atoms[0]),
                (Kind::Bit, Atom::Classical(_)) | (Kind::Q(_), Atom::Quantum(_))
            ) {
                return Err(invalid(span, "source atom changes its ownership category"));
            }
            if values
                .insert(value.identity().expect("source atom identity"), atoms[0])
                .is_some()
            {
                return Err(invalid(span, "source step redefines a live value identity"));
            }
        }
        Kind::Tuple(_) => {
            let mut offset = 0;
            for field in value.fields() {
                let count = atom_count(field.ty());
                bind(field, &atoms[offset..offset + count], values, span)?;
                offset += count;
            }
        }
        _ => unreachable!("preflighted finite source type"),
    }
    Ok(())
}
fn quantum(atoms: &[Atom], span: Span) -> Result<Slot> {
    match atoms {
        [Atom::Quantum(slot)] => Ok(*slot),
        _ => Err(invalid(span, "quantum primitive requires one owned Q<Bit>")),
    }
}
struct Emitter<'a> {
    source: &'a ElaboratedProgram,
    raw: RawState<u32>,
    calls: usize,
    cells: usize,
}
impl Emitter<'_> {
    fn operation(
        &mut self,
        op: &super::SourceOperation,
        arguments: Vec<Vec<Atom>>,
        depth: usize,
    ) -> Result<Vec<Atom>> {
        if let Some(id) = op.definition() {
            return self.invoke(id, arguments, depth, op.span());
        }
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                op.span(),
                "Raw operation exceeds existing call/depth bounds",
            ));
        }
        let child = op.child().expect("retained repeat child");
        let mut value = arguments
            .into_iter()
            .next()
            .expect("preflighted unary operation");
        for _ in 0..op.repeat_count().expect("retained repeat count") {
            value = self.operation(child, vec![value], depth + 1)?;
        }
        Ok(value)
    }
    fn charge_value(&mut self, value: &SourceValue, span: Span) -> Result<()> {
        self.cells = self
            .cells
            .saturating_add(value.ty().owner_shape_size().nodes);
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 100000 value cells",
            ));
        }
        Ok(())
    }
    fn reserve_operations(&self, n: usize, span: Span) -> Result<()> {
        if self.raw.operations.len().saturating_add(n) > MAX_OPERATIONS {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 10000 operations",
            ));
        }
        Ok(())
    }
    fn reserve_qubit(&self, span: Span) -> Result<()> {
        if self
            .raw
            .registers
            .values()
            .map(|r| r.wires.len())
            .sum::<usize>()
            >= MAX_LIVE_QUBITS
        {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 16 globally live quantum wires",
            ));
        }
        Ok(())
    }
    fn input(&mut self, value: &SourceValue, span: Span) -> Result<Vec<Atom>> {
        match &value.ty().kind {
            Kind::Unit => Ok(vec![]),
            Kind::Bit => Ok(vec![Atom::Classical(self.raw.classical())]),
            Kind::Q(basis) if matches!(basis.kind, Kind::Unit) => Ok(vec![Atom::Quantum(
                self.raw.register(SourceType::unit(), vec![]),
            )]),
            Kind::Q(_) => {
                self.reserve_qubit(span)?;
                let wire = self.raw.wire();
                Ok(vec![Atom::Quantum(
                    self.raw.register(SourceType::bit(), vec![wire]),
                )])
            }
            Kind::Tuple(_) => {
                let mut atoms = Vec::new();
                for field in value.fields() {
                    atoms.extend(self.input(field, span)?);
                }
                Ok(atoms)
            }
            _ => unreachable!("preflighted finite source type"),
        }
    }
    fn invoke(
        &mut self,
        id: usize,
        arguments: Vec<Vec<Atom>>,
        depth: usize,
        call_span: Span,
    ) -> Result<Vec<Atom>> {
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                call_span,
                "finite source lowering exceeds call/depth capacity",
            ));
        }
        let definition = &self.source.definitions()[id];
        let module = definition
            .path()
            .rsplit_once("::")
            .map_or(definition.path(), |(module, _)| module);
        (|| -> Result<Vec<Atom>> {
            // A source-ID environment is local to this activation. Physical owners,
            // pending caller arguments and all fresh supplies stay in shared RawState.
            let mut values = Values::new();
            debug_assert_eq!(arguments.len(), definition.inputs().len());
            for (value, atoms) in definition.inputs().iter().zip(arguments) {
                self.charge_value(value, definition.span())?;
                bind(value, &atoms, &mut values, definition.span())?;
            }
            for step in definition.steps() {
                (|| -> Result<()> {
                    let span = step.span();
                    let mut inputs = vec![];
                    for value in step.inputs() {
                        self.charge_value(value, span)?;
                        inputs.push(read(value, &mut values, span)?);
                    }
                    let state_error = |error: crate::frontend::raw_state::StateError| {
                        invalid(span, &error.to_string()).in_module(step.module())
                    };
                    let output = if let Some(operation) = step.boolean() {
                        let operands = inputs
                            .iter()
                            .map(|atoms| match atoms.as_slice() {
                                [Atom::Classical(id)] => Ok(*id),
                                _ => Err(invalid(
                                    span,
                                    "Boolean source operand is not one ordinary Bit",
                                )),
                            })
                            .collect::<Result<Vec<_>>>()?;
                        self.reserve_operations(1, span)?;
                        vec![Atom::Classical(
                            self.raw
                                .boolean(operation, &operands)
                                .map_err(state_error)?,
                        )]
                    } else if let Some(child) = step.called_definition() {
                        self.invoke(child, inputs, depth + 1, span)?
                    } else {
                        use Primitive::*;
                        match step.primitive_kind().expect("preflighted finite primitive") {
                            Init0 => {
                                self.reserve_operations(1, span)?;
                                self.reserve_qubit(span)?;
                                vec![Atom::Quantum(self.raw.init0())]
                            }
                            H | X => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                let gate = if step.primitive_kind() == Some(H) {
                                    SingleGate::H
                                } else {
                                    SingleGate::X
                                };
                                self.raw.gate_bit(gate, slot).map_err(state_error)?;
                                vec![Atom::Quantum(slot)]
                            }
                            Phase => {
                                let slot = quantum(&inputs[0], span)?;
                                let turns = eighths(step.natural_arguments())
                                    .expect("preflighted exact phase");
                                self.reserve_operations(turns, span)?;
                                for _ in 0..turns {
                                    self.raw
                                        .gate_bit(SingleGate::T, slot)
                                        .map_err(state_error)?;
                                }
                                vec![Atom::Quantum(slot)]
                            }
                            PhaseEighth => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                self.raw.scalar_eighth(slot).map_err(state_error)?;
                                vec![Atom::Quantum(slot)]
                            }
                            Cnot => {
                                let control = quantum(&inputs[0], span)?;
                                let target = quantum(&inputs[1], span)?;
                                self.reserve_operations(1, span)?;
                                self.raw.cnot(control, target).map_err(state_error)?;
                                vec![Atom::Quantum(control), Atom::Quantum(target)]
                            }
                            MeasureZ => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                vec![Atom::Classical(
                                    self.raw.measure_z(slot).map_err(state_error)?,
                                )]
                            }
                            _ => unreachable!("preflighted finite primitive"),
                        }
                    };
                    self.charge_value(step.output(), span)?;
                    bind(step.output(), &output, &mut values, span)?;
                    Ok(())
                })()
                .map_err(|error| error.in_module(step.module()))?;
            }
            self.charge_value(definition.output(), definition.span())?;
            let output = read(definition.output(), &mut values, definition.span())?;
            if values
                .values()
                .any(|value| matches!(value, Atom::Quantum(_)))
            {
                return Err(invalid(
                    definition.span(),
                    "source call drops a quantum owner",
                ));
            }
            Ok(output)
        })()
        .map_err(|error| error.in_module(module))
    }
}

pub(super) fn lower(source: &ElaboratedProgram) -> Result<RawSourceProposal> {
    let root = &source.definitions()[source.root()];
    let module = root
        .path()
        .rsplit_once("::")
        .map_or(root.path(), |(module, _)| module);
    lower_inner(source, source.root(), None, None).map_err(|error| error.in_module(module))
}

pub(super) fn lower_operation(
    source: &ElaboratedProgram,
    caller_id: usize,
    name: &str,
) -> Result<RawSourceProposal> {
    let caller = source.definitions().get(caller_id).ok_or_else(|| {
        invalid(
            Span::default(),
            "operation caller is absent from its original source graph",
        )
    })?;
    let op = caller.operations().get(name).ok_or_else(|| {
        located(
            source,
            caller_id,
            caller.span(),
            "unknown entry operation binding",
        )
    })?;
    let mut base = op;
    let mut depth = 0;
    while let Some(child) = base.child() {
        depth += 1;
        if depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                op.span(),
                "Raw operation exceeds existing depth bound",
            ));
        }
        base = child;
    }
    let subject = base.definition().expect("closed operation base");
    let mut selected = BTreeSet::new();
    let mut pending = vec![subject];
    let mut cells = 1usize;
    while let Some(id) = pending.pop() {
        if !selected.insert(id) {
            continue;
        }
        let definition = source.definitions().get(id).ok_or_else(|| {
            invalid(
                caller.span(),
                "operation subject is absent from its original source graph",
            )
        })?;
        cells = cells.saturating_add(1 + definition.steps().len());
        if cells > MAX_CELLS || selected.len() > MAX_CALLS {
            return Err(Error::new(
                "limit",
                caller.span(),
                "Raw operation dependency selection exceeds existing source budgets",
            ));
        }
        for step in definition.steps() {
            if let Some(child) = step.called_definition() {
                pending.push(child);
            }
        }
    }
    let definition = &source.definitions()[subject];
    if definition.effect() != "unitary"
        || definition.inputs().len() != 1
        || !definition.inputs()[0].ty().is_quantum_owner()
        || definition.inputs()[0].ty() != definition.output().ty()
    {
        return Err(invalid(
            op.span(),
            "operation must preserve one exact quantum owner",
        ));
    }
    let module = definition
        .path()
        .rsplit_once("::")
        .map_or(definition.path(), |(module, _)| module);
    lower_inner(source, subject, Some(&selected), Some((caller_id, name)))
        .map_err(|error| error.in_module(module))
}

fn lower_inner(
    source: &ElaboratedProgram,
    subject: usize,
    selected: Option<&BTreeSet<usize>>,
    binding: Option<(usize, &str)>,
) -> Result<RawSourceProposal> {
    check_profile(source, selected)?;
    let root = &source.definitions()[subject];
    let mut emitter = Emitter {
        source,
        raw: RawState::new(),
        calls: 0,
        cells: 0,
    };
    let mut arguments = vec![];
    for value in root.inputs() {
        emitter.charge_value(value, root.span())?;
        arguments.push(emitter.input(value, root.span())?);
    }
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    for atom in arguments.iter().flatten() {
        match atom {
            Atom::Classical(id) => classical_inputs.push(*id),
            Atom::Quantum(slot) => {
                let register = &emitter.raw.registers[slot];
                quantum_inputs.push(QuantumPort {
                    token: register.token,
                    wires: register.wires.clone(),
                    shape: if register.wires.is_empty() {
                        BasisShape::UNIT
                    } else {
                        BasisShape::BIT
                    },
                });
            }
        }
    }
    let operation = binding.map(|(id, name)| &source.definitions()[id].operations()[name]);
    let outputs = if let Some(op) = operation {
        emitter.operation(op, arguments, 0)?
    } else {
        emitter.invoke(subject, arguments, 0, root.span())?
    };
    let mut quantum_outputs = Vec::new();
    let mut classical_outputs = Vec::new();
    let mut retained = BTreeSet::new();
    for atom in outputs {
        match atom {
            Atom::Classical(id) => classical_outputs.push(id),
            Atom::Quantum(slot) => {
                if !retained.insert(slot) {
                    return Err(invalid(
                        root.span(),
                        "source result duplicates a quantum owner",
                    ));
                }
                let register = emitter.raw.registers.get(&slot).ok_or_else(|| {
                    invalid(
                        root.span(),
                        "source result contains a consumed quantum owner",
                    )
                })?;
                quantum_outputs.push(register.token);
            }
        }
    }
    if retained.len() != emitter.raw.registers.len() {
        return Err(invalid(
            root.span(),
            "source result drops a globally live quantum owner",
        ));
    }
    let raw = RawProgram {
        quantum_inputs,
        classical_inputs,
        operations: emitter.raw.operations,
        quantum_outputs,
        classical_outputs,
        declared_effect: effect(source, subject),
    };
    preservation::validate_subject(source, subject, operation, &raw)?;
    // A finite request binds the actual artifact's declared type as well as
    // its ports. Retain a unary quantum boundary only for an exact matching
    // source tree; zero width alone never establishes a Unit signature.
    let interface = match root.inputs() {
        [input] if input.ty() == root.output().ty() => match &input.ty().kind {
            Kind::Q(basis) => match basis.kind {
                Kind::Unit => Some(BasisType::Unit),
                Kind::Bit => Some(BasisType::Bit),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
    .map(|basis| RootInterface {
        input: basis.clone(),
        output: basis,
    });
    let proposal = native::Proposal::from_raw(&raw, interface.as_ref(), Version::V2, None)
        .map_err(|error| Error::new("transport", root.span(), error.to_string()))?;
    let finite_boundary =
        if raw.declared_effect == Effect::Unitary {
            if let Some(interface) = interface {
                // This exact unary source result has one globally live register.
                // Use its actual returned wire order, never just the input width.
                if raw.quantum_inputs.len() != 1
                    || raw.quantum_outputs.len() != 1
                    || emitter.raw.registers.len() != 1
                {
                    return Err(invalid(
                        root.span(),
                        "unary source boundary has a different owner frame",
                    ));
                }
                let output =
                    emitter.raw.registers.values().next().ok_or_else(|| {
                        invalid(root.span(), "missing unary source output register")
                    })?;
                Some(
                    UnitaryBoundary::new(
                        interface.input,
                        raw.quantum_inputs[0].clone(),
                        QuantumPort {
                            token: output.token,
                            wires: output.wires.clone(),
                            shape: if output.wires.is_empty() {
                                BasisShape::UNIT
                            } else {
                                BasisShape::BIT
                            },
                        },
                    )
                    .map_err(|e| invalid(root.span(), &e.to_string()))?,
                )
            } else {
                None
            }
        } else {
            None
        };
    Ok(RawSourceProposal {
        source: source.clone(),
        subject,
        binding: binding.map(|(id, name)| (id, name.into())),
        proposal,
        finite_boundary,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;
    use crate::ir::RawOp;

    #[test]
    fn checked_operation_bytes_are_used_by_the_actual_emitted_hierarchy() {
        use crate::frontend::sized::{BasisBinding, OperationBinding};
        use crate::interchange::{hierarchical, json};
        use hierarchical::execution::ExecutionLimits;
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(),
            "use std::quantum::{x,phase_eighth}; pub unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub unitary fn scalar(q:Q<Unit>)->Q<Unit>{phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))} unitary fn inner[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U){U(q)} pub unitary fn outer[static A:Basis,static k:Nat,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U),k<=2{inner[A,repeat_op(k,U)](q)}".into())])).unwrap();
        let executable = std::env::var_os("QLEISLI_KERNEL").expect("matching native checker");
        let checker = native::Kernel::new(executable.clone());
        let hierarchy_checker = hierarchical::Kernel::new(executable);
        for (basis, provider) in [("Bit", "main::flip"), ("Unit", "main::scalar")] {
            for count in 0..=2 {
                let source = parsed
                    .instantiate_with_types(
                        "main::outer",
                        BTreeMap::from([("A".into(), BasisBinding::parse(basis).unwrap())]),
                        BTreeMap::from([("k".into(), count)]),
                        BTreeMap::from([(
                            "U".into(),
                            OperationBinding::new(provider, BTreeMap::new()),
                        )]),
                    )
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let caller = source
                    .definitions()
                    .iter()
                    .position(|d| d.path() == "main::inner")
                    .unwrap();
                let leaf = source.lower_raw_operation_at(caller, "U").unwrap();
                let required = if basis == "Bit" {
                    FiniteMeaning::permutation(
                        BasisType::Bit,
                        if count == 1 { vec![1, 0] } else { vec![0, 1] },
                    )
                    .unwrap()
                } else {
                    FiniteMeaning::phase(BasisType::Unit, vec![if count == 1 { 4 } else { 0 }])
                        .unwrap()
                };
                let checked = leaf
                    .check_finite_meaning(&checker, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let proposal = checked.lower_hierarchy().unwrap();
                let graph = json::parse(proposal.payload()).unwrap();
                let definitions = graph.field("definitions").unwrap().array().unwrap();
                assert!(
                    definitions.iter().any(|d| {
                        let body = d.field("body").unwrap();
                        body.field("tag").unwrap().text().unwrap() == "leaf"
                            && body.field("program").unwrap().text().unwrap().as_bytes()
                                == checked.leaf().payload()
                    }),
                    "actual provider bytes must be in the emitted artifact"
                );
                let actual = hierarchy_checker
                    .check_against_native(proposal.payload(), proposal.comparison_request())
                    .unwrap();
                let input = if basis == "Bit" {
                    vec![[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]]
                } else {
                    vec![[0.1, -0.2], [0.3, 0.4]]
                };
                let output = actual
                    .execute_pure(
                        &input,
                        2,
                        ExecutionLimits {
                            max_amplitudes: 16,
                            max_steps: 1000,
                        },
                    )
                    .unwrap()
                    .amplitudes;
                let expected = if basis == "Bit" {
                    (0..input.len())
                        .map(|i| input[i ^ (if count == 1 { 1 } else { 0 })])
                        .collect::<Vec<_>>()
                } else {
                    input
                        .iter()
                        .map(|[a, b]| if count == 1 { [-a, -b] } else { [*a, *b] })
                        .collect()
                };
                for (a, b) in output.iter().flatten().zip(expected.iter().flatten()) {
                    assert!((a - b).abs() < 1e-12, "{basis}, {count}");
                }
                assert_eq!(output.len(), expected.len());
                if basis == "Bit" && count == 2 {
                    // Keep the actual input/output frame, but substitute a
                    // native-valid single X for the checked X^2 body. The
                    // emitted matrix request must reject the new artifact.
                    let mut wrong = checked.leaf().program().raw().clone();
                    wrong.operations.remove(0);
                    let RawOp::Gate { input, .. } = &mut wrong.operations[0] else {
                        panic!("X gate")
                    };
                    *input = wrong.quantum_inputs[0].token;
                    let wrong = native::Proposal::from_raw(
                        &wrong,
                        Some(&RootInterface {
                            input: BasisType::Bit,
                            output: BasisType::Bit,
                        }),
                        Version::V2,
                        None,
                    )
                    .unwrap();
                    checker.accept(&wrong).unwrap();
                    let mut changed = json::parse(proposal.payload()).unwrap();
                    let json::Value::Object(root) = &mut changed else {
                        panic!("graph")
                    };
                    let json::Value::Array(definitions) = root.get_mut("definitions").unwrap()
                    else {
                        panic!("definitions")
                    };
                    let mut replaced = 0;
                    for definition in definitions {
                        let json::Value::Object(fields) = definition else {
                            panic!("definition")
                        };
                        let json::Value::Object(body) = fields.get_mut("body").unwrap() else {
                            panic!("body")
                        };
                        if body.get("program")
                            == Some(&json::Value::String(
                                std::str::from_utf8(checked.leaf().payload())
                                    .unwrap()
                                    .into(),
                            ))
                        {
                            body.insert(
                                "program".into(),
                                json::Value::String(
                                    std::str::from_utf8(wrong.artifact()).unwrap().into(),
                                ),
                            );
                            replaced += 1;
                        }
                    }
                    assert_eq!(replaced, 1);
                    let error = hierarchy_checker
                        .check_against_native(
                            &json::encode(&changed).unwrap(),
                            proposal.comparison_request(),
                        )
                        .unwrap_err();
                    assert_eq!(error.code, "contract", "{error}");
                }
            }
        }
    }

    #[test]
    fn repeated_subject_replay_rejects_its_native_valid_base_artifact() {
        use crate::frontend::sized::OperationBinding;
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(),
            "use std::quantum::x; pub unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} unitary fn inner[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q} pub unitary fn outer[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){inner[repeat_op(2,U)](q)}".into())]))
            .unwrap().instantiate("main::outer", BTreeMap::new(), BTreeMap::from([("U".into(), OperationBinding::new("main::flip", BTreeMap::new()))])).unwrap().elaborate().unwrap();
        let caller = source
            .definitions()
            .iter()
            .position(|d| d.path() == "main::inner")
            .unwrap();
        let mut repeated = source.lower_raw_operation_at(caller, "U").unwrap();
        let base = source.lower_raw_operation("U").unwrap();
        // Model a producer substituting both valid bytes and a matching port
        // boundary. Its claim still must replay the retained X^2 subject.
        repeated.proposal = base.proposal;
        repeated.finite_boundary = base.finite_boundary;
        let required = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0]).unwrap();
        let checker = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("matching native checker"),
        );
        finite_leaf::check_with_kernel(
            &checker,
            repeated.payload(),
            repeated.finite_boundary.as_ref().unwrap(),
            &required
                .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let error = repeated
            .check_finite_meaning(&checker, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err();
        assert_eq!(error.code(), "preservation", "{error}");
    }

    #[test]
    fn source_meaning_gate_rejects_a_native_valid_replaced_provider() {
        let source = ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "use std::quantum::x; pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}".into(),
        )]))
        .unwrap()
        .instantiate("main::implementation", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
        let mut proposal = source.lower_raw().unwrap();
        let required = FiniteMeaning::permutation(BasisType::Bit, vec![0, 1]).unwrap();
        proposal.proposal = native::Proposal::from_raw(
            &required.target_ir().unwrap(),
            Some(&RootInterface {
                input: BasisType::Bit,
                output: BasisType::Bit,
            }),
            Version::V2,
            None,
        )
        .unwrap();
        let kernel = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("matching native checker"),
        );
        let matrix = required
            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        // The replacement even satisfies its own requested equation. This
        // cannot establish correspondence to the retained X source steps.
        finite_leaf::check_with_kernel(
            &kernel,
            proposal.payload(),
            proposal.finite_boundary.as_ref().unwrap(),
            &matrix,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let error = proposal
            .check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err();
        assert_eq!(error.code(), "preservation", "{error}");
    }

    fn example() -> ElaboratedProgram {
        ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "unitary fn f((a,b): (Bit,Bit)) -> (Bit,Bit,Bit) { (not a, a and b, a xor b) }\n\
             pub observe fn main() -> (Bit,Bit,Bit) { f((1,1)) }"
                .into(),
        )]))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
    }

    #[test]
    fn raw_source_replay_rejects_native_valid_semantic_and_structural_mutations() {
        let source = example();
        let proposal = source.lower_raw().unwrap();
        let kernel = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("select the matching native checker"),
        );
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let original = accepted.raw();
        let mut mutations = vec![];
        let mut changed = original.clone();
        let index = changed
            .operations
            .iter()
            .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
            .unwrap();
        let RawOp::ClassicalAnd {
            left,
            right,
            output,
        } = &changed.operations[index]
        else {
            unreachable!()
        };
        changed.operations[index] = RawOp::ClassicalXor {
            left: *left,
            right: *right,
            output: *output,
        };
        mutations.push(("and changed to xor", changed));

        let mut changed = original.clone();
        let RawOp::ClassicalConst { value, .. } = &mut changed.operations[0] else {
            unreachable!()
        };
        *value = !*value;
        mutations.push(("literal substituted", changed));

        let mut changed = original.clone();
        changed.operations.push(RawOp::ClassicalConst {
            value: true,
            output: ClassicalId(900),
        });
        mutations.push(("extra unused operation", changed));

        let mut changed = original.clone();
        changed.classical_outputs.reverse();
        mutations.push(("output order reversed", changed));

        for (name, raw) in mutations {
            let accepted_mutation = kernel.accept_raw(raw).expect(name);
            // Exercise the direct opcode/tree matcher, not just the proposal's
            // outer byte-identity check. These programs remain native-valid.
            let error = preservation::validate(&source, accepted_mutation.raw()).expect_err(name);
            assert_eq!(error.code(), "preservation", "{name}: {error}");
            assert!(
                proposal.validate_source_steps(&accepted_mutation).is_err(),
                "{name}"
            );
        }
    }
}
