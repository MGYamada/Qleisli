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
        let root = &self.source.definitions()[self.source.root()];
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
        preservation::validate(&self.source, leaf.program().raw())?;
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
        preservation::validate(&self.source, accepted.raw())
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
fn effect(source: &ElaboratedProgram) -> Effect {
    match source.definitions()[source.root()].effect() {
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
fn check_profile(source: &ElaboratedProgram) -> Result<()> {
    for (id, definition) in source.definitions().iter().enumerate() {
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
    lower_inner(source).map_err(|error| error.in_module(module))
}

fn lower_inner(source: &ElaboratedProgram) -> Result<RawSourceProposal> {
    check_profile(source)?;
    let root = &source.definitions()[source.root()];
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
    let outputs = emitter.invoke(source.root(), arguments, 0, root.span())?;
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
        declared_effect: effect(source),
    };
    preservation::validate(source, &raw)?;
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
