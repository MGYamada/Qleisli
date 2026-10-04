//! Source-bound finite proposals. This adapter supplies no acceptance decision.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::primitive::Primitive;
use super::{ElaboratedProgram, Error, Result, SourceType, SourceValue, Span};
use crate::frontend::raw_state::{RawState, Slot};
use crate::frontend::types::Kind;
use crate::interchange::{Version, native};
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
/// The current adapter supports Unit/Bit/Q<Bit>/products, specialized ordinary
/// calls and the explicitly supported finite primitives. Native Raw validity
/// and source-step correspondence are distinct checks; neither proves source
/// elaboration preserves meaning. Whole argument/result trees remain beside
/// the separate classical SSA and quantum-owner transport interfaces.
#[derive(Clone, Debug)]
pub struct RawSourceProposal {
    source: ElaboratedProgram,
    proposal: native::Proposal,
}
impl RawSourceProposal {
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
        Kind::Q(basis) => matches!(basis.kind, Kind::Bit),
        Kind::Tuple(fields) => fields.iter().all(supported),
        Kind::Bits(_) => false,
    }
}
fn atom_count(ty: &SourceType) -> usize {
    match &ty.kind {
        Kind::Unit => 0,
        Kind::Bit | Kind::Q(_) => 1,
        Kind::Tuple(fields) => fields.iter().map(atom_count).sum(),
        Kind::Bits(_) => unreachable!("preflighted finite source type"),
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
                    "finite source lowering requires Unit, Bit, Q<Bit> or exact products; Bits and other quantum bases need explicit target support",
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
                    | Primitive::MeasureZ,
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
        if self.raw.registers.len() >= MAX_LIVE_QUBITS {
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
                    shape: BasisShape::BIT,
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
    let proposal = native::Proposal::from_raw(&raw, None, Version::V2, None)
        .map_err(|error| Error::new("transport", root.span(), error.to_string()))?;
    Ok(RawSourceProposal {
        source: source.clone(),
        proposal,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;
    use crate::ir::RawOp;

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
