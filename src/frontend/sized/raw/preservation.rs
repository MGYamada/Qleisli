//! Independent comparison of a retained source-step graph with Raw IR.
//! This untrusted check issues neither native acceptance nor a source theorem.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use crate::frontend::ordinary::Boolean;
use crate::frontend::sized::primitive::Primitive;
use crate::frontend::sized::{
    ElaboratedProgram, Error, Result, SourceDefinition, SourceStep, SourceType, SourceValue, Span,
};
use crate::frontend::types::Kind;
use crate::ir::{BasisShape, ClassicalId, Effect, RawOp, RawProgram, SingleGate, TokenId, WireId};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CALLS: usize = 1024;
const MAX_DEPTH: usize = 16;
const MAX_STEPS: usize = 10_000;
const MAX_CELLS: usize = 100_000;
const MAX_LIVE: usize = 16;

#[derive(Clone, Copy)]
struct Site<'a> {
    module: &'a str,
    span: Span,
}
impl<'a> Site<'a> {
    fn definition(definition: &'a SourceDefinition) -> Self {
        Self {
            module: definition
                .path()
                .rsplit_once("::")
                .map_or(definition.path(), |(module, _)| module),
            span: definition.span(),
        }
    }
    fn error(self, code: &'static str, message: impl Into<String>) -> Error {
        Error::new(code, self.span, message).in_module(self.module)
    }
    fn invalid(self, message: impl Into<String>) -> Error {
        self.error("preservation", message)
    }
}

fn effect(name: &str, site: Site<'_>) -> Result<Effect> {
    match name {
        "unitary" => Ok(Effect::Unitary),
        "iso" => Ok(Effect::Iso),
        "observe" => Ok(Effect::Observe),
        _ => Err(site.invalid("unknown source effect")),
    }
}

fn quantum_bit(ty: &SourceType) -> bool {
    matches!(&ty.kind, Kind::Q(basis) if matches!(basis.kind, Kind::Bit))
}

fn quantum_width(ty: &SourceType) -> Option<usize> {
    match &ty.kind {
        Kind::Q(basis) => match basis.kind {
            Kind::Unit => Some(0),
            Kind::Bit => Some(1),
            _ => None,
        },
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Atom {
    Classical(ClassicalId),
    Quantum(TokenId, Option<WireId>),
}

#[derive(Default)]
struct Environment {
    values: BTreeMap<u32, Atom>,
    // Consuming a quantum value must not permit redefinition of its source ID.
    issued: BTreeSet<u32>,
    quantum: BTreeSet<TokenId>,
}

struct Argument<'a> {
    ty: &'a SourceType,
    atoms: Vec<Atom>,
}

struct Replay<'a> {
    source: &'a ElaboratedProgram,
    raw: &'a RawProgram,
    cursor: usize,
    calls: usize,
    steps: usize,
    cells: usize,
    classical: BTreeSet<ClassicalId>,
    tokens: BTreeSet<TokenId>,
    wires: BTreeSet<WireId>,
    live: BTreeMap<TokenId, Option<WireId>>,
}

impl Replay<'_> {
    fn charge(&mut self, count: usize, site: Site<'_>) -> Result<()> {
        self.cells = self.cells.saturating_add(count);
        if self.cells > MAX_CELLS {
            return Err(site.error("limit", "Raw replay exceeds 100000 value cells"));
        }
        Ok(())
    }

    /// Exact source constructors, including ordinary Unit versus zero-width
    /// owners/registers. Charge pending children before extending the stack.
    fn atoms(&mut self, value: &SourceValue, site: Site<'_>) -> Result<Vec<(u32, Option<usize>)>> {
        self.charge(1, site)?;
        let mut pending = vec![(value, value.ty(), 0usize)];
        let mut result = Vec::new();
        while let Some((value, expected, depth)) = pending.pop() {
            if depth > 64 {
                return Err(site.error("limit", "Raw replay exceeds its value-depth bound"));
            }
            if value.ty() != expected {
                return Err(site.invalid("source value field differs from its exact type tree"));
            }
            match &expected.kind {
                Kind::Unit => {
                    if value.identity().is_some() || !value.fields().is_empty() {
                        return Err(site.invalid("ordinary Unit has an identity or fields"));
                    }
                }
                Kind::Bit | Kind::Q(_)
                    if matches!(expected.kind, Kind::Bit) || quantum_width(expected).is_some() =>
                {
                    if !value.fields().is_empty() {
                        return Err(site.invalid("source atom has product fields"));
                    }
                    result.push((
                        value
                            .identity()
                            .ok_or_else(|| site.invalid("source atom lacks its identity"))?,
                        quantum_width(expected),
                    ));
                }
                Kind::Tuple(fields) => {
                    if value.identity().is_some()
                        || fields.is_empty()
                        || fields.len() != value.fields().len()
                    {
                        return Err(site
                            .invalid("source product loses its exact arity or identity boundary"));
                    }
                    self.charge(fields.len(), site)?;
                    pending.extend(
                        value
                            .fields()
                            .iter()
                            .zip(fields)
                            .rev()
                            .map(|(value, ty)| (value, ty, depth + 1)),
                    );
                }
                Kind::Bit | Kind::Bits(_) | Kind::Q(_) | Kind::Parameter(_) => {
                    return Err(site.error(
                        "unsupported",
                        "Raw replay supports only Unit, Bit, Q<Unit>, Q<Bit> and their exact products",
                    ));
                }
            }
        }
        Ok(result)
    }

    fn bind(
        &mut self,
        value: &SourceValue,
        actual: &[Atom],
        environment: &mut Environment,
        site: Site<'_>,
    ) -> Result<()> {
        let atoms = self.atoms(value, site)?;
        if atoms.len() != actual.len() {
            return Err(site.invalid("Raw values differ from the source value's leaf count"));
        }
        for ((source, quantum), actual) in atoms.into_iter().zip(actual) {
            if quantum.is_some() != matches!(actual, Atom::Quantum(..))
                || !environment.issued.insert(source)
            {
                return Err(site.invalid(
                    "source step changes leaf ownership kind or redefines a local identity",
                ));
            }
            match actual {
                Atom::Quantum(token, wire) => {
                    if quantum != Some(usize::from(wire.is_some()))
                        || self.live.get(token) != Some(wire)
                        || !environment.quantum.insert(*token)
                    {
                        return Err(
                            site.invalid("source binding aliases or loses a live quantum owner")
                        );
                    }
                }
                Atom::Classical(id) if !self.classical.contains(id) => {
                    return Err(site.invalid("source binding names an unissued classical value"));
                }
                Atom::Classical(_) => {}
            }
            environment.values.insert(source, *actual);
        }
        Ok(())
    }

    fn read(
        &mut self,
        value: &SourceValue,
        environment: &mut Environment,
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let mut result = Vec::new();
        for (id, quantum) in self.atoms(value, site)? {
            let actual = environment
                .values
                .get(&id)
                .copied()
                .ok_or_else(|| site.invalid("source step uses an unavailable value"))?;
            if quantum.is_some() != matches!(actual, Atom::Quantum(..)) {
                return Err(site.invalid("source read changes a leaf's ownership kind"));
            }
            if let Atom::Quantum(token, wire) = actual {
                if quantum != Some(usize::from(wire.is_some()))
                    || self.live.get(&token) != Some(&wire)
                    || !environment.quantum.remove(&token)
                {
                    return Err(site.invalid("source read reuses a consumed quantum owner"));
                }
                environment.values.remove(&id);
            }
            result.push(actual);
        }
        Ok(result)
    }

    fn fresh_classical(&mut self, output: ClassicalId, site: Site<'_>) -> Result<()> {
        if !self.classical.insert(output) {
            return Err(site.invalid("Raw output reuses an issued classical identity"));
        }
        Ok(())
    }

    fn introduce(
        &mut self,
        token: TokenId,
        wire: WireId,
        fresh_wire: bool,
        site: Site<'_>,
    ) -> Result<Atom> {
        self.introduce_owner(token, Some(wire), fresh_wire, site)
    }

    fn introduce_owner(
        &mut self,
        token: TokenId,
        wire: Option<WireId>,
        fresh_wire: bool,
        site: Site<'_>,
    ) -> Result<Atom> {
        self.charge(1, site)?;
        if wire.is_some() && self.live.values().filter(|wire| wire.is_some()).count() >= MAX_LIVE {
            return Err(site.error("limit", "Raw replay exceeds 16 globally live quantum wires"));
        }
        if !self.tokens.insert(token)
            || (fresh_wire && wire.is_some_and(|wire| !self.wires.insert(wire)))
        {
            return Err(site.invalid("Raw operation reuses an issued token or wire"));
        }
        if wire.is_some() && self.live.values().any(|existing| *existing == wire) {
            return Err(site.invalid("Raw operation aliases a live wire"));
        }
        self.live.insert(token, wire);
        Ok(Atom::Quantum(token, wire))
    }

    fn quantum(input: &Argument<'_>, site: Site<'_>) -> Result<(TokenId, WireId)> {
        match input.atoms.as_slice() {
            [Atom::Quantum(token, Some(wire))] if quantum_bit(input.ty) => Ok((*token, *wire)),
            _ => Err(site.invalid("primitive requires one exact Q<Bit> argument")),
        }
    }

    fn remove(&mut self, token: TokenId, wire: WireId, site: Site<'_>) -> Result<()> {
        if self.live.remove(&token) != Some(Some(wire)) {
            return Err(site.invalid("Raw instruction consumes an unavailable quantum owner"));
        }
        Ok(())
    }

    fn gate(
        &mut self,
        input: (TokenId, WireId),
        expected: SingleGate,
        site: Site<'_>,
    ) -> Result<Atom> {
        let Some(RawOp::Gate {
            gate,
            input: token,
            output,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("Raw program omits the source's single-qubit gate"));
        };
        if *gate != expected || *token != input.0 {
            return Err(site.invalid("Raw gate or operand differs from the source step"));
        }
        let output = *output;
        self.remove(input.0, input.1, site)?;
        let atom = self.introduce(output, input.1, false, site)?;
        self.cursor += 1;
        Ok(atom)
    }

    fn boolean(
        &mut self,
        operation: Boolean,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<Atom> {
        let mut bits = Vec::new();
        for input in inputs {
            match input.atoms.as_slice() {
                [Atom::Classical(id)] if matches!(input.ty.kind, Kind::Bit) => bits.push(*id),
                _ => return Err(site.invalid("Boolean source step has a non-Bit operand")),
            }
        }
        let actual = self
            .raw
            .operations
            .get(self.cursor)
            .ok_or_else(|| site.invalid("Raw program omits a Boolean source step"))?;
        // Read opcodes and operands directly, independently of the emitter.
        let output = match (operation, bits.as_slice(), actual) {
            (Boolean::Constant(expected), [], RawOp::ClassicalConst { value, output })
                if expected == *value =>
            {
                *output
            }
            (
                Boolean::Not,
                [input],
                RawOp::ClassicalNot {
                    input: actual,
                    output,
                },
            ) if input == actual => *output,
            (
                Boolean::And,
                [a, b],
                RawOp::ClassicalAnd {
                    left,
                    right,
                    output,
                },
            ) if a == left && b == right => *output,
            (
                Boolean::Xor,
                [a, b],
                RawOp::ClassicalXor {
                    left,
                    right,
                    output,
                },
            ) if a == left && b == right => *output,
            _ => {
                return Err(
                    site.invalid("Raw Boolean instruction differs from the original source step")
                );
            }
        };
        self.fresh_classical(output, site)?;
        self.cursor += 1;
        Ok(Atom::Classical(output))
    }

    fn primitive(
        &mut self,
        kind: Primitive,
        step: &SourceStep,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let required = match kind {
            Primitive::H | Primitive::X | Primitive::Cnot | Primitive::Phase => Effect::Unitary,
            Primitive::Init0 => Effect::Iso,
            Primitive::MeasureZ => Effect::Observe,
            _ => {
                return Err(site.error(
                    "unsupported",
                    "Raw replay does not support this primitive or operation capability",
                ));
            }
        };
        if effect(step.effect(), site)? != required
            || (kind != Primitive::Phase && !step.natural_arguments().is_empty())
        {
            return Err(site.invalid(
                "primitive effect or natural arguments differ from its source signature",
            ));
        }
        match (kind, inputs) {
            (Primitive::H | Primitive::X, [input]) if quantum_bit(step.output().ty()) => {
                let input = Self::quantum(input, site)?;
                let gate = if kind == Primitive::H {
                    SingleGate::H
                } else {
                    SingleGate::X
                };
                Ok(vec![self.gate(input, gate, site)?])
            }
            (Primitive::Phase, [input]) if quantum_bit(step.output().ty()) => {
                let mut input = Self::quantum(input, site)?;
                let [j, k] = step.natural_arguments() else {
                    return Err(site.invalid("phase source step has wrong natural arity"));
                };
                // Preserve the elaborator's domain; do not normalize an invalid j.
                if *k > 8 || *j >= (1u32 << *k) {
                    return Err(site.error("unsupported", "phase requires k <= 8 and j < 2^k"));
                }
                let denominator = 1u32 << *k;
                let numerator = (*j % denominator) * 8;
                if numerator % denominator != 0 {
                    return Err(site.error(
                        "unsupported",
                        "Raw replay requires an exact eighth-turn phase",
                    ));
                }
                for _ in 0..numerator / denominator {
                    let Atom::Quantum(token, Some(wire)) = self.gate(input, SingleGate::T, site)?
                    else {
                        unreachable!("gate returns a quantum atom")
                    };
                    input = (token, wire);
                }
                Ok(vec![Atom::Quantum(input.0, Some(input.1))])
            }
            (Primitive::Cnot, [control, target]) if matches!(&step.output().ty().kind, Kind::Tuple(fields) if fields.len() == 2 && fields.iter().all(quantum_bit)) =>
            {
                let control = Self::quantum(control, site)?;
                let target = Self::quantum(target, site)?;
                let Some(RawOp::Cnot {
                    control: c,
                    target: t,
                    control_out,
                    target_out,
                }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source CNOT"));
                };
                if *c != control.0
                    || *t != target.0
                    || control.0 == target.0
                    || control.1 == target.1
                {
                    return Err(site.invalid("Raw CNOT changes or aliases its ordered operands"));
                }
                let (c, t) = (*control_out, *target_out);
                self.remove(control.0, control.1, site)?;
                self.remove(target.0, target.1, site)?;
                let outputs = vec![
                    self.introduce(c, control.1, false, site)?,
                    self.introduce(t, target.1, false, site)?,
                ];
                self.cursor += 1;
                Ok(outputs)
            }
            (Primitive::Init0, []) if quantum_bit(step.output().ty()) => {
                let Some(RawOp::Init0 { output, wire }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source initialization"));
                };
                let (output, wire) = (*output, *wire);
                let atom = self.introduce(output, wire, true, site)?;
                self.cursor += 1;
                Ok(vec![atom])
            }
            (Primitive::MeasureZ, [input]) if matches!(step.output().ty().kind, Kind::Bit) => {
                let input = Self::quantum(input, site)?;
                let Some(RawOp::MeasureZ {
                    input: actual,
                    output,
                }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source measurement"));
                };
                if *actual != input.0 {
                    return Err(site.invalid("Raw measurement changes its source owner"));
                }
                let output = *output;
                self.remove(input.0, input.1, site)?;
                self.fresh_classical(output, site)?;
                self.cursor += 1;
                Ok(vec![Atom::Classical(output)])
            }
            _ => Err(site
                .invalid("primitive source step changes its whole arguments or exact result type")),
        }
    }

    fn function(
        &mut self,
        id: usize,
        arguments: &[Argument<'_>],
        depth: usize,
        call_site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(call_site.error("limit", "Raw replay exceeds its call/depth bound"));
        }
        let source = self.source;
        let definition = source
            .definitions()
            .get(id)
            .ok_or_else(|| call_site.invalid("source call refers to a missing definition"))?;
        let site = Site::definition(definition);
        let declared = effect(definition.effect(), site)?;
        if !definition.operations().is_empty() {
            return Err(site.error(
                "unsupported",
                "Raw replay does not support operation providers",
            ));
        }
        if arguments.len() != definition.inputs().len() {
            return Err(call_site.invalid("source call changes whole-argument arity"));
        }
        let mut environment = Environment::default();
        for (input, actual) in definition.inputs().iter().zip(arguments) {
            if input.ty() != actual.ty {
                return Err(call_site.invalid("source call changes an argument's exact type tree"));
            }
            self.bind(input, &actual.atoms, &mut environment, site)?;
        }
        // At most 16 live owners: capture the actual suspended caller frame,
        // without assuming those wires are separable from this call's inputs.
        self.charge(self.live.len(), site)?;
        let suspended: BTreeMap<_, _> = self
            .live
            .iter()
            .filter(|(token, _)| !environment.quantum.contains(token))
            .map(|(t, w)| (*t, *w))
            .collect();
        for step in definition.steps() {
            self.steps += 1;
            let site = Site {
                module: step.module(),
                span: step.span(),
            };
            if self.steps > MAX_STEPS {
                return Err(site.error("limit", "Raw replay exceeds 10000 source steps"));
            }
            let step_effect = effect(step.effect(), site)?;
            if step_effect > declared {
                return Err(site.invalid("source step exceeds its declaration's effect"));
            }
            self.charge(step.inputs().len(), site)?;
            let mut inputs = Vec::new();
            for input in step.inputs() {
                inputs.push(Argument {
                    ty: input.ty(),
                    atoms: self.read(input, &mut environment, site)?,
                });
            }
            let output = if let Some(operation) = step.boolean() {
                if step_effect != Effect::Unitary || !matches!(step.output().ty().kind, Kind::Bit) {
                    return Err(site.invalid("Boolean source result or effect differs"));
                }
                vec![self.boolean(operation, &inputs, site)?]
            } else if let Some(kind) = step.primitive_kind() {
                self.primitive(kind, step, &inputs, site)?
            } else if let Some(child) = step.called_definition() {
                if step
                    .operation_bindings()
                    .is_some_and(|bindings| !bindings.is_empty())
                {
                    return Err(site.error(
                        "unsupported",
                        "Raw replay does not support operation arguments",
                    ));
                }
                let callee = source
                    .definitions()
                    .get(child)
                    .ok_or_else(|| site.invalid("source call refers to a missing definition"))?;
                if callee.output().ty() != step.output().ty()
                    || effect(callee.effect(), site)? != step_effect
                {
                    return Err(
                        site.invalid("source call changes its result type or declared effect")
                    );
                }
                self.function(child, &inputs, depth + 1, site)?
            } else {
                return Err(site.error(
                    "unsupported",
                    "Raw replay does not support this source operation capability",
                ));
            };
            self.bind(step.output(), &output, &mut environment, site)?;
        }
        let output = self.read(definition.output(), &mut environment, site)?;
        let returned = output
            .iter()
            .filter(|atom| matches!(atom, Atom::Quantum(..)))
            .count();
        if !environment.quantum.is_empty()
            || self.live.len() != suspended.len() + returned
            || suspended
                .iter()
                .any(|(token, wire)| self.live.get(token) != Some(wire))
        {
            return Err(site.invalid(
                "source call drops a quantum owner or changes its suspended caller frame",
            ));
        }
        Ok(output)
    }
}

pub(super) fn validate(source: &ElaboratedProgram, raw: &RawProgram) -> Result<()> {
    let definition = source
        .definitions()
        .get(source.root())
        .ok_or_else(|| Error::new("preservation", Span::default(), "source root is absent"))?;
    let site = Site::definition(definition);
    if raw.declared_effect != effect(definition.effect(), site)? {
        return Err(site.invalid("Raw declared effect differs from the source root"));
    }
    if raw.classical_inputs.len() > MAX_CELLS
        || raw.classical_outputs.len() > MAX_CELLS
        || raw.operations.len() > MAX_STEPS
        || raw.quantum_inputs.len() > MAX_LIVE
        || raw.quantum_outputs.len() > MAX_LIVE
    {
        return Err(site.error("limit", "Raw proposal exceeds replay bounds"));
    }
    let mut replay = Replay {
        source,
        raw,
        cursor: 0,
        calls: 0,
        steps: 0,
        cells: 0,
        classical: BTreeSet::new(),
        tokens: BTreeSet::new(),
        wires: BTreeSet::new(),
        live: BTreeMap::new(),
    };
    replay.charge(raw.classical_inputs.len(), site)?;
    for id in &raw.classical_inputs {
        replay.fresh_classical(*id, site)?;
    }
    for input in &raw.quantum_inputs {
        if !matches!(input.shape, BasisShape::UNIT | BasisShape::BIT)
            || usize::from(input.shape.bits) != input.wires.len()
        {
            return Err(site.invalid(
                "Raw quantum source input must have exact Unit/Bit shape and wire count",
            ));
        }
        replay.introduce_owner(
            input.token,
            input.wires.first().copied(),
            !input.wires.is_empty(),
            site,
        )?;
    }
    replay.charge(definition.inputs().len(), site)?;
    let (mut classical, mut quantum) = (0, 0);
    let mut arguments = Vec::new();
    for input in definition.inputs() {
        let mut atoms = Vec::new();
        for (_, is_quantum) in replay.atoms(input, site)? {
            if let Some(width) = is_quantum {
                let port = raw
                    .quantum_inputs
                    .get(quantum)
                    .ok_or_else(|| site.invalid("Raw program omits a quantum source input"))?;
                quantum += 1;
                if usize::from(port.shape.bits) != width || port.wires.len() != width {
                    return Err(
                        site.invalid("Raw input changes the source's exact Unit/Bit owner shape")
                    );
                }
                atoms.push(Atom::Quantum(port.token, port.wires.first().copied()));
            } else {
                let id = raw
                    .classical_inputs
                    .get(classical)
                    .ok_or_else(|| site.invalid("Raw program omits an ordinary source input"))?;
                classical += 1;
                atoms.push(Atom::Classical(*id));
            }
        }
        arguments.push(Argument {
            ty: input.ty(),
            atoms,
        });
    }
    if classical != raw.classical_inputs.len() || quantum != raw.quantum_inputs.len() {
        return Err(site.invalid("Raw program has extra source inputs"));
    }
    let outputs = replay.function(source.root(), &arguments, 0, site)?;
    if replay.cursor != raw.operations.len() {
        return Err(site.invalid("Raw program contains extra instructions after source replay"));
    }
    let (mut classical, mut quantum) = (Vec::new(), Vec::new());
    for atom in outputs {
        match atom {
            Atom::Classical(id) => classical.push(id),
            Atom::Quantum(token, _) => quantum.push(token),
        }
    }
    if classical != raw.classical_outputs || quantum != raw.quantum_outputs {
        return Err(site.invalid("Raw outputs differ from the source's ordered result"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;
    use crate::interchange::native::{AcceptedProgram, Kernel};
    use crate::ir::QuantumPort;

    fn elaborate(text: &str, entry: &str) -> ElaboratedProgram {
        ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
            .unwrap()
            .instantiate(entry, BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
    }

    fn kernel() -> Kernel {
        Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("select the matching native checker"))
    }

    fn checked(source: &ElaboratedProgram, raw: RawProgram) -> AcceptedProgram {
        let accepted = kernel().accept_raw(raw).unwrap();
        validate(source, accepted.raw()).unwrap();
        accepted
    }

    fn closed_pair() -> (ElaboratedProgram, RawProgram) {
        let source = elaborate(
            "use std::quantum::{h,x,cnot,init0}; use std::observe::measure_z;\n\
             unitary fn turn(q: Q<Bit>) -> Q<Bit> { x(q) }\n\
             pub observe fn main() -> (Bit,Bit) {\n\
             let a = init0(); let b = init0(); let (a,b) = cnot(h(a),b);\n\
             let a = turn(a); (measure_z(a),measure_z(b)) }",
            "main::main",
        );
        // Authored independently of RawState and the sized emitter. The helper
        // acts on one half of a Bell pair while the caller retains the other.
        let raw = RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations: vec![
                RawOp::Init0 {
                    output: TokenId(0),
                    wire: WireId(0),
                },
                RawOp::Init0 {
                    output: TokenId(1),
                    wire: WireId(1),
                },
                RawOp::Gate {
                    gate: SingleGate::H,
                    input: TokenId(0),
                    output: TokenId(2),
                },
                RawOp::Cnot {
                    control: TokenId(2),
                    target: TokenId(1),
                    control_out: TokenId(3),
                    target_out: TokenId(4),
                },
                RawOp::Gate {
                    gate: SingleGate::X,
                    input: TokenId(3),
                    output: TokenId(5),
                },
                RawOp::MeasureZ {
                    input: TokenId(5),
                    output: ClassicalId(0),
                },
                RawOp::MeasureZ {
                    input: TokenId(4),
                    output: ClassicalId(1),
                },
            ],
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0), ClassicalId(1)],
            declared_effect: Effect::Observe,
        };
        (source, raw)
    }

    #[test]
    fn raw_source_replay_preserves_zero_width_owners_and_order_through_calls() {
        let source = elaborate(
            "unitary fn keep(q: Q<Unit>) -> Q<Unit> { q }\n\
             pub unitary fn f(a: Q<Unit>, b: Q<Unit>, c: Q<Bit>)\n\
             -> (Q<Unit>, Q<Bit>, Q<Unit>) { (keep(a), c, keep(b)) }",
            "main::f",
        );
        // Independently authored ports retain two distinct zero-width owners.
        // Neither owner aliases the other's empty wire list or c's wire zero.
        let raw = RawProgram {
            quantum_inputs: vec![
                QuantumPort {
                    token: TokenId(0),
                    shape: BasisShape::UNIT,
                    wires: vec![],
                },
                QuantumPort {
                    token: TokenId(1),
                    shape: BasisShape::UNIT,
                    wires: vec![],
                },
                QuantumPort {
                    token: TokenId(2),
                    shape: BasisShape::BIT,
                    wires: vec![WireId(0)],
                },
            ],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(0), TokenId(2), TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());

        let mut reordered = raw.clone();
        reordered.quantum_outputs.swap(0, 2);
        let accepted = kernel().accept_raw(reordered).unwrap();
        assert!(validate(&source, accepted.raw()).is_err());

        for outputs in [
            vec![TokenId(0), TokenId(2)],
            vec![TokenId(0), TokenId(2), TokenId(0)],
        ] {
            let mut changed = raw.clone();
            changed.quantum_outputs = outputs;
            assert!(validate(&source, &changed).is_err());
            assert!(kernel().accept_raw(changed).is_err());
        }
        for (port, shape) in [(0, BasisShape::BIT), (2, BasisShape::UNIT)] {
            let mut changed = raw.clone();
            changed.quantum_inputs[port].shape = shape;
            assert!(validate(&source, &changed).is_err());
            assert!(kernel().accept_raw(changed).is_err());
        }
    }

    #[test]
    fn raw_source_replay_distinguishes_plain_unit_from_a_zero_width_owner() {
        let source = elaborate("pub unitary fn f(u: Unit) -> Unit { u }", "main::f");
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                shape: BasisShape::UNIT,
                wires: vec![],
            }],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(0)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let accepted = kernel().accept_raw(raw).unwrap();
        assert!(validate(&source, accepted.raw()).is_err());
    }

    #[test]
    fn raw_source_replay_mixed_preserves_entangled_caller_frame_through_an_ordinary_call() {
        let (source, raw) = closed_pair();
        let accepted = checked(&source, raw);
        let observed =
            crate::sim::run_closed(&accepted, crate::sim::SimulationLimits::default()).unwrap();
        assert_eq!(observed.len(), 2);
        for bits in [vec![false, true], vec![true, false]] {
            assert!((observed[&bits] - 0.5).abs() < 1e-12);
        }
    }

    #[test]
    fn raw_source_replay_mixed_rejects_native_valid_gate_control_measurement_and_extra_mutations() {
        let (source, raw) = closed_pair();
        checked(&source, raw.clone());
        let mut mutations = Vec::new();
        let mut changed = raw.clone();
        let RawOp::Gate { gate, .. } = &mut changed.operations[2] else {
            unreachable!()
        };
        *gate = SingleGate::X;
        mutations.push(("H replaced by X", changed));
        let mut changed = raw.clone();
        let RawOp::Cnot {
            control, target, ..
        } = &mut changed.operations[3]
        else {
            unreachable!()
        };
        std::mem::swap(control, target);
        mutations.push(("CNOT operand direction swapped", changed));
        let mut changed = raw.clone();
        changed.operations[5] = RawOp::MeasureZ {
            input: TokenId(4),
            output: ClassicalId(0),
        };
        changed.operations[6] = RawOp::MeasureZ {
            input: TokenId(5),
            output: ClassicalId(1),
        };
        mutations.push(("two measurement owners exchanged", changed));
        let mut changed = raw.clone();
        changed.operations.extend([
            RawOp::Init0 {
                output: TokenId(900),
                wire: WireId(900),
            },
            RawOp::MeasureZ {
                input: TokenId(900),
                output: ClassicalId(900),
            },
        ]);
        mutations.push(("unused quantum initialization and observation", changed));
        let mut changed = raw;
        changed.classical_outputs.reverse();
        mutations.push(("classical output order exchanged", changed));
        for (name, raw) in mutations {
            let accepted = kernel().accept_raw(raw).expect(name);
            // Native-valid alternatives reach the independent matcher directly;
            // the outer RawSourceProposal byte equality guard is not involved.
            let error = validate(&source, accepted.raw()).expect_err(name);
            assert_eq!(error.code(), "preservation", "{name}: {error}");
        }
    }

    #[test]
    fn raw_source_replay_mixed_checks_open_quantum_and_classical_input_and_output_order() {
        let source = elaborate(
            "use std::quantum::{h,cnot};\n\
             pub unitary fn f((q,r): (Q<Bit>,Q<Bit>), c: Bit) -> ((Q<Bit>,Bit),Q<Bit>) {\n\
             let (q,r) = cnot(h(q),r); ((q,c),r) }",
            "main::f",
        );
        let raw = RawProgram {
            quantum_inputs: vec![
                QuantumPort {
                    token: TokenId(10),
                    wires: vec![WireId(5)],
                    shape: BasisShape::BIT,
                },
                QuantumPort {
                    token: TokenId(20),
                    wires: vec![WireId(8)],
                    shape: BasisShape::BIT,
                },
            ],
            classical_inputs: vec![ClassicalId(41)],
            operations: vec![
                RawOp::Gate {
                    gate: SingleGate::H,
                    input: TokenId(10),
                    output: TokenId(11),
                },
                RawOp::Cnot {
                    control: TokenId(11),
                    target: TokenId(20),
                    control_out: TokenId(12),
                    target_out: TokenId(21),
                },
            ],
            quantum_outputs: vec![TokenId(12), TokenId(21)],
            classical_outputs: vec![ClassicalId(41)],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());
        let mut changed = raw.clone();
        changed.quantum_outputs.reverse();
        let accepted = kernel().accept_raw(changed).unwrap();
        assert_eq!(
            validate(&source, accepted.raw()).unwrap_err().code(),
            "preservation"
        );
        let mut changed = raw;
        changed.quantum_inputs.reverse();
        let accepted = kernel().accept_raw(changed).unwrap();
        assert_eq!(
            validate(&source, accepted.raw()).unwrap_err().code(),
            "preservation"
        );
    }

    #[test]
    fn raw_source_replay_mixed_retains_zero_phase_and_matches_only_exact_eighth_turns() {
        let source = elaborate(
            "use std::quantum::phase; pub unitary fn f(q: Q<Bit>) -> Q<Bit> {\n\
             phase[7,3](phase[1,2](phase[2,4](phase[0,8](q)))) }",
            "main::f",
        );
        let operations = (0..10)
            .map(|i| RawOp::Gate {
                gate: SingleGate::T,
                input: TokenId(i),
                output: TokenId(i + 1),
            })
            .collect();
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(0)],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![TokenId(10)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());
        let mut changed = raw.clone();
        let RawOp::Gate { gate, .. } = &mut changed.operations[0] else {
            unreachable!()
        };
        *gate = SingleGate::Z;
        let accepted = kernel().accept_raw(changed).unwrap();
        assert_eq!(
            validate(&source, accepted.raw()).unwrap_err().code(),
            "preservation"
        );
        let unsupported = elaborate(
            "use std::quantum::phase; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { phase[1,4](q) }",
            "main::f",
        );
        let identity = RawProgram {
            operations: vec![],
            quantum_outputs: vec![TokenId(0)],
            ..raw
        };
        let accepted = kernel().accept_raw(identity).unwrap();
        assert_eq!(
            validate(&unsupported, accepted.raw()).unwrap_err().code(),
            "unsupported"
        );
    }
}
