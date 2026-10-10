//! Independent comparison of a retained source-step graph with Raw IR.
//! This untrusted check issues neither native acceptance nor a source theorem.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use crate::frontend::ordinary::Boolean;
use crate::frontend::specialize::primitive::Primitive;
use crate::frontend::specialize::{
    ElaboratedProgram, Error, Result, SourceDefinition, SourceOperation, SourceStep, SourceType,
    SourceValue, Span,
};
use crate::frontend::types::Kind;
#[cfg(test)]
use crate::ir::BasisShape;
use crate::ir::{
    CircuitAction, ClassicalId, Effect, RawOp, RawProgram, SingleGate, TokenId, WireId,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod access;

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

fn basis_width(ty: &SourceType) -> Option<usize> {
    ty.storage_size(4096, 64)?;
    let mut pending = vec![ty];
    let mut width = 0usize;
    while let Some(ty) = pending.pop() {
        match &ty.kind {
            Kind::Unit => {}
            Kind::Bit => width += 1,
            Kind::Bits(bits) => width = width.checked_add(*bits as usize)?,
            Kind::Tuple(fields) => pending.extend(fields),
            _ => return None,
        }
    }
    Some(width)
}
fn quantum_width(ty: &SourceType) -> Option<usize> {
    ty.quantum_basis().and_then(basis_width)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Atom {
    Classical(ClassicalId),
    Register(Arc<[ClassicalId]>),
    Quantum(TokenId, Arc<[WireId]>),
}

#[derive(Clone, Copy)]
enum SourceLeafKind {
    Bit,
    Register(usize),
    Quantum(usize),
}
impl SourceLeafKind {
    fn quantum_width(self) -> Option<usize> {
        match self {
            Self::Quantum(width) => Some(width),
            _ => None,
        }
    }
    fn register_width(self) -> Option<usize> {
        match self {
            Self::Register(width) => Some(width),
            _ => None,
        }
    }
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

struct Replay<'a, 'b> {
    source: &'a ElaboratedProgram,
    raw: &'a RawProgram,
    kernel: Option<&'a crate::interchange::native::Kernel>,
    control_work: &'b mut crate::contract::exact::Budget,
    cursor: usize,
    calls: usize,
    steps: usize,
    cells: usize,
    classical: BTreeSet<ClassicalId>,
    tokens: BTreeSet<TokenId>,
    wires: BTreeSet<WireId>,
    live: BTreeMap<TokenId, Arc<[WireId]>>,
}

impl Replay<'_, '_> {
    fn control_call(
        &mut self,
        step: &SourceStep,
        inputs: &[Argument<'_>],
        outputs: &[Atom],
        first: usize,
        site: Site<'_>,
    ) -> Result<()> {
        use crate::frontend::ast::QuantumAccess;
        if !step.access_roles().contains(&QuantumAccess::Ctrl) {
            return Ok(());
        }
        let kernel = self.kernel.ok_or_else(|| {
            site.error(
                "unsupported",
                "ctrl source replay requires a fresh native sector decision",
            )
        })?;
        self.charge(self.cursor - first + inputs.len() + outputs.len(), site)?;
        let mut ports = Vec::new();
        let mut signatures = Vec::new();
        let mut axes = Vec::new();
        let mut offset = 0;
        for (input, role) in inputs.iter().zip(step.access_roles()) {
            let [Atom::Quantum(token, wires)] = input.atoms.as_slice() else {
                return Err(site.invalid("control call argument is not one quantum owner"));
            };
            let basis = input
                .ty
                .quantum_basis()
                .ok_or_else(|| site.invalid("control call loses its source basis tree"))?;
            self.charge(
                basis
                    .storage_size(4096, 64)
                    .ok_or_else(|| {
                        site.error("limit", "control call basis exceeds source storage limits")
                    })?
                    .nodes
                    + wires.len(),
                site,
            )?;
            signatures.push(super::finite_basis(basis).ok_or_else(|| {
                site.error(
                    "unsupported",
                    "control call basis is outside the finite profile",
                )
            })?);
            ports.push(crate::ir::QuantumPort {
                token: *token,
                wires: wires.to_vec(),
                shape: crate::ir::BasisShape {
                    bits: wires.len() as u8,
                },
            });
            if *role == QuantumAccess::Ctrl {
                axes.extend(offset..offset + wires.len());
            }
            offset += wires.len();
        }
        let returned = outputs
            .iter()
            .map(|output| match output {
                Atom::Quantum(token, _) => Ok(*token),
                _ => Err(site.invalid("control call returns an ordinary value")),
            })
            .collect::<Result<Vec<_>>>()?;
        if returned.len() != ports.len() {
            return Err(site.invalid("control call changes its ordered owner partition"));
        }
        // This is the actual interval just consumed by independent source replay,
        // with its actual tokens/wires. No producer-supplied call body is used.
        let call = RawProgram {
            quantum_inputs: ports,
            classical_inputs: vec![],
            operations: self.raw.operations[first..self.cursor].to_vec(),
            quantum_outputs: returned,
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        kernel
            .check_control_owners(&call, &signatures, &axes, self.control_work)
            .map_err(|error| {
                site.error(
                    error.code,
                    format!(
                        "ctrl requires exact computational-basis sector preservation: {error}; {}",
                        crate::frontend::diagnostic::CONTROL_ACCESS_EXPLANATION
                    ),
                )
            })?;
        Ok(())
    }

    fn access(
        &mut self,
        operation: &SourceOperation,
        inputs: &[Argument<'_>],
        depth: usize,
        controlled: bool,
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        if inputs.len() != 1 + usize::from(controlled) {
            return Err(site.invalid("source access changes argument arity"));
        }
        let target = &inputs[usize::from(controlled)];
        let [Atom::Quantum(target_token, target_wires)] = target.atoms.as_slice() else {
            return Err(site.invalid("source access requires one whole target owner"));
        };
        let mut pending = vec![(operation, 0)];
        while let Some((operation, depth)) = pending.pop() {
            if depth > MAX_DEPTH {
                return Err(site.error("limit", "source access binding exceeds depth bounds"));
            }
            if !operation.children().is_empty() {
                self.charge(1, site)?;
                pending.extend(operation.children().iter().map(|child| (child, depth + 1)));
            }
        }
        let (ports, principal, _) =
            super::operation_signature(operation, self.source.definitions(), operation.span())?;
        if (if controlled {
            ports.input
        } else {
            ports.output
        }) != target.ty
            || (controlled && ports.input != ports.output)
            || principal != Effect::Unitary
        {
            return Err(site.invalid("source access substitutes an exact interface or effect"));
        }
        let expected = access::expected(
            self.source,
            operation,
            depth,
            &mut self.calls,
            &mut self.cells,
            controlled,
            site,
        )?;
        if !controlled {
            let Some(RawOp::ApplyUnitary {
                input,
                output,
                steps,
            }) = self.raw.operations.get(self.cursor)
            else {
                return Err(site.invalid("Raw program omits the source inverse action"));
            };
            if input != target_token || steps != &expected {
                return Err(
                    site.invalid("Raw inverse differs from the original ordered source action")
                );
            }
            let output = *output;
            if self.live.remove(target_token).as_ref() != Some(target_wires) {
                return Err(site.invalid("source inverse consumes an unavailable owner"));
            }
            let result = self.introduce_owner(output, target_wires, false, site)?;
            self.cursor += 1;
            return Ok(vec![result]);
        }
        let (control_token, control_wire) = Self::quantum(&inputs[0], site)?;
        if control_token == *target_token {
            return Err(site.invalid("source control aliases its target owner"));
        }
        let Some(RawOp::Join {
            left,
            right,
            output: joined,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("Raw control omits its exact joint frame"));
        };
        if *left != control_token || right != target_token {
            return Err(site.invalid("Raw control changes operand order or caller owners"));
        }
        let joined = *joined;
        self.remove(control_token, control_wire, site)?;
        if self.live.remove(target_token).as_ref() != Some(target_wires) {
            return Err(site.invalid("source control consumes an unavailable target"));
        }
        self.charge(1 + target_wires.len(), site)?;
        let wires: Vec<_> = std::iter::once(control_wire)
            .chain(target_wires.iter().copied())
            .collect();
        self.introduce_owner(joined, &wires, false, site)?;
        let Some(RawOp::ApplyUnitary {
            input,
            output: transformed,
            steps,
        }) = self.raw.operations.get(self.cursor + 1)
        else {
            return Err(site.invalid("Raw control omits its conditional exact action"));
        };
        if *input != joined || steps != &expected {
            return Err(
                site.invalid("Raw controlled action changes phase, axes or original provider")
            );
        }
        let transformed = *transformed;
        self.live.remove(&joined);
        self.introduce_owner(transformed, &wires, false, site)?;
        let Some(RawOp::Split {
            input,
            left,
            right,
            left_bits,
        }) = self.raw.operations.get(self.cursor + 2)
        else {
            return Err(site.invalid("Raw control omits its returned owner interface"));
        };
        if *input != transformed || *left_bits != 1 {
            return Err(site.invalid("Raw control changes its exact returned split"));
        }
        let (left, right) = (*left, *right);
        self.live.remove(&transformed);
        let control = self.introduce(left, control_wire, false, site)?;
        let target = self.introduce_owner(right, target_wires, false, site)?;
        self.cursor += 3;
        Ok(vec![control, target])
    }
    fn charge(&mut self, count: usize, site: Site<'_>) -> Result<()> {
        self.cells = self.cells.saturating_add(count);
        if self.cells > MAX_CELLS {
            return Err(site.error("limit", "Raw replay exceeds 100000 value cells"));
        }
        Ok(())
    }

    /// Exact source constructors, including ordinary Unit versus zero-width
    /// owners/registers. Charge pending children before extending the stack.
    fn atoms(&mut self, value: &SourceValue, site: Site<'_>) -> Result<Vec<(u32, SourceLeafKind)>> {
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
                Kind::Bits(width) => {
                    if !value.fields().is_empty() {
                        return Err(site.invalid("ordinary register has product fields"));
                    }
                    self.charge(*width as usize, site)?;
                    result.push((
                        value.identity().ok_or_else(|| {
                            site.invalid("ordinary register lacks its source identity")
                        })?,
                        SourceLeafKind::Register(*width as usize),
                    ));
                }
                Kind::Bit | Kind::Q(_)
                    if matches!(expected.kind, Kind::Bit) || quantum_width(expected).is_some() =>
                {
                    if !value.fields().is_empty() {
                        return Err(site.invalid("source atom has product fields"));
                    }
                    if let Some(basis) = expected.quantum_basis() {
                        self.charge(
                            basis
                                .storage_size(4096, 64)
                                .ok_or_else(|| {
                                    site.error("limit", "quantum basis exceeds type capacity")
                                })?
                                .nodes,
                            site,
                        )?;
                    }
                    result.push((
                        value
                            .identity()
                            .ok_or_else(|| site.invalid("source atom lacks its identity"))?,
                        match quantum_width(expected) {
                            Some(width) => SourceLeafKind::Quantum(width),
                            None => SourceLeafKind::Bit,
                        },
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
                Kind::Bit | Kind::Q(_) | Kind::Parameter(_) => {
                    return Err(site.error(
                        "unsupported",
                        "Raw replay supports Unit/Bit and exact ordinary or packaged quantum products",
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
        for ((source, kind), actual) in atoms.into_iter().zip(actual) {
            let quantum = kind.quantum_width();
            let register = kind.register_width();
            if quantum.is_some() != matches!(actual, Atom::Quantum(..))
                || !environment.issued.insert(source)
            {
                return Err(site.invalid(
                    "source step changes leaf ownership kind or redefines a local identity",
                ));
            }
            if register
                != match actual {
                    Atom::Register(ids) => Some(ids.len()),
                    _ => None,
                }
            {
                return Err(site.invalid("source binding changes ordinary register type or width"));
            }
            match actual {
                Atom::Register(ids) => {
                    if ids.iter().any(|id| !self.classical.contains(id)) {
                        return Err(
                            site.invalid("source register names an unissued classical value")
                        );
                    }
                }
                Atom::Quantum(token, wire) => {
                    if quantum != Some(wire.len())
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
            environment.values.insert(source, actual.clone());
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
        for (id, kind) in self.atoms(value, site)? {
            let quantum = kind.quantum_width();
            let register = kind.register_width();
            let actual = environment
                .values
                .get(&id)
                .cloned()
                .ok_or_else(|| site.invalid("source step uses an unavailable value"))?;
            if quantum.is_some() != matches!(actual, Atom::Quantum(..)) {
                return Err(site.invalid("source read changes a leaf's ownership kind"));
            }
            if register
                != match &actual {
                    Atom::Register(ids) => Some(ids.len()),
                    _ => None,
                }
            {
                return Err(site.invalid("source read changes ordinary register type or width"));
            }
            if let Atom::Quantum(token, wire) = &actual {
                if quantum != Some(wire.len())
                    || self.live.get(token) != Some(wire)
                    || !environment.quantum.remove(token)
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
        self.introduce_owner(token, &[wire], fresh_wire, site)
    }

    fn introduce_owner(
        &mut self,
        token: TokenId,
        wires: &[WireId],
        fresh_wire: bool,
        site: Site<'_>,
    ) -> Result<Atom> {
        self.charge(1 + wires.len(), site)?;
        if wires.len() > MAX_LIVE
            || self.live.values().map(|w| w.len()).sum::<usize>() + wires.len() > MAX_LIVE
        {
            return Err(site.error("limit", "Raw replay exceeds 16 globally live quantum wires"));
        }
        if !self.tokens.insert(token)
            || wires.iter().copied().collect::<BTreeSet<_>>().len() != wires.len()
            || (fresh_wire && wires.iter().any(|wire| !self.wires.insert(*wire)))
        {
            return Err(site.invalid("Raw operation reuses an issued token or wire"));
        }
        if self
            .live
            .values()
            .any(|existing| wires.iter().any(|wire| existing.contains(wire)))
        {
            return Err(site.invalid("Raw operation aliases a live wire"));
        }
        let wires: Arc<[WireId]> = wires.into();
        self.live.insert(token, wires.clone());
        Ok(Atom::Quantum(token, wires))
    }

    fn quantum(input: &Argument<'_>, site: Site<'_>) -> Result<(TokenId, WireId)> {
        match input.atoms.as_slice() {
            [Atom::Quantum(token, wires)] if quantum_bit(input.ty) && wires.len() == 1 => {
                Ok((*token, wires[0]))
            }
            _ => Err(site.invalid("primitive requires one exact Q<Bit> argument")),
        }
    }

    fn remove(&mut self, token: TokenId, wire: WireId, site: Site<'_>) -> Result<()> {
        if self
            .live
            .remove(&token)
            .is_none_or(|wires| wires.as_ref() != [wire])
        {
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

    fn split_register(
        &mut self,
        token: TokenId,
        wires: &[WireId],
        width: usize,
        site: Site<'_>,
    ) -> Result<(Atom, Atom)> {
        let Some(RawOp::Split {
            input,
            left,
            right,
            left_bits,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("register repartition omits an ordered split"));
        };
        if *input != token || usize::from(*left_bits) != width || width > wires.len() {
            return Err(site.invalid("register repartition changes its source owner or split axis"));
        }
        let (left, right) = (*left, *right);
        if self.live.remove(&token).as_deref() != Some(wires) {
            return Err(site.invalid("register repartition consumes an unavailable owner"));
        }
        let left = self.introduce_owner(left, &wires[..width], false, site)?;
        let right = self.introduce_owner(right, &wires[width..], false, site)?;
        self.cursor += 1;
        Ok((left, right))
    }
    fn join_register(&mut self, left: Atom, right: Atom, site: Site<'_>) -> Result<Atom> {
        let (Atom::Quantum(l, lw), Atom::Quantum(r, rw)) = (left, right) else {
            return Err(site.invalid("register repartition requires two quantum owners"));
        };
        let Some(RawOp::Join {
            left,
            right,
            output,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("register repartition omits an ordered join"));
        };
        if *left != l || *right != r || l == r {
            return Err(site.invalid("register repartition changes or aliases its ordered owners"));
        }
        let output = *output;
        if self.live.remove(&l).as_ref() != Some(&lw) || self.live.remove(&r).as_ref() != Some(&rw)
        {
            return Err(site.invalid("register repartition joins unavailable owners"));
        }
        self.charge(lw.len() + rw.len(), site)?;
        let wires: Vec<_> = lw.iter().chain(rw.iter()).copied().collect();
        let result = self.introduce_owner(output, &wires, false, site)?;
        self.cursor += 1;
        Ok(result)
    }
    fn register_bit(
        &mut self,
        kind: Primitive,
        step: &SourceStep,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let [n, k] = step.natural_arguments() else {
            return Err(site.invalid("register repartition loses its Nat arguments"));
        };
        if k >= n || *n > 8 {
            return Err(site.invalid("register repartition loses its static bounds"));
        }
        self.partition_register(
            super::super::elaborate::PlacePartition {
                taking: kind == Primitive::TakeBit,
                width: *n,
                start: *k,
                end: k + 1,
                bit: true,
            },
            step,
            inputs,
            site,
        )
    }
    fn partition_register(
        &mut self,
        p: super::super::elaborate::PlacePartition,
        step: &SourceStep,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let n = p.width;
        let size = p
            .end
            .checked_sub(p.start)
            .ok_or_else(|| site.invalid("place partition reverses its ordered bounds"))?;
        if p.end > n || n > 8 || (p.bit && size != 1) {
            return Err(site.invalid("place partition loses its exact static bounds"));
        }
        let selected = SourceType::quantum(if p.bit {
            SourceType::bit()
        } else {
            SourceType::bits(size)
        });
        self.charge(12 + n as usize * 3, site)?;
        if p.taking {
            let [input] = inputs else {
                return Err(site.invalid("take_bit changes source arity"));
            };
            let [Atom::Quantum(token, wires)] = input.atoms.as_slice() else {
                return Err(site.invalid("take_bit requires one original quantum owner"));
            };
            let output = SourceType::tuple(vec![
                selected.clone(),
                SourceType::quantum(SourceType::bits(n - size)),
            ]);
            if input.ty != &SourceType::quantum(SourceType::bits(n))
                || step.output().ty() != &output
                || wires.len() != n as usize
            {
                return Err(
                    site.invalid("take_bit changes its exact original input or result tree")
                );
            }
            let (prefix, tail) = self.split_register(*token, wires, p.start as usize, site)?;
            let Atom::Quantum(tail_token, tail_wires) = tail else {
                unreachable!()
            };
            let (bit, suffix) =
                self.split_register(tail_token, &tail_wires, size as usize, site)?;
            let rest = self.join_register(prefix, suffix, site)?;
            Ok(vec![bit, rest])
        } else {
            let [bit, rest] = inputs else {
                return Err(site.invalid("put_bit changes source arity"));
            };
            let ([Atom::Quantum(_, bit_wires)], [Atom::Quantum(token, wires)]) =
                (bit.atoms.as_slice(), rest.atoms.as_slice())
            else {
                return Err(site.invalid("put_bit requires two original quantum owners"));
            };
            if bit.ty != &selected
                || bit_wires.len() != size as usize
                || rest.ty != &SourceType::quantum(SourceType::bits(n - size))
                || wires.len() != (n - size) as usize
                || step.output().ty() != &SourceType::quantum(SourceType::bits(n))
            {
                return Err(site.invalid("put_bit changes its exact original input or result tree"));
            }
            self.charge(1, site)?;
            let (prefix, suffix) = self.split_register(*token, wires, p.start as usize, site)?;
            let head = self.join_register(prefix, bit.atoms[0].clone(), site)?;
            Ok(vec![self.join_register(head, suffix, site)?])
        }
    }

    fn primitive(
        &mut self,
        kind: Primitive,
        step: &SourceStep,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let required = match kind {
            Primitive::H
            | Primitive::X
            | Primitive::Z
            | Primitive::Cnot
            | Primitive::Phase
            | Primitive::PhaseEighth
            | Primitive::Split
            | Primitive::Join
            | Primitive::TakeBit
            | Primitive::PutBit
            | Primitive::EmptyBits
            | Primitive::PrependBit => Effect::Unitary,
            Primitive::Unit | Primitive::Finish => Effect::Unitary,
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
            || (!matches!(
                kind,
                Primitive::Phase | Primitive::PrependBit | Primitive::TakeBit | Primitive::PutBit
            ) && !step.natural_arguments().is_empty())
        {
            return Err(site.invalid(
                "primitive effect or natural arguments differ from its source signature",
            ));
        }
        match (kind, inputs) {
            (Primitive::Unit, [input])
                if matches!(input.ty.kind, Kind::Unit)
                    && input.atoms.is_empty()
                    && step.output().ty() == &SourceType::quantum(SourceType::unit()) =>
            {
                let Some(RawOp::PackUnit { output }) = self.raw.operations.get(self.cursor) else {
                    return Err(site.invalid("Raw program omits the source Unit introduction"));
                };
                let atom = self.introduce_owner(*output, &[], false, site)?;
                self.cursor += 1;
                Ok(vec![atom])
            }
            (Primitive::Finish, [input])
                if input.ty == &SourceType::quantum(SourceType::unit())
                    && matches!(step.output().ty().kind, Kind::Unit) =>
            {
                let [Atom::Quantum(token, wires)] = input.atoms.as_slice() else {
                    return Err(site.invalid("finish source argument is not one quantum owner"));
                };
                let Some(RawOp::UnpackUnit { input: actual }) =
                    self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source Unit consumption"));
                };
                if actual != token
                    || !wires.is_empty()
                    || self.live.remove(token).as_deref() != Some(&[])
                {
                    return Err(site.invalid("Raw finish changes or reuses its source owner"));
                }
                self.cursor += 1;
                Ok(vec![])
            }
            (Primitive::TakeBit | Primitive::PutBit, _) => {
                self.register_bit(kind, step, inputs, site)
            }
            (Primitive::EmptyBits, []) if matches!(step.output().ty().kind, Kind::Bits(0)) => {
                Ok(vec![Atom::Register(Arc::from([]))])
            }
            (Primitive::PrependBit, [head, tail]) => {
                let ([Atom::Classical(bit)], [Atom::Register(ids)]) =
                    (head.atoms.as_slice(), tail.atoms.as_slice())
                else {
                    return Err(site.invalid("packing changes ordinary argument categories"));
                };
                let [width] = step.natural_arguments() else {
                    return Err(site.invalid("packing loses its exact Nat argument"));
                };
                if *width >= 8
                    || !matches!(head.ty.kind, Kind::Bit)
                    || !matches!(tail.ty.kind, Kind::Bits(n) if n == *width)
                    || !matches!(step.output().ty().kind, Kind::Bits(n) if n == width + 1)
                    || ids.len() != *width as usize
                {
                    return Err(site.invalid("packing changes source width or output type"));
                }
                self.charge(ids.len() + 1, site)?;
                Ok(vec![Atom::Register(
                    std::iter::once(*bit).chain(ids.iter().copied()).collect(),
                )])
            }
            (Primitive::PhaseEighth, [input])
                if input.ty == step.output().ty() && quantum_width(input.ty).is_some() =>
            {
                let [Atom::Quantum(token, wire)] = input.atoms.as_slice() else {
                    return Err(site.invalid("scalar phase requires one quantum owner"));
                };
                let Some(RawOp::ApplyUnitary {
                    input: actual,
                    output,
                    steps,
                }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source scalar phase"));
                };
                if actual != token || steps.len() != 1 || !steps[0].controls.is_empty() {
                    return Err(site.invalid("Raw scalar changes its owner or controlled action"));
                }
                match &steps[0].action {
                    CircuitAction::Monomial {
                        indices,
                        permutation,
                        phases,
                    } if indices.is_empty() && permutation == &[0] && phases == &[1] => {}
                    _ => return Err(site.invalid("Raw scalar differs from exact omega identity")),
                }
                let output = *output;
                if self.live.remove(token).as_ref() != Some(wire) {
                    return Err(site.invalid("Raw scalar consumes an unavailable owner"));
                }
                let atom = self.introduce_owner(output, wire, false, site)?;
                self.cursor += 1;
                Ok(vec![atom])
            }
            (Primitive::Split, [input]) => {
                let fields = input
                    .ty
                    .quantum_basis()
                    .and_then(SourceType::tuple_fields)
                    .filter(|fields| fields.len() == 2)
                    .ok_or_else(|| site.invalid("split requires an exact packaged pair"))?;
                let output_fields = step
                    .output()
                    .ty()
                    .tuple_fields()
                    .filter(|fields| fields.len() == 2)
                    .ok_or_else(|| site.invalid("split result is not two owners"))?;
                if output_fields[0].quantum_basis() != Some(&fields[0])
                    || output_fields[1].quantum_basis() != Some(&fields[1])
                {
                    return Err(site.invalid("split changes its exact field types or order"));
                }
                let [Atom::Quantum(token, wires)] = input.atoms.as_slice() else {
                    return Err(site.invalid("split requires one whole owner"));
                };
                let width = basis_width(&fields[0])
                    .ok_or_else(|| site.invalid("split has an unsupported field basis"))?;
                if width > wires.len() {
                    return Err(site.invalid("split field exceeds original wires"));
                }
                let Some(RawOp::Split {
                    input: actual,
                    left,
                    right,
                    left_bits,
                }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source split"));
                };
                if actual != token || usize::from(*left_bits) != width {
                    return Err(
                        site.invalid("Raw split changes its owner or exact ordered partition")
                    );
                }
                let (left, right) = (*left, *right);
                if self.live.remove(token).as_ref() != Some(wires) {
                    return Err(site.invalid("split consumes an unavailable owner"));
                }
                let outputs = vec![
                    self.introduce_owner(left, &wires[..width], false, site)?,
                    self.introduce_owner(right, &wires[width..], false, site)?,
                ];
                self.cursor += 1;
                Ok(outputs)
            }
            (Primitive::Join, [left, right]) => {
                let fields = step
                    .output()
                    .ty()
                    .quantum_basis()
                    .and_then(SourceType::tuple_fields)
                    .filter(|fields| fields.len() == 2)
                    .ok_or_else(|| site.invalid("join result is not an exact packaged pair"))?;
                if left.ty.quantum_basis() != Some(&fields[0])
                    || right.ty.quantum_basis() != Some(&fields[1])
                {
                    return Err(site.invalid("join changes its exact field types or order"));
                }
                let ([Atom::Quantum(l, lw)], [Atom::Quantum(r, rw)]) =
                    (left.atoms.as_slice(), right.atoms.as_slice())
                else {
                    return Err(site.invalid("join requires two whole owners"));
                };
                let Some(RawOp::Join {
                    left: actual_l,
                    right: actual_r,
                    output,
                }) = self.raw.operations.get(self.cursor)
                else {
                    return Err(site.invalid("Raw program omits the source join"));
                };
                if actual_l != l || actual_r != r || l == r {
                    return Err(site.invalid("Raw join changes or aliases its ordered owners"));
                }
                let output = *output;
                if self.live.remove(l).as_ref() != Some(lw)
                    || self.live.remove(r).as_ref() != Some(rw)
                {
                    return Err(site.invalid("join consumes an unavailable owner"));
                }
                self.charge(lw.len() + rw.len(), site)?;
                let wires = lw.iter().chain(rw.iter()).copied().collect::<Vec<_>>();
                let output = self.introduce_owner(output, &wires, false, site)?;
                self.cursor += 1;
                Ok(vec![output])
            }
            (Primitive::H | Primitive::X | Primitive::Z, [input])
                if quantum_bit(step.output().ty()) =>
            {
                let input = Self::quantum(input, site)?;
                let gate = match kind {
                    Primitive::H => SingleGate::H,
                    Primitive::X => SingleGate::X,
                    Primitive::Z => SingleGate::Z,
                    _ => unreachable!("matched single gate"),
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
                    let Atom::Quantum(token, wires) = self.gate(input, SingleGate::T, site)? else {
                        unreachable!("gate returns a quantum atom")
                    };
                    input = (token, wires[0]);
                }
                Ok(vec![Atom::Quantum(input.0, Arc::from([input.1]))])
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

    fn operation(
        &mut self,
        operation: &SourceOperation,
        arguments: &[Argument<'_>],
        depth: usize,
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        if let Some(id) = operation.definition() {
            let definition =
                self.source.definitions().get(id).ok_or_else(|| {
                    site.invalid("source operation refers to a missing definition")
                })?;
            let [argument] = arguments else {
                return Err(site.invalid("forward operation requires one whole argument"));
            };
            if definition.inputs().len() != 1
                || definition.inputs()[0].ty() != argument.ty
                || effect(definition.effect(), site)? > Effect::Iso
            {
                return Err(
                    site.invalid("forward operation changes its exact input interface or effect")
                );
            }
            return self.function(id, arguments, depth, site);
        }
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(site.error("limit", "Raw operation replay exceeds call/depth bounds"));
        }
        if let Some((kind, children, ports)) = operation.constructed() {
            use crate::frontend::specialize::ast::OperationConstructor as C;
            let [argument] = arguments else {
                return Err(site.invalid("constructor requires one whole argument"));
            };
            if argument.ty != &ports.input {
                return Err(site.invalid("constructor changes its complete input type"));
            }
            return match kind {
                C::Then => {
                    let middle = self.operation(&children[0], arguments, depth + 1, site)?;
                    let (first, _, _) = super::operation_signature(
                        &children[0],
                        self.source.definitions(),
                        site.span,
                    )?;
                    self.operation(
                        &children[1],
                        &[Argument {
                            ty: first.output,
                            atoms: middle,
                        }],
                        depth + 1,
                        site,
                    )
                }
                C::Adjoint => self.access(&children[0], arguments, depth + 1, false, site),
                C::Conjugate => {
                    let first = self.access(&children[0], arguments, depth + 1, false, site)?;
                    let (outer, _, _) = super::operation_signature(
                        &children[0],
                        self.source.definitions(),
                        site.span,
                    )?;
                    let middle = self.operation(
                        &children[1],
                        &[Argument {
                            ty: outer.input,
                            atoms: first,
                        }],
                        depth + 1,
                        site,
                    )?;
                    self.operation(
                        &children[0],
                        &[Argument {
                            ty: outer.input,
                            atoms: middle,
                        }],
                        depth + 1,
                        site,
                    )
                }
                C::Tensor | C::Controlled => {
                    let (left, right) = self.split_constructor(argument, site)?;
                    let (a, _, _) = super::operation_signature(
                        &children[0],
                        self.source.definitions(),
                        site.span,
                    )?;
                    let (left, right) = if kind == C::Tensor {
                        let (b, _, _) = super::operation_signature(
                            &children[1],
                            self.source.definitions(),
                            site.span,
                        )?;
                        let left = self.operation(
                            &children[0],
                            &[Argument {
                                ty: a.input,
                                atoms: vec![left],
                            }],
                            depth + 1,
                            site,
                        )?;
                        let right = self.operation(
                            &children[1],
                            &[Argument {
                                ty: b.input,
                                atoms: vec![right],
                            }],
                            depth + 1,
                            site,
                        )?;
                        (left, right)
                    } else {
                        let control = SourceType::quantum(SourceType::bit());
                        let mut output = self.access(
                            &children[0],
                            &[
                                Argument {
                                    ty: &control,
                                    atoms: vec![left],
                                },
                                Argument {
                                    ty: a.input,
                                    atoms: vec![right],
                                },
                            ],
                            depth + 1,
                            true,
                            site,
                        )?;
                        if output.len() != 2 {
                            return Err(site.invalid("packed control owner arity differs"));
                        }
                        let right = output.pop().unwrap();
                        (output, vec![right])
                    };
                    self.join_constructor(&left, &right, site)
                }
            };
        }
        let [argument] = arguments else {
            return Err(site.invalid("repeated operation requires one whole argument"));
        };
        self.charge(argument.atoms.len(), site)?;
        let mut value = argument.atoms.clone();
        for _ in 0..operation.repeat_count().expect("retained repeat") {
            value = self.operation(
                operation.child().expect("retained repeat child"),
                &[Argument {
                    ty: argument.ty,
                    atoms: value,
                }],
                depth + 1,
                site,
            )?;
        }
        Ok(value)
    }
    fn split_constructor(&mut self, input: &Argument<'_>, site: Site<'_>) -> Result<(Atom, Atom)> {
        let fields = input
            .ty
            .quantum_basis()
            .and_then(SourceType::tuple_fields)
            .filter(|fields| fields.len() == 2)
            .ok_or_else(|| site.invalid("constructor split input tree differs"))?;
        let width = basis_width(&fields[0])
            .ok_or_else(|| site.invalid("constructor split basis is not finite"))?;
        let [Atom::Quantum(token, wires)] = input.atoms.as_slice() else {
            return Err(site.invalid("constructor split requires one owner"));
        };
        if width > wires.len() {
            return Err(site.invalid("constructor split field exceeds axes"));
        }
        let Some(RawOp::Split {
            input: actual,
            left,
            right,
            left_bits,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("Raw constructor split is missing"));
        };
        if actual != token || usize::from(*left_bits) != width {
            return Err(site.invalid("Raw constructor split changes original ordered axes"));
        }
        let (left, right) = (*left, *right);
        if self.live.remove(token).as_ref() != Some(wires) {
            return Err(site.invalid("constructor consumes an absent owner"));
        }
        let left = self.introduce_owner(left, &wires[..width], false, site)?;
        let right = self.introduce_owner(right, &wires[width..], false, site)?;
        self.cursor += 1;
        Ok((left, right))
    }
    fn join_constructor(
        &mut self,
        left: &[Atom],
        right: &[Atom],
        site: Site<'_>,
    ) -> Result<Vec<Atom>> {
        let ([Atom::Quantum(l, lw)], [Atom::Quantum(r, rw)]) = (left, right) else {
            return Err(site.invalid("constructor tensor results are not two owners"));
        };
        let Some(RawOp::Join {
            left: actual_l,
            right: actual_r,
            output,
        }) = self.raw.operations.get(self.cursor)
        else {
            return Err(site.invalid("Raw constructor join is missing"));
        };
        if actual_l != l || actual_r != r || l == r {
            return Err(site.invalid("Raw constructor join changes ordered owners"));
        }
        let output = *output;
        if self.live.remove(l).as_ref() != Some(lw) || self.live.remove(r).as_ref() != Some(rw) {
            return Err(site.invalid("constructor returns unavailable owners"));
        }
        self.charge(lw.len() + rw.len(), site)?;
        let mut wires = lw.to_vec();
        wires.extend(rw.iter().copied());
        let atom = self.introduce_owner(output, &wires, false, site)?;
        self.cursor += 1;
        Ok(vec![atom])
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
        // Capture the actual suspended caller frame within the wire/storage bounds,
        // without assuming those wires are separable from this call's inputs.
        self.charge(self.live.len(), site)?;
        let suspended: BTreeMap<_, _> = self
            .live
            .iter()
            .filter(|(token, _)| !environment.quantum.contains(token))
            .map(|(t, w)| (*t, w.clone()))
            .collect();
        for step in definition.steps() {
            step.check_access_shape()?;
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
            let first_instruction = self.cursor;
            let output = if let Some(operation) = step.boolean() {
                if step_effect != Effect::Unitary || !matches!(step.output().ty().kind, Kind::Bit) {
                    return Err(site.invalid("Boolean source result or effect differs"));
                }
                vec![self.boolean(operation, &inputs, site)?]
            } else if let Some(partition) = step.partition() {
                if step_effect != Effect::Unitary {
                    return Err(site.invalid("place partition changes its structural effect"));
                }
                self.partition_register(partition, step, &inputs, site)?
            } else if let Some(kind) = step.primitive_kind() {
                self.primitive(kind, step, &inputs, site)?
            } else if let Some(child) = step.called_definition() {
                let callee = source
                    .definitions()
                    .get(child)
                    .ok_or_else(|| site.invalid("source call refers to a missing definition"))?;
                let actual = step
                    .operation_bindings()
                    .ok_or_else(|| site.invalid("source call has no operation binding map"))?;
                self.charge(actual.len(), site)?;
                if actual.len() != callee.operations().len() {
                    return Err(site.invalid("source call changes its operation arguments"));
                }
                for (name, operation) in actual {
                    let retained = callee.operations().get(name).ok_or_else(|| {
                        site.invalid("source call changes an operation parameter identity")
                    })?;
                    for value in [operation, retained] {
                        let mut pending = vec![(value, 0)];
                        while let Some((value, depth)) = pending.pop() {
                            self.charge(1, site)?;
                            if depth > MAX_DEPTH {
                                return Err(site.error(
                                    "limit",
                                    "Raw call binding exceeds operation depth bounds",
                                ));
                            }
                            pending.extend(value.children().iter().map(|child| (child, depth + 1)));
                        }
                    }
                    if operation.key() != retained.key() {
                        return Err(site.invalid(
                            "source call substitutes an operation definition or Meaning request",
                        ));
                    }
                }
                if callee.output().ty() != step.output().ty()
                    || effect(callee.effect(), site)? != step_effect
                {
                    return Err(
                        site.invalid("source call changes its result type or declared effect")
                    );
                }
                self.function(child, &inputs, depth + 1, site)?
            } else if let Some(operation) = step.operation() {
                if step.kind() == "apply" {
                    self.operation(operation, &inputs, depth + 1, site)?
                } else {
                    self.access(
                        operation,
                        &inputs,
                        depth + 1,
                        step.kind() == "controlled",
                        site,
                    )?
                }
            } else {
                return Err(site.error(
                    "unsupported",
                    "Raw replay does not support this source operation capability",
                ));
            };
            self.control_call(step, &inputs, &output, first_instruction, site)?;
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

#[cfg(test)]
pub(super) fn validate(source: &ElaboratedProgram, raw: &RawProgram) -> Result<()> {
    validate_definition(source, source.root(), raw)
}

#[cfg(test)]
pub(super) fn validate_definition(
    source: &ElaboratedProgram,
    subject: usize,
    raw: &RawProgram,
) -> Result<()> {
    validate_subject(source, subject, None, raw)
}

pub(super) fn validate_subject(
    source: &ElaboratedProgram,
    subject: usize,
    operation: Option<&SourceOperation>,
    raw: &RawProgram,
) -> Result<()> {
    validate_subject_with_kernel(source, subject, operation, raw, None)
}

pub(super) fn validate_subject_with_kernel(
    source: &ElaboratedProgram,
    subject: usize,
    operation: Option<&SourceOperation>,
    raw: &RawProgram,
    kernel: Option<&crate::interchange::native::Kernel>,
) -> Result<()> {
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    validate_subject_with_control_work(source, subject, operation, raw, kernel, &mut budget)
}

pub(super) fn validate_subject_with_control_work(
    source: &ElaboratedProgram,
    subject: usize,
    operation: Option<&SourceOperation>,
    raw: &RawProgram,
    kernel: Option<&crate::interchange::native::Kernel>,
    control_work: &mut crate::contract::exact::Budget,
) -> Result<()> {
    let definition = source
        .definitions()
        .get(subject)
        .ok_or_else(|| Error::new("preservation", Span::default(), "source subject is absent"))?;
    let site = Site::definition(definition);
    let signature = operation
        .map(|operation| {
            super::operation_signature(operation, source.definitions(), operation.span())
        })
        .transpose()?;
    if let Some(operation) = operation {
        let mut base = operation;
        let mut depth = 0;
        while let Some(child) = base.child() {
            depth += 1;
            if depth > MAX_DEPTH {
                return Err(site.error("limit", "Raw operation replay exceeds depth bound"));
            }
            base = child;
        }
        if base.definition().is_some_and(|id| id != subject) {
            return Err(site.invalid("operation subject differs from its original leaf"));
        }
    }
    let declared = signature.as_ref().map_or_else(
        || effect(definition.effect(), site),
        |(_, effect, _)| Ok(*effect),
    )?;
    if raw.declared_effect != declared {
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
        kernel,
        control_work,
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
        if usize::from(input.shape.bits) != input.wires.len() {
            return Err(site.invalid("Raw quantum source input shape and wire count disagree"));
        }
        replay.introduce_owner(input.token, &input.wires, !input.wires.is_empty(), site)?;
    }
    replay.charge(definition.inputs().len(), site)?;
    let (mut classical, mut quantum) = (0usize, 0usize);
    let mut arguments = Vec::new();
    if let Some((ports, _, _)) = &signature {
        let width = quantum_width(ports.input)
            .ok_or_else(|| site.invalid("operation input is not a finite quantum owner"))?;
        let [port] = raw.quantum_inputs.as_slice() else {
            return Err(site.invalid("operation input owner arity differs"));
        };
        if usize::from(port.shape.bits) != width || port.wires.len() != width {
            return Err(site.invalid("operation input changes its exact width"));
        }
        quantum = 1;
        arguments.push(Argument {
            ty: ports.input,
            atoms: vec![Atom::Quantum(port.token, Arc::from(port.wires.as_slice()))],
        });
    } else {
        for input in definition.inputs() {
            let mut atoms = Vec::new();
            for (_, kind) in replay.atoms(input, site)? {
                let is_quantum = kind.quantum_width();
                let register_width = kind.register_width();
                if let Some(width) = is_quantum {
                    let port = raw
                        .quantum_inputs
                        .get(quantum)
                        .ok_or_else(|| site.invalid("Raw program omits a quantum source input"))?;
                    quantum += 1;
                    if usize::from(port.shape.bits) != width || port.wires.len() != width {
                        return Err(site
                            .invalid("Raw input changes the source's exact quantum owner shape"));
                    }
                    atoms.push(Atom::Quantum(port.token, Arc::from(port.wires.as_slice())));
                } else if let Some(width) = register_width {
                    let end = classical
                        .checked_add(width)
                        .ok_or_else(|| site.error("limit", "ordinary input width overflow"))?;
                    let ids = raw.classical_inputs.get(classical..end).ok_or_else(|| {
                        site.invalid("Raw program omits ordinary register input elements")
                    })?;
                    atoms.push(Atom::Register(Arc::from(ids)));
                    classical = end;
                } else {
                    let id = raw.classical_inputs.get(classical).ok_or_else(|| {
                        site.invalid("Raw program omits an ordinary source input")
                    })?;
                    classical += 1;
                    atoms.push(Atom::Classical(*id));
                }
            }
            arguments.push(Argument {
                ty: input.ty(),
                atoms,
            });
        }
    }
    if classical != raw.classical_inputs.len() || quantum != raw.quantum_inputs.len() {
        return Err(site.invalid("Raw program has extra source inputs"));
    }
    let outputs = if let Some(operation) = operation {
        replay.operation(operation, &arguments, 0, site)?
    } else {
        replay.function(subject, &arguments, 0, site)?
    };
    if replay.cursor != raw.operations.len() {
        return Err(site.invalid("Raw program contains extra instructions after source replay"));
    }
    let (mut classical, mut quantum) = (Vec::new(), Vec::new());
    for atom in outputs {
        match atom {
            Atom::Classical(id) => classical.push(id),
            Atom::Register(ids) => classical.extend(ids.iter().copied()),
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
    #[test]
    fn access_replay_rejects_native_valid_inverse_order_phase_and_control_frame_substitutions() {
        for body in ["h(phase[1,3](q))", "helper[then_op(twist,had)](q)"] {
            let source = elaborate(
                &format!(
                    "use std::quantum::{{h,phase}};
                unitary fn twist(q:Q<Bit>)->Q<Bit>{{phase[1,3](q)}}
                unitary fn had(q:Q<Bit>)->Q<Bit>{{h(q)}}
                unitary fn helper[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
                    requires Applicable(U){{U(q)}}
                unitary fn turn(q:Q<Bit>)->Q<Bit>{{{body}}}
                pub unitary fn caller(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){{(adjoint(turn)(q),r)}}"
                ),
                "main::caller",
            );
            let phase = crate::ir::CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![0],
                    permutation: vec![0, 1],
                    phases: vec![0, 7],
                },
            };
            let hadamard = crate::ir::CircuitStep {
                controls: vec![],
                action: CircuitAction::Hadamard { target: 0 },
            };
            let raw = RawProgram {
                quantum_inputs: vec![
                    QuantumPort {
                        token: TokenId(0),
                        shape: BasisShape::BIT,
                        wires: vec![WireId(0)],
                    },
                    QuantumPort {
                        token: TokenId(1),
                        shape: BasisShape::BIT,
                        wires: vec![WireId(1)],
                    },
                ],
                classical_inputs: vec![],
                operations: vec![RawOp::ApplyUnitary {
                    input: TokenId(0),
                    output: TokenId(2),
                    steps: vec![hadamard.clone(), phase.clone()],
                }],
                quantum_outputs: vec![TokenId(2), TokenId(1)],
                classical_outputs: vec![],
                declared_effect: Effect::Unitary,
            };
            checked(&source, raw.clone());
            let mut wrong = raw;
            let RawOp::ApplyUnitary { steps, .. } = &mut wrong.operations[0] else {
                unreachable!()
            };
            steps.reverse();
            let accepted = kernel().accept_raw(wrong).unwrap();
            assert!(validate(&source, accepted.raw()).is_err());
        }

        let source = elaborate(
            "use std::quantum::phase_eighth;unitary fn turn(q:Q<Unit>)->Q<Unit>{phase_eighth(q)} pub unitary fn caller(c:Q<Bit>,q:Q<Unit>,r:Q<Bit>)->(Q<Bit>,Q<Unit>,Q<Bit>){let(c,q)=controlled(turn)(c,q);(c,q,r)}",
            "main::caller",
        );
        let raw = RawProgram {
            quantum_inputs: vec![
                QuantumPort {
                    token: TokenId(0),
                    shape: BasisShape::BIT,
                    wires: vec![WireId(0)],
                },
                QuantumPort {
                    token: TokenId(1),
                    shape: BasisShape { bits: 0 },
                    wires: vec![],
                },
                QuantumPort {
                    token: TokenId(2),
                    shape: BasisShape::BIT,
                    wires: vec![WireId(1)],
                },
            ],
            classical_inputs: vec![],
            operations: vec![
                RawOp::Join {
                    left: TokenId(0),
                    right: TokenId(1),
                    output: TokenId(3),
                },
                RawOp::ApplyUnitary {
                    input: TokenId(3),
                    output: TokenId(4),
                    steps: vec![crate::ir::CircuitStep {
                        controls: vec![crate::ir::BitControl {
                            index: 0,
                            when_one: true,
                        }],
                        action: CircuitAction::Monomial {
                            indices: vec![],
                            permutation: vec![0],
                            phases: vec![1],
                        },
                    }],
                },
                RawOp::Split {
                    input: TokenId(4),
                    left: TokenId(5),
                    right: TokenId(6),
                    left_bits: 1,
                },
            ],
            quantum_outputs: vec![TokenId(5), TokenId(6), TokenId(2)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());
        for mutation in 0..3 {
            let mut wrong = raw.clone();
            if mutation == 2 {
                let RawOp::Join { left, .. } = &mut wrong.operations[0] else {
                    unreachable!()
                };
                *left = TokenId(2);
                wrong.quantum_outputs = vec![TokenId(0), TokenId(6), TokenId(5)];
            } else {
                let RawOp::ApplyUnitary { steps, .. } = &mut wrong.operations[1] else {
                    unreachable!()
                };
                if mutation == 0 {
                    steps[0].controls.clear();
                } else {
                    let CircuitAction::Monomial { phases, .. } = &mut steps[0].action else {
                        unreachable!()
                    };
                    phases[0] = 7;
                }
            }
            let accepted = kernel().accept_raw(wrong).unwrap();
            assert!(validate(&source, accepted.raw()).is_err());
        }
    }
    use super::*;
    use crate::frontend::compile::ParsedProgram;
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

    #[test]
    fn ordinary_register_replay_rejects_native_valid_order_and_computation_faults() {
        let source = elaborate(
            "use std::classical::{empty_bits,prepend_bit};
            pub unitary fn main()->Bits<2>{prepend_bit[1](0,prepend_bit[0](1,empty_bits()))}",
            "main::main",
        );
        let proposal = source.lower_raw().unwrap();
        let accepted = kernel().accept(proposal.proposal()).unwrap();
        validate(&source, accepted.raw()).unwrap();
        let original = accepted.raw().clone();
        let mut reversed = original.clone();
        reversed.classical_outputs.reverse();
        let mut duplicated = original.clone();
        duplicated.classical_outputs[1] = duplicated.classical_outputs[0];
        let mut computed = original.clone();
        let RawOp::ClassicalConst { value, .. } = &mut computed.operations[0] else {
            panic!("first source constant")
        };
        *value = !*value;
        for fault in [reversed, duplicated, computed] {
            // Each counterexample passes the real native scope/ownership gate.
            let accepted_fault = kernel().accept_raw(fault).unwrap();
            assert!(validate(&source, accepted_fault.raw()).is_err());
            assert!(proposal.validate_source_steps(&accepted_fault).is_err());
        }
        let mut missing = original;
        missing.classical_outputs.pop();
        let accepted_fault = kernel().accept_raw(missing).unwrap();
        assert!(validate(&source, accepted_fault.raw()).is_err());
    }

    #[test]
    fn ordinary_register_storage_is_charged_before_emission() {
        let source = elaborate("pub unitary fn f(b:Bits<2>)->Bits<2>{b}", "main::f");
        let root = &source.definitions()[source.root()];
        let mut emitter = super::super::Emitter {
            source: &source,
            raw: crate::frontend::raw_state::RawState::new(),
            calls: 0,
            cells: MAX_CELLS - 1,
        };
        let error = emitter
            .charge_value(&root.inputs()[0], root.span())
            .unwrap_err();
        assert_eq!(error.code(), "limit");
        assert!(error.message().contains("value cells"));
        assert!(emitter.raw.operations.is_empty());
        assert!(emitter.raw.registers.is_empty());
        let parsed = ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "pub unitary fn f(b:Bits<9>)->Bits<9>{b}".into(),
        )]))
        .unwrap();
        let error = parsed
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.code(), "limit");
        assert!(error.message().contains("eight bits"));
    }

    fn kernel() -> Kernel {
        Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("select the matching native checker"))
    }

    fn checked(source: &ElaboratedProgram, raw: RawProgram) -> AcceptedProgram {
        let accepted = kernel().accept_raw(raw).unwrap();
        validate(source, accepted.raw()).unwrap();
        accepted
    }

    #[test]
    fn rectangular_constructor_subject_keeps_its_own_ports_and_suspended_caller() {
        let source = elaborate(
            "use std::quantum::{split,join};
            fn regroup(q:Q<(Bit,(Bit,Bit))>)->Q<((Bit,Bit),Bit)>{
                let(a,bc)=split(q);let(b,c)=split(bc);join(join(a,b),c)}
            fn invoke[const U:Op<((Bit,Bit),Bit) -> (Bit,(Bit,Bit))>](
                q:Q<((Bit,Bit),Bit)>,r:Q<Bit>)->(Q<(Bit,(Bit,Bit))>,Q<Bit>)
                requires Applicable(U){(U(q),r)}
            pub fn main(q:Q<((Bit,Bit),Bit)>,r:Q<Bit>)->(Q<(Bit,(Bit,Bit))>,Q<Bit>){
                invoke[adjoint(regroup)](q,r)}",
            "main::main",
        );
        let caller = source
            .definitions()
            .iter()
            .position(|d| d.path() == "main::invoke")
            .unwrap();
        let proposal = source.lower_raw_operation_at(caller, "U").unwrap();
        assert_eq!(proposal.definition_index(), caller);
        assert_eq!(proposal.operation_binding(), Some((caller, "U")));
        let accepted = kernel().accept(proposal.proposal()).unwrap();
        assert_eq!(accepted.raw().quantum_inputs.len(), 1);
        assert_eq!(accepted.raw().quantum_inputs[0].wires.len(), 3);
        proposal.validate_source_steps(&accepted).unwrap();
        let mut wrong = accepted.raw().clone();
        let RawOp::ApplyUnitary { steps, .. } = &mut wrong.operations[0] else {
            panic!("the general adjoint has one independently replayed circuit");
        };
        // Reversing the three logical axes is still a native-valid unitary.
        steps.push(crate::ir::CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: vec![0, 2],
                permutation: vec![0, 2, 1, 3],
                phases: vec![0; 4],
            },
        });
        let accepted = kernel().accept_raw(wrong).unwrap();
        assert!(
            validate_subject_with_kernel(
                &source,
                caller,
                proposal.operation(),
                accepted.raw(),
                Some(&kernel())
            )
            .is_err()
        );
        let root = source.lower_raw().unwrap();
        let accepted = kernel().accept(root.proposal()).unwrap();
        assert_eq!(accepted.raw().quantum_inputs.len(), 2);
        root.validate_source_steps(&accepted).unwrap();
    }

    #[test]
    fn constructor_replay_rejects_native_valid_gate_and_phase_substitutions() {
        let prefix = "use std::quantum::{x,h,phase};
            fn flip(q:Q<Bit>)->Q<Bit>{x(q)}
            fn had(q:Q<Bit>)->Q<Bit>{h(q)}
            fn twist(q:Q<Bit>)->Q<Bit>{phase[1,3](q)}";
        for (basis, operation) in [
            ("Bit", "then_op(flip,had)"),
            ("Bit", "adjoint(then_op(twist,had))"),
            ("(Bit,Bit)", "tensor_op(then_op(twist,twist),had)"),
            ("(Bit,Bit)", "controlled(adjoint(twist))"),
            ("Bit", "conjugate_op(then_op(twist,twist),had)"),
        ] {
            let text = format!("{prefix}
                fn invoke[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}> requires Applicable(U){{U(q)}}
                pub fn main(q:Q<{basis}>)->Q<{basis}>{{invoke[{operation}](q)}}");
            let source = elaborate(&text, "main::main");
            let proposal = source.lower_raw().unwrap();
            let accepted = kernel().accept(proposal.proposal()).unwrap();
            proposal.validate_source_steps(&accepted).unwrap();
            let mut wrong = accepted.raw().clone();
            let changed = wrong.operations.iter_mut().any(|step| match step {
                RawOp::Gate { gate, .. } => {
                    *gate = if *gate == SingleGate::X {
                        SingleGate::H
                    } else {
                        SingleGate::X
                    };
                    true
                }
                RawOp::ApplyUnitary { steps, .. } => steps.iter_mut().any(|step| {
                    if let CircuitAction::Monomial { phases, .. } = &mut step.action {
                        phases[0] = (phases[0] + 1) % 8;
                        true
                    } else {
                        false
                    }
                }),
                _ => false,
            });
            assert!(changed, "{operation}");
            let accepted = kernel().accept_raw(wrong).unwrap();
            assert!(validate(&source, accepted.raw()).is_err(), "{operation}");
        }
    }

    #[test]
    fn nested_forward_replay_rejects_native_valid_provider_and_caller_frame_substitutions() {
        let source = elaborate(
            "use std::quantum::x;unitary fn leaf(q:Q<Bit>)->Q<Bit>{x(q)}
            unitary fn helper[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
            pub unitary fn caller(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){(helper[leaf](q),r)}",
            "main::caller",
        );
        // Original two-owner interface and X action authored independently of
        // the emitter. The second owner remains suspended during both calls.
        let raw = RawProgram {
            quantum_inputs: vec![
                QuantumPort {
                    token: TokenId(0),
                    shape: BasisShape::BIT,
                    wires: vec![WireId(0)],
                },
                QuantumPort {
                    token: TokenId(1),
                    shape: BasisShape::BIT,
                    wires: vec![WireId(1)],
                },
            ],
            classical_inputs: vec![],
            operations: vec![RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(0),
                output: TokenId(2),
            }],
            quantum_outputs: vec![TokenId(2), TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());
        let mut wrong = raw.clone();
        wrong.operations[0] = RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(0),
            output: TokenId(2),
        };
        let accepted = kernel().accept_raw(wrong).unwrap();
        assert!(validate(&source, accepted.raw()).is_err());
        let mut wrong = raw;
        wrong.operations[0] = RawOp::Gate {
            gate: SingleGate::X,
            input: TokenId(1),
            output: TokenId(2),
        };
        wrong.quantum_outputs = vec![TokenId(0), TokenId(2)];
        let accepted = kernel().accept_raw(wrong).unwrap();
        assert!(validate(&source, accepted.raw()).is_err());
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
    fn packaged_product_replay_rejects_native_valid_axis_and_owner_substitutions() {
        let source = elaborate(
            "use std::quantum::{split,join};
             pub unitary fn f(q:Q<(Unit,(Bit,Bit))>)->Q<(Unit,(Bit,Bit))>{
                 let (u,r)=split(q); let (a,b)=split(r); join(u,join(b,a))}",
            "main::f",
        );
        // Independently authored instructions, including the zero-wire owner
        // and ordered physical wire slices. No emitter supplies this oracle.
        let raw = RawProgram {
            quantum_inputs: vec![crate::ir::QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(0), WireId(1)],
                shape: BasisShape { bits: 2 },
            }],
            classical_inputs: vec![],
            operations: vec![
                RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 0,
                },
                RawOp::Split {
                    input: TokenId(2),
                    left: TokenId(3),
                    right: TokenId(4),
                    left_bits: 1,
                },
                RawOp::Join {
                    left: TokenId(4),
                    right: TokenId(3),
                    output: TokenId(5),
                },
                RawOp::Join {
                    left: TokenId(1),
                    right: TokenId(5),
                    output: TokenId(6),
                },
            ],
            quantum_outputs: vec![TokenId(6)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        checked(&source, raw.clone());
        for changed in [
            // Same widths, fresh valid owners, different axis action.
            {
                let mut r = raw.clone();
                r.operations[2] = RawOp::Join {
                    left: TokenId(3),
                    right: TokenId(4),
                    output: TokenId(5),
                };
                r
            },
            // A valid zero-width partition is still the wrong original tree.
            {
                let mut r = raw.clone();
                r.operations[0] = RawOp::Split {
                    input: TokenId(0),
                    left: TokenId(1),
                    right: TokenId(2),
                    left_bits: 1,
                };
                r.operations[1] = RawOp::Split {
                    input: TokenId(2),
                    left: TokenId(3),
                    right: TokenId(4),
                    left_bits: 0,
                };
                r
            },
            // Native accepts this fresh owner, but the source's join order is fixed.
            {
                let mut r = raw.clone();
                r.operations[3] = RawOp::Join {
                    left: TokenId(5),
                    right: TokenId(1),
                    output: TokenId(6),
                };
                r
            },
        ] {
            let accepted = kernel().accept_raw(changed).unwrap();
            assert_eq!(
                validate(&source, accepted.raw()).unwrap_err().code(),
                "preservation"
            );
        }
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
    fn raw_source_replay_rejects_native_valid_scalar_substitutions() {
        for (basis, shape, wires) in [
            ("Unit", BasisShape::UNIT, vec![]),
            ("Bit", BasisShape::BIT, vec![WireId(0)]),
            ("(Unit,Unit)", BasisShape::UNIT, vec![]),
            ("(Unit,Bit,Unit)", BasisShape::BIT, vec![WireId(0)]),
            (
                "(Unit,(Bit,Bit))",
                BasisShape { bits: 2 },
                vec![WireId(0), WireId(1)],
            ),
        ] {
            let source = elaborate(
                &format!(
                    "use std::quantum::phase_eighth; pub unitary fn f(q: Q<{basis}>) -> Q<{basis}> {{ phase_eighth(q) }}"
                ),
                "main::f",
            );
            let raw = RawProgram {
                quantum_inputs: vec![QuantumPort {
                    token: TokenId(0),
                    shape,
                    wires,
                }],
                classical_inputs: vec![],
                operations: vec![RawOp::ApplyUnitary {
                    input: TokenId(0),
                    output: TokenId(1),
                    steps: vec![crate::ir::CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Monomial {
                            indices: vec![],
                            permutation: vec![0],
                            phases: vec![1],
                        },
                    }],
                }],
                quantum_outputs: vec![TokenId(1)],
                classical_outputs: vec![],
                declared_effect: Effect::Unitary,
            };
            checked(&source, raw.clone());
            for phase in [0, 2] {
                let mut changed = raw.clone();
                let RawOp::ApplyUnitary { steps, .. } = &mut changed.operations[0] else {
                    unreachable!()
                };
                let CircuitAction::Monomial { phases, .. } = &mut steps[0].action else {
                    unreachable!()
                };
                phases[0] = phase;
                let accepted = kernel().accept_raw(changed).unwrap();
                assert!(validate(&source, accepted.raw()).is_err());
            }
            if basis == "Bit" {
                let mut changed = raw;
                let RawOp::ApplyUnitary { steps, .. } = &mut changed.operations[0] else {
                    unreachable!()
                };
                steps[0].action = CircuitAction::Monomial {
                    indices: vec![0],
                    permutation: vec![0, 1],
                    phases: vec![0, 1],
                };
                let accepted = kernel().accept_raw(changed).unwrap();
                assert!(validate(&source, accepted.raw()).is_err());
            }
        }
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
    #[test]
    fn source_z_replay_rejects_native_valid_x_substitution() {
        let source = elaborate(
            "use std::quantum::z; pub unitary fn f(q:Q<Bit>)->Q<Bit>{z(q)}",
            "main::f",
        );
        let proposal = source.lower_raw().unwrap();
        let accepted = kernel().accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let mut fault = accepted.raw().clone();
        let [RawOp::Gate { gate, .. }] = fault.operations.as_mut_slice() else {
            panic!("one Z gate")
        };
        assert_eq!(*gate, SingleGate::Z);
        *gate = SingleGate::X;
        let valid_fault = kernel().accept_raw(fault).unwrap();
        assert!(validate(&source, valid_fault.raw()).is_err());
        assert!(proposal.validate_source_steps(&valid_fault).is_err());
    }
}
