//! Independent symbolic replay of original pure source access paths.
//! This reads source identities and logical axes, not the produced Raw trace.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{
    ElaboratedProgram, Kind, MAX_CALLS, MAX_CELLS, MAX_DEPTH, MAX_STEPS, Primitive, Result, Site,
    SourceOperation, SourceType, SourceValue, quantum_width,
};
use crate::ir::{BitControl, CircuitAction, CircuitStep};
use std::collections::{BTreeMap, BTreeSet};

/// Located by the independent source traversal, never by a producer receipt.
pub(super) struct Interval {
    pub(super) leaf: usize,
    pub(super) first: usize,
    pub(super) end: usize,
    pub(super) input: Vec<usize>,
    pub(super) output: Vec<usize>,
    pub(super) controls: Vec<usize>,
    pub(super) adjoint: bool,
}
pub(super) struct Expected {
    pub(super) steps: Vec<CircuitStep>,
    pub(super) intervals: Vec<Interval>,
}

#[derive(Clone)]
enum Logical {
    Classical,
    Quantum(Vec<usize>),
}
struct Frame {
    values: BTreeMap<u32, Logical>,
    issued: BTreeSet<u32>,
}
struct Trace<'a, 'b, 's> {
    source: &'a ElaboratedProgram,
    calls: &'b mut usize,
    cells: &'b mut usize,
    steps: Vec<CircuitStep>,
    site: Site<'s>,
    meanings: &'a [super::super::CheckedMeaning],
    intervals: Vec<Interval>,
}
impl Trace<'_, '_, '_> {
    fn charge(&mut self, n: usize) -> Result<()> {
        *self.cells = self.cells.saturating_add(n);
        if *self.cells > MAX_CELLS {
            return Err(self
                .site
                .error("limit", "source access replay exceeds value-cell bounds"));
        }
        Ok(())
    }
    fn call(&mut self, depth: usize) -> Result<()> {
        *self.calls = self.calls.saturating_add(1);
        if *self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(self
                .site
                .error("limit", "source access replay exceeds call/depth bounds"));
        }
        Ok(())
    }
    fn push(&mut self, step: CircuitStep) -> Result<()> {
        let count = 1
            + step.controls.len()
            + match &step.action {
                CircuitAction::Hadamard { .. } => 1,
                CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases,
                } => indices.len() + permutation.len() + phases.len(),
                CircuitAction::Contract { .. } => {
                    return Err(self
                        .site
                        .invalid("source access cannot be replaced by opaque evidence"));
                }
            };
        self.charge(count)?;
        if self.steps.len() >= MAX_STEPS {
            return Err(self
                .site
                .error("limit", "source access replay exceeds circuit-step bounds"));
        }
        self.steps.push(step);
        Ok(())
    }
    fn read(&mut self, value: &SourceValue, frame: &mut Frame) -> Result<Vec<Logical>> {
        self.charge(value.ty().owner_shape_size().nodes)?;
        match &value.ty().kind {
            Kind::Unit => Ok(vec![]),
            Kind::Bit | Kind::Q(_) => {
                let id = value
                    .identity()
                    .ok_or_else(|| self.site.invalid("source access atom has no identity"))?;
                let v = if value.ty().is_quantum() {
                    frame.values.remove(&id)
                } else {
                    frame.values.get(&id).cloned()
                }
                .ok_or_else(|| self.site.invalid("source access consumes an absent value"))?;
                match (&v, value.ty().is_quantum()) {
                    (Logical::Quantum(axes), true)
                        if quantum_width(value.ty()) == Some(axes.len()) => {}
                    (Logical::Classical, false) => {}
                    _ => {
                        return Err(self
                            .site
                            .invalid("source access read changes exact ownership shape"));
                    }
                }
                Ok(vec![v])
            }
            Kind::Tuple(fields) => {
                if fields.len() != value.fields().len() {
                    return Err(self.site.invalid("source access product changes arity"));
                }
                let mut result = Vec::new();
                for (ty, field) in fields.iter().zip(value.fields()) {
                    if ty != field.ty() {
                        return Err(self.site.invalid("source access product changes its tree"));
                    }
                    result.extend(self.read(field, frame)?);
                }
                Ok(result)
            }
            _ => Err(self.site.error(
                "unsupported",
                "source access replay requires the current exact finite basis profile",
            )),
        }
    }
    fn bind(&mut self, value: &SourceValue, actual: &[Logical], frame: &mut Frame) -> Result<()> {
        self.charge(value.ty().owner_shape_size().nodes)?;
        match &value.ty().kind {
            Kind::Unit if actual.is_empty() => Ok(()),
            Kind::Bit | Kind::Q(_) => {
                let [atom] = actual else {
                    return Err(self
                        .site
                        .invalid("source access binding changes atom count"));
                };
                match (atom, value.ty().is_quantum()) {
                    (Logical::Quantum(axes), true)
                        if quantum_width(value.ty()) == Some(axes.len()) => {}
                    (Logical::Classical, false) => {}
                    _ => {
                        return Err(self
                            .site
                            .invalid("source access binding changes exact ownership shape"));
                    }
                }
                self.charge(
                    1 + match atom {
                        Logical::Quantum(a) => a.len(),
                        Logical::Classical => 0,
                    },
                )?;
                let id = value
                    .identity()
                    .ok_or_else(|| self.site.invalid("source access binding has no identity"))?;
                if !frame.issued.insert(id) {
                    return Err(self.site.invalid("source access reissues a local identity"));
                }
                frame.values.insert(id, atom.clone());
                Ok(())
            }
            Kind::Tuple(fields) => {
                let mut offset = 0;
                for (ty, field) in fields.iter().zip(value.fields()) {
                    if ty != field.ty() {
                        return Err(self
                            .site
                            .invalid("source access result changes exact product tree"));
                    }
                    let n = super::super::atom_count(field.ty());
                    let slice = actual
                        .get(offset..offset + n)
                        .ok_or_else(|| self.site.invalid("source access result omits fields"))?;
                    self.bind(field, slice, frame)?;
                    offset += n;
                }
                if offset != actual.len() || fields.len() != value.fields().len() {
                    return Err(self
                        .site
                        .invalid("source access result changes product arity"));
                }
                Ok(())
            }
            _ => Err(self
                .site
                .invalid("source access result is unsupported or has extra atoms")),
        }
    }
    fn owner(&self, values: &[Logical]) -> Result<Vec<usize>> {
        match values {
            [Logical::Quantum(axes)] => Ok(axes.clone()),
            _ => Err(self
                .site
                .invalid("source access expects one complete quantum owner")),
        }
    }
    fn single(&self, values: &[Logical]) -> Result<usize> {
        let axes = self.owner(values)?;
        match axes.as_slice() {
            [axis] => Ok(*axis),
            _ => Err(self
                .site
                .invalid("source access gate requires exact Q<Bit>")),
        }
    }
    fn monomial(
        &mut self,
        indices: Vec<usize>,
        permutation: Vec<u16>,
        phases: Vec<u8>,
    ) -> Result<()> {
        self.push(CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            },
        })
    }
    fn operation(
        &mut self,
        op: &SourceOperation,
        arguments: Vec<Vec<Logical>>,
        depth: usize,
    ) -> Result<Vec<Logical>> {
        let first = self.steps.len();
        if self.meanings.is_empty() {
            return self.operation_inner(op, arguments, depth);
        }
        self.charge_binding(op)?;
        self.charge(self.meanings.len())?;
        let key = op.key();
        let leaves = self
            .meanings
            .iter()
            .enumerate()
            .filter_map(|(index, (required, _))| (*required == key).then_some(index))
            .collect::<Vec<_>>();
        let input = if leaves.is_empty() {
            vec![]
        } else {
            let [input] = arguments.as_slice() else {
                return Err(self.site.invalid("Meaning access changes argument arity"));
            };
            self.owner(input)?
        };
        let outputs = self.operation_inner(op, arguments, depth)?;
        if !leaves.is_empty() {
            let output = self.owner(&outputs)?;
            let (ports, effect, _) =
                super::super::operation_signature(op, self.source.definitions(), op.span())?;
            let basis = ports
                .input
                .quantum_basis()
                .and_then(super::super::finite_basis)
                .ok_or_else(|| self.site.invalid("Meaning access loses its exact basis"))?;
            if ports.input != ports.output || effect != crate::ir::Effect::Unitary {
                return Err(self
                    .site
                    .invalid("Meaning access changes its exact interface or effect"));
            }
            for leaf in leaves {
                if &basis != self.meanings[leaf].1.boundary().signature() {
                    return Err(self
                        .site
                        .invalid("Meaning access substitutes the original type tree"));
                }
                self.charge(1 + input.len() + output.len())?;
                if self.intervals.len() >= MAX_CALLS {
                    return Err(self
                        .site
                        .error("limit", "source access exceeds 1024 Meaning intervals"));
                }
                self.intervals.push(Interval {
                    leaf,
                    first,
                    end: self.steps.len(),
                    input: input.clone(),
                    output: output.clone(),
                    controls: vec![],
                    adjoint: false,
                });
            }
        }
        Ok(outputs)
    }
    fn operation_inner(
        &mut self,
        op: &SourceOperation,
        arguments: Vec<Vec<Logical>>,
        depth: usize,
    ) -> Result<Vec<Logical>> {
        if let Some(id) = op.definition() {
            return self.function(id, arguments, depth);
        }
        self.call(depth)?;
        if let Some((kind, children, ports)) = op.constructed() {
            use crate::frontend::specialize::ast::OperationConstructor as C;
            return match kind {
                C::Then => {
                    let middle = self.operation(&children[0], arguments, depth + 1)?;
                    self.operation(&children[1], vec![middle], depth + 1)
                }
                C::Adjoint => self.transform(&children[0], arguments, depth + 1, false),
                C::Conjugate => {
                    let first = self.transform(&children[0], arguments, depth + 1, false)?;
                    let middle = self.operation(&children[1], vec![first], depth + 1)?;
                    self.operation(&children[0], vec![middle], depth + 1)
                }
                C::Tensor | C::Controlled => {
                    let [input]: [Vec<Logical>; 1] = arguments.try_into().map_err(|_| {
                        self.site.invalid("packed operation argument arity differs")
                    })?;
                    let axes = self.owner(&input)?;
                    let fields = ports
                        .input
                        .quantum_basis()
                        .and_then(SourceType::tuple_fields)
                        .filter(|fields| fields.len() == 2)
                        .ok_or_else(|| self.site.invalid("packed operation input tree differs"))?;
                    let n = fields[0]
                        .basis_width()
                        .ok_or_else(|| self.site.invalid("packed operation is not finite"))?
                        as usize;
                    if n > axes.len() {
                        return Err(self.site.invalid("packed operation field exceeds axes"));
                    }
                    self.charge(axes.len() + 2)?;
                    let left = vec![Logical::Quantum(axes[..n].to_vec())];
                    let right = vec![Logical::Quantum(axes[n..].to_vec())];
                    let output = if kind == C::Tensor {
                        let left = self.operation(&children[0], vec![left], depth + 1)?;
                        let right = self.operation(&children[1], vec![right], depth + 1)?;
                        let mut axes = self.owner(&left)?;
                        axes.extend(self.owner(&right)?);
                        axes
                    } else {
                        let outputs =
                            self.transform(&children[0], vec![left, right], depth + 1, true)?;
                        let [Logical::Quantum(left), Logical::Quantum(right)] = outputs.as_slice()
                        else {
                            return Err(self.site.invalid("packed control changes owner arity"));
                        };
                        let mut axes = left.clone();
                        axes.extend(right);
                        axes
                    };
                    Ok(vec![Logical::Quantum(output)])
                }
            };
        }
        let [mut value]: [Vec<Logical>; 1] = arguments.try_into().map_err(|_| {
            self.site
                .invalid("source repetition changes whole argument arity")
        })?;
        let child = op
            .child()
            .ok_or_else(|| self.site.invalid("source repetition omits its child"))?;
        for _ in 0..op
            .repeat_count()
            .ok_or_else(|| self.site.invalid("source repetition has no count"))?
        {
            value = self.operation(child, vec![value], depth + 1)?;
        }
        Ok(value)
    }
    fn charge_binding(&mut self, op: &SourceOperation) -> Result<()> {
        // Key comparison below expands every ordered child, including children
        // of zero repetitions. Bound that traversal before allocating either key.
        let mut pending = vec![(op, 0)];
        while let Some((operation, depth)) = pending.pop() {
            self.charge(1)?;
            if depth > MAX_DEPTH {
                return Err(self
                    .site
                    .error("limit", "source access binding exceeds depth bounds"));
            }
            pending.extend(operation.children().iter().map(|child| (child, depth + 1)));
        }
        Ok(())
    }
    fn function(
        &mut self,
        id: usize,
        arguments: Vec<Vec<Logical>>,
        depth: usize,
    ) -> Result<Vec<Logical>> {
        self.call(depth)?;
        let source = self.source;
        let definition = source.definitions().get(id).ok_or_else(|| {
            self.site
                .invalid("source access calls a missing definition")
        })?;
        if definition.effect() != "unitary" || arguments.len() != definition.inputs().len() {
            return Err(self
                .site
                .invalid("source access calls a non-pure or different interface"));
        }
        let mut frame = Frame {
            values: BTreeMap::new(),
            issued: BTreeSet::new(),
        };
        for (input, actual) in definition.inputs().iter().zip(arguments) {
            self.bind(input, &actual, &mut frame)?;
        }
        for step in definition.steps() {
            // This symbolic transformed trace has no original Raw call interval
            // on which to obtain a fresh native sector decision. Do not erase a
            // retained control obligation while constructing an inverse/control.
            step.check_access_contract()?;
            if step.effect() != "unitary" {
                return Err(self.site.invalid("source access contains a non-pure step"));
            }
            let mut inputs = Vec::new();
            for input in step.inputs() {
                inputs.push(self.read(input, &mut frame)?);
            }
            let output = if step.boolean().is_some() {
                vec![Logical::Classical]
            } else if let Some(p) = step.partition() {
                let size = p.end.checked_sub(p.start).ok_or_else(|| {
                    self.site
                        .invalid("source place reverses its ordered interval")
                })?;
                if p.end > p.width || p.width > 8 || (p.bit && size != 1) {
                    return Err(self.site.invalid("source place loses its static bounds"));
                }
                self.charge(4 + p.width as usize * 2)?;
                if p.taking {
                    let [input] = inputs.as_slice() else {
                        return Err(self.site.invalid("source place changes extraction arity"));
                    };
                    let mut axes = self.owner(input)?;
                    if axes.len() != p.width as usize {
                        return Err(self
                            .site
                            .invalid("source place changes original parent width"));
                    }
                    let selected = axes.drain(p.start as usize..p.end as usize).collect();
                    vec![Logical::Quantum(selected), Logical::Quantum(axes)]
                } else {
                    let [selected, rest] = inputs.as_slice() else {
                        return Err(self
                            .site
                            .invalid("source place changes reconstruction arity"));
                    };
                    let selected = self.owner(selected)?;
                    let mut axes = self.owner(rest)?;
                    if selected.len() != size as usize
                        || axes.len() + selected.len() != p.width as usize
                        || selected.iter().any(|axis| axes.contains(axis))
                    {
                        return Err(self.site.invalid(
                            "source place reconstruction changes or aliases ordered axes",
                        ));
                    }
                    axes.splice(p.start as usize..p.start as usize, selected);
                    vec![Logical::Quantum(axes)]
                }
            } else if let Some(child) = step.called_definition() {
                let callee = source
                    .definitions()
                    .get(child)
                    .ok_or_else(|| self.site.invalid("source access calls a missing callee"))?;
                if step.inputs().len() != callee.inputs().len()
                    || step
                        .inputs()
                        .iter()
                        .zip(callee.inputs())
                        .any(|(a, b)| a.ty() != b.ty())
                    || step.output().ty() != callee.output().ty()
                {
                    return Err(self
                        .site
                        .invalid("source access call changes exact type trees"));
                }
                let actual = step
                    .operation_bindings()
                    .ok_or_else(|| self.site.invalid("source access call has no binding map"))?;
                if actual.len() != callee.operations().len() {
                    return Err(self
                        .site
                        .invalid("source access call changes operation arity"));
                }
                for (name, operation) in actual {
                    let retained = callee.operations().get(name).ok_or_else(|| {
                        self.site
                            .invalid("source access substitutes a parameter identity")
                    })?;
                    for op in [operation, retained] {
                        self.charge_binding(op)?;
                    }
                    if operation.key() != retained.key() {
                        return Err(self
                            .site
                            .invalid("source access substitutes a provider or original Meaning"));
                    }
                }
                self.function(child, inputs, depth + 1)?
            } else if let Some(op) = step.operation() {
                if step.kind() == "apply" {
                    self.operation(op, inputs, depth + 1)?
                } else {
                    self.transform(op, inputs, depth + 1, step.kind() == "controlled")?
                }
            } else {
                match step
                    .primitive_kind()
                    .ok_or_else(|| self.site.invalid("source access has no primitive"))?
                {
                    Primitive::Unit => {
                        if inputs.len() != 1
                            || !inputs[0].is_empty()
                            || step.inputs()[0].ty() != &SourceType::unit()
                            || step.output().ty() != &SourceType::quantum(SourceType::unit())
                        {
                            return Err(self
                                .site
                                .invalid("source Unit introduction changes its exact interface"));
                        }
                        vec![Logical::Quantum(vec![])]
                    }
                    Primitive::Finish => {
                        if inputs.len() != 1
                            || step.inputs()[0].ty() != &SourceType::quantum(SourceType::unit())
                            || step.output().ty() != &SourceType::unit()
                            || !self.owner(&inputs[0])?.is_empty()
                        {
                            return Err(self
                                .site
                                .invalid("source Unit consumption changes its exact interface"));
                        }
                        vec![]
                    }
                    Primitive::H | Primitive::X | Primitive::Z => {
                        let a = self.single(&inputs[0])?;
                        if step.primitive_kind() == Some(Primitive::H) {
                            self.push(CircuitStep {
                                controls: vec![],
                                action: CircuitAction::Hadamard { target: a },
                            })?;
                        } else if step.primitive_kind() == Some(Primitive::X) {
                            self.monomial(vec![a], vec![1, 0], vec![0, 0])?;
                        } else {
                            self.monomial(vec![a], vec![0, 1], vec![0, 4])?;
                        }
                        inputs[0].clone()
                    }
                    Primitive::Phase => {
                        let [j, k] = step.natural_arguments() else {
                            return Err(self
                                .site
                                .invalid("source phase has the wrong static arity"));
                        };
                        if *k > 8 || *j >= 1u32 << k || (j * 8) % (1u32 << k) != 0 {
                            return Err(self.site.error(
                                "unsupported",
                                "source access phase is not an exact eighth-turn",
                            ));
                        }
                        let a = self.single(&inputs[0])?;
                        for _ in 0..j * 8 / (1u32 << k) {
                            self.monomial(vec![a], vec![0, 1], vec![0, 1])?;
                        }
                        inputs[0].clone()
                    }
                    Primitive::PhaseEighth => {
                        self.monomial(vec![], vec![0], vec![1])?;
                        inputs[0].clone()
                    }
                    Primitive::Cnot => {
                        let a = self.single(&inputs[0])?;
                        let b = self.single(&inputs[1])?;
                        if a == b {
                            return Err(self.site.invalid("source access Cnot aliases its axes"));
                        }
                        self.monomial(vec![a, b], vec![0, 3, 2, 1], vec![0; 4])?;
                        inputs.into_iter().flatten().collect()
                    }
                    Primitive::Split => {
                        let axes = self.owner(&inputs[0])?;
                        let fields = step.inputs()[0]
                            .ty()
                            .quantum_basis()
                            .and_then(SourceType::tuple_fields)
                            .filter(|v| v.len() == 2)
                            .ok_or_else(|| {
                                self.site.invalid("source split changes its exact product")
                            })?;
                        let n = fields[0]
                            .basis_width()
                            .ok_or_else(|| self.site.invalid("source split has no closed width"))?
                            as usize;
                        if n > axes.len() {
                            return Err(self.site.invalid("source split exceeds its owner"));
                        }
                        vec![
                            Logical::Quantum(axes[..n].to_vec()),
                            Logical::Quantum(axes[n..].to_vec()),
                        ]
                    }
                    Primitive::Join => {
                        let mut axes = self.owner(&inputs[0])?;
                        axes.extend(self.owner(&inputs[1])?);
                        vec![Logical::Quantum(axes)]
                    }
                    Primitive::TakeBit | Primitive::PutBit => {
                        let [n, k] = step.natural_arguments() else {
                            return Err(self
                                .site
                                .invalid("source register access loses static arguments"));
                        };
                        if k >= n || *n > 8 {
                            return Err(self
                                .site
                                .invalid("source register access loses static bounds"));
                        }
                        self.charge(4 + *n as usize * 2)?;
                        if step.primitive_kind() == Some(Primitive::TakeBit) {
                            let mut axes = self.owner(&inputs[0])?;
                            if axes.len() != *n as usize {
                                return Err(self
                                    .site
                                    .invalid("source take_bit changes its register width"));
                            }
                            let bit = axes.remove(*k as usize);
                            vec![Logical::Quantum(vec![bit]), Logical::Quantum(axes)]
                        } else {
                            let bit = self.single(&inputs[0])?;
                            let mut axes = self.owner(&inputs[1])?;
                            if axes.len() + 1 != *n as usize || axes.contains(&bit) {
                                return Err(self
                                    .site
                                    .invalid("source put_bit changes or aliases its axes"));
                            }
                            axes.insert(*k as usize, bit);
                            vec![Logical::Quantum(axes)]
                        }
                    }
                    _ => {
                        return Err(self.site.error(
                            "unsupported",
                            "source access replay requires the current exact pure circuit profile",
                        ));
                    }
                }
            };
            self.bind(step.output(), &output, &mut frame)?;
        }
        let output = self.read(definition.output(), &mut frame)?;
        if frame
            .values
            .values()
            .any(|v| matches!(v, Logical::Quantum(_)))
        {
            return Err(self
                .site
                .invalid("source access drops a quantum owner, including zero-width owners"));
        }
        Ok(output)
    }
    fn canonical(&mut self, op: &SourceOperation, depth: usize) -> Result<usize> {
        let mut pending = vec![(op, 0)];
        while let Some((operation, level)) = pending.pop() {
            if level > MAX_DEPTH {
                return Err(self
                    .site
                    .error("limit", "source access operation exceeds depth bounds"));
            }
            if !operation.children().is_empty() {
                self.charge(1)?;
                pending.extend(operation.children().iter().map(|child| (child, level + 1)));
            }
        }
        let (ports, effect, _) =
            super::super::operation_signature(op, self.source.definitions(), op.span())?;
        if effect != crate::ir::Effect::Unitary {
            return Err(self
                .site
                .invalid("source access requires principal Unitary effect"));
        }
        let width = quantum_width(ports.input).ok_or_else(|| {
            self.site
                .invalid("source access provider is not a finite quantum owner")
        })?;
        self.charge(width)?;
        let first_interval = self.intervals.len();
        let output = self.operation(
            op,
            vec![vec![Logical::Quantum((0..width).collect())]],
            depth,
        )?;
        let desired = self.owner(&output)?;
        if desired.len() != width {
            return Err(self.site.invalid("source access changes axis count"));
        }
        let mut arrangement: Vec<_> = (0..width).collect();
        for position in 0..width {
            if arrangement[position] != desired[position] {
                let other = arrangement
                    .iter()
                    .position(|axis| *axis == desired[position])
                    .ok_or_else(|| self.site.invalid("source access loses an original axis"))?;
                self.monomial(vec![position, other], vec![0, 2, 1, 3], vec![0; 4])?;
                arrangement.swap(position, other);
            }
        }
        if !self.meanings.is_empty() {
            self.charge_binding(op)?;
            let key = op.key();
            for interval in &mut self.intervals[first_interval..] {
                if self.meanings[interval.leaf].0 == key {
                    // Include the actual canonical output routing in this
                    // whole-operation equation, before any inverse/control.
                    interval.end = self.steps.len();
                    interval.output = (0..width).collect();
                }
            }
        }
        Ok(width)
    }
    fn transform(
        &mut self,
        op: &SourceOperation,
        arguments: Vec<Vec<Logical>>,
        depth: usize,
        controlled: bool,
    ) -> Result<Vec<Logical>> {
        let target = self.owner(&arguments[usize::from(controlled)])?;
        let control = if controlled {
            Some(self.single(&arguments[0])?)
        } else {
            None
        };
        let mut child = Trace {
            source: self.source,
            calls: &mut *self.calls,
            cells: &mut *self.cells,
            steps: Vec::new(),
            site: self.site,
            meanings: self.meanings,
            intervals: Vec::new(),
        };
        let width = child.canonical(op, depth)?;
        if width != target.len() {
            return Err(self.site.invalid("source access changes its target axes"));
        }
        let count = child.steps.len();
        let Trace {
            mut steps,
            mut intervals,
            ..
        } = child;
        let first = self.steps.len();
        for interval in &mut intervals {
            if !controlled {
                (interval.first, interval.end) = (count - interval.end, count - interval.first);
                std::mem::swap(&mut interval.input, &mut interval.output);
                interval.adjoint = !interval.adjoint;
            }
            for axis in interval
                .input
                .iter_mut()
                .chain(&mut interval.output)
                .chain(&mut interval.controls)
            {
                *axis = target[*axis];
            }
            if let Some(control) = control {
                interval.controls.push(control);
            }
            interval.first += first;
            interval.end += first;
        }
        if !controlled {
            invert(&mut steps, self.site)?;
        }
        for mut step in steps {
            route(&mut step, &target);
            if let Some(index) = control {
                step.controls.push(BitControl {
                    index,
                    when_one: true,
                });
            }
            self.push(step)?;
        }
        self.charge(
            intervals
                .iter()
                .map(|i| 1 + i.input.len() + i.output.len() + i.controls.len())
                .sum(),
        )?;
        if self.intervals.len() + intervals.len() > MAX_CALLS {
            return Err(self
                .site
                .error("limit", "source access exceeds 1024 Meaning intervals"));
        }
        self.intervals.extend(intervals);
        Ok(arguments.into_iter().flatten().collect())
    }
}
fn route(step: &mut CircuitStep, axes: &[usize]) {
    match &mut step.action {
        CircuitAction::Hadamard { target } => *target = axes[*target],
        CircuitAction::Monomial { indices, .. } | CircuitAction::Contract { indices, .. } => {
            for i in indices {
                *i = axes[*i];
            }
        }
    }
    for control in &mut step.controls {
        control.index = axes[control.index];
    }
}
fn invert(steps: &mut [CircuitStep], site: Site<'_>) -> Result<()> {
    steps.reverse();
    for step in steps {
        match &mut step.action {
            CircuitAction::Hadamard { .. } => {}
            CircuitAction::Monomial {
                permutation,
                phases,
                ..
            } => {
                let mut inverse = vec![0; permutation.len()];
                let mut conjugate = vec![0; phases.len()];
                for (column, row) in permutation.iter().copied().enumerate() {
                    let row = usize::from(row);
                    if row >= inverse.len() || column >= phases.len() {
                        return Err(site.invalid("source access permutation is malformed"));
                    }
                    inverse[row] = column as u16;
                    conjugate[row] = (8 - phases[column]) % 8;
                }
                *permutation = inverse;
                *phases = conjugate;
            }
            CircuitAction::Contract { .. } => {
                return Err(
                    site.invalid("source inverse cannot acquire an opaque contract assertion")
                );
            }
        }
    }
    Ok(())
}

pub(super) fn expected_with_meanings(
    source: &ElaboratedProgram,
    op: &SourceOperation,
    depth: usize,
    calls: &mut usize,
    cells: &mut usize,
    requirements: (&[super::super::CheckedMeaning], bool),
    site: Site<'_>,
) -> Result<Expected> {
    let (meanings, controlled) = requirements;
    let mut trace = Trace {
        source,
        calls,
        cells,
        steps: Vec::new(),
        site,
        meanings,
        intervals: Vec::new(),
    };
    let width = trace.canonical(op, depth)?;
    if controlled {
        let axes: Vec<_> = (1..=width).collect();
        for step in &mut trace.steps {
            route(step, &axes);
            step.controls.push(BitControl {
                index: 0,
                when_one: true,
            });
        }
    } else {
        invert(&mut trace.steps, site)?;
    }
    let count = trace.steps.len();
    for interval in &mut trace.intervals {
        if controlled {
            for axis in interval
                .input
                .iter_mut()
                .chain(&mut interval.output)
                .chain(&mut interval.controls)
            {
                *axis += 1;
            }
            interval.controls.push(0);
        } else {
            (interval.first, interval.end) = (count - interval.end, count - interval.first);
            std::mem::swap(&mut interval.input, &mut interval.output);
            interval.adjoint = !interval.adjoint;
        }
    }
    Ok(Expected {
        steps: trace.steps,
        intervals: trace.intervals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;

    fn source(operation: &str, basis: &str) -> ElaboratedProgram {
        let text = format!(
            "unitary fn leaf(q:Q<Bit>)->Q<Bit>{{q}}
             unitary fn invoke[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}>
                requires Applicable(U){{U(q)}}
             pub unitary fn main(q:Q<{basis}>)->Q<{basis}>{{invoke[{operation}](q)}}"
        );
        ParsedProgram::parse(BTreeMap::from([("main".into(), text)]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
    }

    #[test]
    fn access_binding_checks_depth_of_nonrepeat_children_before_key_expansion() {
        for (depth, succeeds) in [(MAX_DEPTH, true), (MAX_DEPTH + 1, false)] {
            // The right child contributes no executed circuit steps. Its full
            // identity still participates in the call's provider-key comparison.
            let mut child = "leaf".to_owned();
            for _ in 1..depth {
                child = format!("power({child},0)");
            }
            let source = source(&format!("then_op(leaf,{child})"), "Bit");
            let root = &source.definitions()[source.root()];
            let binding = root
                .steps()
                .iter()
                .find_map(|step| step.operation_bindings())
                .unwrap()
                .get("U")
                .unwrap();
            let mut calls = 0;
            let mut cells = 0;
            let mut trace = Trace {
                source: &source,
                calls: &mut calls,
                cells: &mut cells,
                steps: Vec::new(),
                site: Site::definition(root),
                meanings: &[],
                intervals: Vec::new(),
            };
            let result = trace.charge_binding(binding);
            assert_eq!(result.is_ok(), succeeds, "depth={depth}");
            if let Err(error) = result {
                assert_eq!(error.code(), "limit");
                assert!(error.message().contains("depth bounds"));
            }
            assert!(trace.steps.is_empty());
        }
    }

    #[test]
    fn access_binding_charges_all_constructor_children_even_below_zero_repeat() {
        for (basis, operation, nodes) in [
            ("Bit", "leaf", 1),
            ("Bit", "power(leaf,0)", 2),
            ("Bit", "then_op(leaf,leaf)", 3),
            ("(Bit,Bit)", "tensor_op(leaf,leaf)", 3),
            ("Bit", "adjoint(then_op(leaf,leaf))", 4),
            ("(Bit,Bit)", "controlled(adjoint(leaf))", 3),
            ("Bit", "conjugate_op(leaf,leaf)", 3),
            ("Bit", "then_op(leaf,power(adjoint(leaf),0))", 5),
        ] {
            let source = source(operation, basis);
            let root = &source.definitions()[source.root()];
            let binding = root
                .steps()
                .iter()
                .find_map(|step| step.operation_bindings())
                .unwrap()
                .get("U")
                .unwrap();
            for (initial, succeeds) in [
                (0, true),
                (MAX_CELLS - nodes, true),
                (MAX_CELLS - nodes + 1, false),
            ] {
                let mut cells = initial;
                let mut calls = 0;
                let mut trace = Trace {
                    source: &source,
                    calls: &mut calls,
                    cells: &mut cells,
                    steps: Vec::new(),
                    site: Site::definition(root),
                    meanings: &[],
                    intervals: Vec::new(),
                };
                let result = trace.charge_binding(binding);
                assert_eq!(result.is_ok(), succeeds, "{operation}, initial={initial}");
                if let Err(error) = result {
                    assert_eq!(error.code(), "limit");
                }
                assert!(trace.steps.is_empty());
                assert_eq!(calls, 0);
                assert_eq!(cells, initial + nodes, "{operation}");
            }
        }
    }
}
