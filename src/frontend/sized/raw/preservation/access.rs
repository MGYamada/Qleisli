//! Independent symbolic replay of original pure source access paths.
//! This reads source identities and logical axes, not the produced Raw trace.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{
    ElaboratedProgram, Kind, MAX_CALLS, MAX_CELLS, MAX_DEPTH, MAX_STEPS, Primitive, Result, Site,
    SourceOperation, SourceType, SourceValue, quantum_width,
};
use crate::ir::{BitControl, CircuitAction, CircuitStep};
use std::collections::{BTreeMap, BTreeSet};

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
        if let Some(id) = op.definition() {
            return self.function(id, arguments, depth);
        }
        self.call(depth)?;
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
            if step.effect() != "unitary" {
                return Err(self.site.invalid("source access contains a non-pure step"));
            }
            let mut inputs = Vec::new();
            for input in step.inputs() {
                inputs.push(self.read(input, &mut frame)?);
            }
            let output = if step.boolean().is_some() {
                vec![Logical::Classical]
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
                        let mut op = op;
                        let mut d = 0;
                        loop {
                            self.charge(1)?;
                            if d > MAX_DEPTH {
                                return Err(self
                                    .site
                                    .error("limit", "source access binding exceeds depth bounds"));
                            }
                            if let Some(child) = op.child() {
                                op = child;
                                d += 1;
                            } else {
                                break;
                            }
                        }
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
                    Primitive::H | Primitive::X => {
                        let a = self.single(&inputs[0])?;
                        if step.primitive_kind() == Some(Primitive::H) {
                            self.push(CircuitStep {
                                controls: vec![],
                                action: CircuitAction::Hadamard { target: a },
                            })?;
                        } else {
                            self.monomial(vec![a], vec![1, 0], vec![0, 0])?;
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
        let mut base = op;
        let mut d = 0;
        while let Some(child) = base.child() {
            self.charge(1)?;
            d += 1;
            if d > MAX_DEPTH {
                return Err(self
                    .site
                    .error("limit", "source access operation exceeds depth bounds"));
            }
            base = child;
        }
        let definition = &self.source.definitions()[base
            .definition()
            .ok_or_else(|| self.site.invalid("source access has no closed provider"))?];
        let [input] = definition.inputs() else {
            return Err(self.site.invalid("source access provider is not unary"));
        };
        if input.ty() != definition.output().ty() {
            return Err(self
                .site
                .invalid("source access provider changes its exact endomorphism tree"));
        }
        let width = quantum_width(input.ty()).ok_or_else(|| {
            self.site
                .invalid("source access provider is not a finite quantum owner")
        })?;
        self.charge(width)?;
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
        };
        let width = child.canonical(op, depth)?;
        if width != target.len() {
            return Err(self.site.invalid("source access changes its target axes"));
        }
        let mut steps = child.steps;
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

pub(super) fn expected(
    source: &ElaboratedProgram,
    op: &SourceOperation,
    depth: usize,
    calls: &mut usize,
    cells: &mut usize,
    controlled: bool,
    site: Site<'_>,
) -> Result<Vec<CircuitStep>> {
    let mut trace = Trace {
        source,
        calls,
        cells,
        steps: Vec::new(),
        site,
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
    Ok(trace.steps)
}
