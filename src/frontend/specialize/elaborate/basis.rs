//! Bounded ordinary-label evaluation of projected original checked occurrences.
//! Tables are untrusted proposals. Runtime owners and outer values never enter
//! the label environment; all calls retain their original declaration identity.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

struct Label {
    ty: SourceType,
    value: u16,
}

type Labels = BTreeMap<BinderKey, Label>;

impl Builder<'_> {
    pub(super) fn basis_cells(&mut self, ty: &SourceType, span: Span) -> Result<usize> {
        crate::frontend::check::type_size_budgeted(
            ty,
            4096,
            64,
            false,
            span,
            &mut |span, amount| {
                self.charge_cells(amount, span)
                    .map_err(crate::frontend::check::SourceError::from)
            },
        )
        .map(|size| size.nodes)
        .map_err(Error::from)
    }

    pub(super) fn basis_width(&mut self, ty: &SourceType, span: Span) -> Result<u32> {
        self.basis_cells(ty, span)?;
        // Both borrowed walks charge every visit/stack entry before allocation;
        // the width walk uses no recursive Rust calls outside the frame guard.
        self.charge_cells(1, span)?;
        let mut pending = vec![ty];
        let mut width = 0u32;
        while let Some(ty) = pending.pop() {
            self.charge_cells(1, span)?;
            let added = match &ty.kind {
                TypeKind::Unit => 0,
                TypeKind::Bit => 1,
                TypeKind::Bits(width) => *width,
                TypeKind::Tuple(fields) => {
                    self.charge_cells(fields.len(), span)?;
                    pending.extend(fields.iter().rev());
                    0
                }
                _ => {
                    return Err(error(
                        "type",
                        span,
                        "coherent label requires an exact ordinary basis",
                    ));
                }
            };
            width = width
                .checked_add(added)
                .ok_or_else(|| error("limit", span, "basis width overflow"))?;
            if width > 8 {
                return Err(error(
                    "limit",
                    span,
                    "coherent basis evaluation requires at most eight bits",
                ));
            }
        }
        Ok(width)
    }
    fn basis_tick(&mut self, span: Span, depth: usize) -> Result<()> {
        self.basis_work = self
            .basis_work
            .checked_add(1)
            .ok_or_else(|| error("limit", span, "basis work accounting overflow"))?;
        if self.basis_work > MAX_STEPS || depth > MAX_DEPTH {
            return Err(error(
                "limit",
                span,
                "basis evaluation exceeds existing work/depth bounds",
            ));
        }
        self.charge_cells(1, span)
    }

    fn label_pattern(
        &mut self,
        pattern: &Pattern,
        ty: &SourceType,
        value: u16,
        labels: &mut Labels,
        depth: usize,
    ) -> Result<()> {
        let span = match pattern {
            Pattern::Name(_, span) | Pattern::Wildcard(span) | Pattern::Tuple(_, span) => *span,
        };
        self.enter(span)?;
        let result = self.label_pattern_inner(pattern, ty, value, labels, depth);
        self.active_frames -= 1;
        result
    }

    fn label_pattern_inner(
        &mut self,
        pattern: &Pattern,
        ty: &SourceType,
        value: u16,
        labels: &mut Labels,
        depth: usize,
    ) -> Result<()> {
        let span = match pattern {
            Pattern::Name(_, span) | Pattern::Wildcard(span) | Pattern::Tuple(_, span) => *span,
        };
        self.basis_tick(span, depth)?;
        self.basis_width(ty, span)?;
        match pattern {
            Pattern::Name(name, _) => {
                let cells = self.basis_cells(ty, span)?;
                self.charge_cells(2 + name.key.name.len() + cells, span)?;
                if labels
                    .insert(
                        name.key.clone(),
                        Label {
                            ty: ty.clone(),
                            value,
                        },
                    )
                    .is_some()
                {
                    return Err(error("ownership", span, "duplicate original basis binder"));
                }
            }
            Pattern::Wildcard(_) => {}
            Pattern::Tuple(patterns, _) => {
                let fields = ty.pattern_fields(patterns.len()).ok_or_else(|| {
                    error(
                        "type",
                        span,
                        "basis pattern differs from its exact Unit/product tree",
                    )
                })?;
                let mut offset = 0;
                for (pattern, field) in patterns.iter().zip(fields) {
                    let bits = self.basis_width(field, span)?;
                    let label = (value >> offset) & ((1u16 << bits) - 1);
                    self.label_pattern(pattern, field, label, labels, depth + 1)?;
                    offset += bits;
                }
            }
        }
        Ok(())
    }

    fn label_expression(
        &mut self,
        expression: &Expr,
        labels: &Labels,
        lexical: &Arc<Table>,
        depth: usize,
    ) -> Result<Label> {
        self.enter(expression.span)?;
        let result = self.label_expression_inner(expression, labels, lexical, depth);
        self.active_frames -= 1;
        result
    }

    fn label_expression_inner(
        &mut self,
        expression: &Expr,
        labels: &Labels,
        lexical: &Arc<Table>,
        depth: usize,
    ) -> Result<Label> {
        let span = expression.span;
        self.basis_tick(span, depth)?;
        let result = match &expression.kind {
            ExprKind::Unit => Label {
                ty: SourceType::unit(),
                value: 0,
            },
            ExprKind::Name(reference) => {
                let label = reference.get(labels).ok_or_else(|| {
                    error(
                        "name",
                        span,
                        "basis value is outside its original isolated scope",
                    )
                })?;
                let cells = self.basis_cells(&label.ty, span)?;
                self.charge_cells(cells, span)?;
                Label {
                    ty: label.ty.clone(),
                    value: label.value,
                }
            }
            ExprKind::Tuple(fields) => {
                self.charge_cells(1 + fields.len(), span)?;
                let mut types = Vec::with_capacity(fields.len());
                let mut offset = 0;
                let mut value = 0;
                let mut nodes = 1usize;
                for field in fields {
                    let label = self.label_expression(field, labels, lexical, depth + 1)?;
                    let bits = self.basis_width(&label.ty, field.span)?;
                    nodes = nodes.saturating_add(self.basis_cells(&label.ty, span)?);
                    if offset + bits > 8 || nodes > 4096 {
                        return Err(error(
                            "limit",
                            span,
                            "coherent product exceeds basis capacity",
                        ));
                    }
                    value |= label.value << offset;
                    offset += bits;
                    types.push(label.ty);
                }
                Label {
                    ty: SourceType::tuple(types),
                    value,
                }
            }
            ExprKind::Boolean(operation, operands) => {
                if operands.len() != operation.arity() {
                    return Err(error("type", span, "basis Boolean operand arity differs"));
                }
                self.charge_cells(operands.len(), span)?;
                let mut values = Vec::with_capacity(operands.len());
                for operand in operands {
                    let label = self.label_expression(operand, labels, lexical, depth + 1)?;
                    if label.ty != SourceType::bit() {
                        return Err(error(
                            "type",
                            operand.span,
                            "basis Boolean operand is not exact Bit",
                        ));
                    }
                    values.push(label.value);
                }
                let value = match operation {
                    Boolean::Constant(value) => u16::from(*value),
                    Boolean::Not => values[0] ^ 1,
                    Boolean::And => values[0] & values[1],
                    Boolean::Xor => values[0] ^ values[1],
                };
                Label {
                    ty: SourceType::bit(),
                    value,
                }
            }
            ExprKind::Call(reference, statics, arguments) => {
                if !statics.is_empty() {
                    return Err(error(
                        "unsupported",
                        span,
                        "basis calls do not infer static arguments",
                    ));
                }
                match reference.target(lexical) {
                    ResolvedUse::Global(Target::Primitive(id)) => {
                        // Compare the original canonical primitive identity;
                        // no path String is allocated or source name re-resolved.
                        if id
                            != (crate::frontend::resolve::PrimitiveId {
                                module: "std::classical",
                                name: "empty_bits",
                            })
                            || !arguments.is_empty()
                        {
                            return Err(error(
                                "unsupported",
                                span,
                                "basis constructor is outside the admitted ordinary profile",
                            ));
                        }
                        Label {
                            ty: SourceType::bits(0),
                            value: 0,
                        }
                    }
                    ResolvedUse::Global(Target::Declaration(id)) => {
                        let interface = self.program.checked.interface(id);
                        if interface.kind != crate::frontend::ast::FnKind::Classical {
                            return Err(error(
                                "type",
                                span,
                                "basis call requires an original classical declaration",
                            ));
                        }
                        self.calls = self.calls.checked_add(1).ok_or_else(|| {
                            error("limit", span, "basis call accounting overflow")
                        })?;
                        if self.calls > MAX_CALLS {
                            return Err(error(
                                "limit",
                                span,
                                "basis calls exceed 1024 combined calls",
                            ));
                        }
                        self.charge_cells(1, span)?;
                        let (_, function) = self.program.definition(id)?;
                        let function = Arc::clone(function);
                        let program = self.program;
                        let closed = super::super::bindings::closed_interface_budgeted(
                            program,
                            id,
                            &BTreeMap::new(),
                            &BTreeMap::new(),
                            "basis classical call",
                            span,
                            |span, cells| self.charge_cells(cells, span),
                        )?;
                        if arguments.len() != closed.parameters.len()
                            || function.arguments.len() != arguments.len()
                            || !function.body.statements.is_empty()
                        {
                            return Err(error(
                                "type",
                                span,
                                "basis call differs from its complete checked interface",
                            ));
                        }
                        self.charge_cells(arguments.len(), span)?;
                        let mut actual = Vec::with_capacity(arguments.len());
                        for (argument, ty) in arguments.iter().zip(&closed.parameters) {
                            let label =
                                self.label_expression(argument, labels, lexical, depth + 1)?;
                            if label.ty != *ty {
                                return Err(error(
                                    "type",
                                    argument.span,
                                    "basis argument differs from its exact type tree",
                                ));
                            }
                            actual.push(label);
                        }
                        let mut inner = Labels::new();
                        for ((pattern, _), label) in function.arguments.iter().zip(actual) {
                            self.label_pattern(
                                pattern,
                                &label.ty,
                                label.value,
                                &mut inner,
                                depth + 1,
                            )?;
                        }
                        let label = self.label_expression(
                            &function.body.result,
                            &inner,
                            &function.lexical,
                            depth + 1,
                        )?;
                        if label.ty != closed.result {
                            return Err(error(
                                "type",
                                span,
                                "basis result differs from its exact declared tree",
                            ));
                        }
                        label
                    }
                    _ => {
                        return Err(error(
                            "name",
                            span,
                            "basis callee is not its original global definition",
                        ));
                    }
                }
            }
            _ => {
                return Err(error(
                    "unsupported",
                    span,
                    "basis evaluation requires a checked total ordinary body",
                ));
            }
        };
        let bits = self.basis_width(&result.ty, span)?;
        if usize::from(result.value) >= (1usize << bits) {
            return Err(error(
                "type",
                span,
                "basis label is outside its exact result tree",
            ));
        }
        Ok(result)
    }

    pub(super) fn basis_table(
        &mut self,
        input: &SourceType,
        pattern: &Pattern,
        body: &Expr,
        lexical: &Arc<Table>,
        span: Span,
    ) -> Result<(SourceType, Vec<u16>)> {
        let input_width = self.basis_width(input, span)?;
        let count = 1usize << input_width;
        // Both table slots and the complete bounded output seen-set are charged
        // before their allocation, including the one-label zero-width domain.
        self.charge_cells(count + 256, span)?;
        let mut table = Vec::with_capacity(count);
        let mut seen = vec![false; 256];
        let mut result_type = None;
        for label in 0..count {
            let mut labels = Labels::new();
            let value = u16::try_from(label)
                .map_err(|_| error("limit", span, "basis label conversion overflow"))?;
            self.label_pattern(pattern, input, value, &mut labels, 0)?;
            let output = self.label_expression(body, &labels, lexical, 0)?;
            if self.basis_width(&output.ty, span)? < input_width {
                return Err(error(
                    "type",
                    span,
                    "coherent basis lift cannot shrink its domain",
                ));
            }
            if result_type.as_ref().is_some_and(|ty| *ty != output.ty) {
                return Err(error(
                    "type",
                    span,
                    "coherent basis output varies its exact tree",
                ));
            }
            if seen[usize::from(output.value)] {
                return Err(error(
                    "ownership",
                    span,
                    "coherent basis lift is not injective",
                ));
            }
            seen[usize::from(output.value)] = true;
            if result_type.is_none() {
                result_type = Some(output.ty);
            }
            table.push(output.value);
        }
        Ok((
            result_type.expect("finite basis has at least one label"),
            table,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coherent_table_precharges_storage_and_combined_label_work() {
        let program = ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{basis q as x {not x}}".into(),
        )]))
        .unwrap();
        let id = program.checked.resolution.qualified("main::f").unwrap();
        let (_, function) = program.definition(id).unwrap();
        let ExprKind::CoherentLift { pattern, body, .. } = &function.body.result.kind else {
            panic!("original projected lift");
        };
        for (cells, work, frames) in [
            (MAX_CELLS - 256, 0, 0),
            (0, MAX_STEPS, 0),
            (0, 0, 63),
            (0, 0, 64),
        ] {
            let mut builder = Builder {
                program: &program,
                definitions: vec![],
                cache: BTreeMap::new(),
                active: BTreeSet::new(),
                calls: 0,
                folds: 0,
                steps: 0,
                cells,
                active_frames: frames,
                basis_work: work,
            };
            let error = builder
                .basis_table(
                    &SourceType::bit(),
                    pattern,
                    body,
                    &function.lexical,
                    function.span,
                )
                .unwrap_err();
            assert_eq!(error.code(), "limit");
            assert_eq!(
                builder.active_frames, frames,
                "basis failure restores the suspended caller depth"
            );
        }
    }
}
