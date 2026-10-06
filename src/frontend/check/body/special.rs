//! Ordinary finite meanings and isolated quantum evidence obligations.
use super::*;

impl Checker<'_, '_> {
    pub(super) fn basis_expr(&mut self, expr: &BasisExpr, scope: &mut Scope) -> Result<Ty> {
        if self.depth >= 64 {
            return Err(SourceError::new(
                "limit",
                expr.span,
                "source expression exceeds depth 64",
            ));
        }
        self.depth += 1;
        let result = self.basis_inner(expr, scope);
        self.depth -= 1;
        result
    }
    fn basis_inner(&mut self, expr: &BasisExpr, scope: &mut Scope) -> Result<Ty> {
        self.tick(expr.span)?;
        let result = match &expr.kind {
            BasisExprKind::Name(name) => {
                let key = self
                    .local(name)
                    .ok_or_else(|| SourceError::new("name", name.span, "unbound basis value"))?;
                let value = scope
                    .values
                    .get(key)
                    .ok_or_else(|| SourceError::new("name", name.span, "unbound basis value"))?;
                if value.ty.linear() {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "basis expression requires an ordinary value",
                    ));
                }
                self.program.budget.copy_ty(name.span, &value.ty)?
            }
            BasisExprKind::Unit => Ty::unit(),
            BasisExprKind::Bit(_) => Ty::bit(),
            BasisExprKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        expr.span,
                        "basis tuple exceeds 64 fields",
                    ));
                }
                self.program.budget.charge(expr.span, fields.len() + 1)?;
                let mut result = Vec::new();
                let mut cells = 1usize;
                for field in fields {
                    let value = self.basis_expr(field, scope)?;
                    cells = cells
                        .checked_add(self.program.budget.ty(field.span, &value)?)
                        .ok_or_else(|| {
                            SourceError::new("limit", expr.span, "basis tuple cell count overflow")
                        })?;
                    if cells > 4096 {
                        return Err(SourceError::new(
                            "limit",
                            expr.span,
                            "basis tuple exceeds 4096 cells",
                        ));
                    }
                    result.push(value);
                }
                Ty::tuple(result)
            }
            BasisExprKind::Call { callee, args } => {
                if self.local(callee).is_some() {
                    return Err(SourceError::new(
                        "type",
                        callee.span,
                        "a basis value is not callable",
                    ));
                }
                let Target::Declaration(id) = self.resolve(callee)? else {
                    return Err(SourceError::new(
                        "type",
                        callee.span,
                        "basis expression requires a basis function",
                    ));
                };
                if self.program.decl(id).kind != FnKind::Basis {
                    return Err(SourceError::new(
                        "type",
                        callee.span,
                        "basis expression requires a basis function",
                    ));
                }
                let (params, result, _) = self.specialize(id, &[], scope, callee.span, false)?;
                if params.len() != args.len() {
                    return Err(SourceError::new(
                        "arity",
                        callee.span,
                        "basis function argument arity mismatch",
                    ));
                }
                for (arg, expected) in args.iter().zip(&params) {
                    let actual = self.basis_expr(arg, scope)?;
                    normalize::expect(
                        &actual,
                        expected,
                        &scope.context,
                        arg.span,
                        &self.program.budget,
                    )?;
                }
                result
            }
            BasisExprKind::Not(a) => {
                let actual = self.basis_expr(a, scope)?;
                normalize::expect(
                    &actual,
                    &Ty::bit(),
                    &scope.context,
                    a.span,
                    &self.program.budget,
                )?;
                Ty::bit()
            }
            BasisExprKind::And(a, b) | BasisExprKind::Xor(a, b) => {
                let a_ty = self.basis_expr(a, scope)?;
                normalize::expect(
                    &a_ty,
                    &Ty::bit(),
                    &scope.context,
                    a.span,
                    &self.program.budget,
                )?;
                let b_ty = self.basis_expr(b, scope)?;
                normalize::expect(
                    &b_ty,
                    &Ty::bit(),
                    &scope.context,
                    b.span,
                    &self.program.budget,
                )?;
                Ty::bit()
            }
        };
        self.program.budget.ty(expr.span, &result)?;
        Ok(result)
    }
    pub(super) fn meaning(
        &mut self,
        permutation: bool,
        function: &Ident,
        basis: &Ty,
        scope: &Scope,
    ) -> Result<()> {
        let Target::Declaration(id) = self.resolve(function)? else {
            return Err(SourceError::new(
                "type",
                function.span,
                "meaning requires a basis function",
            ));
        };
        if self.program.decl(id).kind != FnKind::Basis {
            return Err(SourceError::new(
                "type",
                function.span,
                "meaning requires a basis function",
            ));
        }
        let (params, result, _) = self.specialize(id, &[], scope, function.span, false)?;
        if params.len() != 1 {
            return Err(SourceError::new(
                "type",
                function.span,
                "meaning requires exactly one basis argument",
            ));
        }
        normalize::expect(
            &params[0],
            basis,
            &scope.context,
            function.span,
            &self.program.budget,
        )?;
        let output = if permutation {
            self.program.budget.copy_ty(function.span, basis)?
        } else {
            Ty::pair(Ty::bit(), Ty::pair(Ty::bit(), Ty::bit()))
        };
        normalize::expect(
            &result,
            &output,
            &scope.context,
            function.span,
            &self.program.budget,
        )
    }
    /// Direct transform/qif targets retain the existing sealed unary rule.
    /// Static Op arguments still require ordinary providers or actual formals.
    pub(super) fn target_operation(
        &mut self,
        name: &Ident,
        basis: &Ty,
        scope: &Scope,
    ) -> Result<Operation> {
        if self
            .local(name)
            .and_then(|key| scope.operations.get(key))
            .is_some()
        {
            let op = self.named_operation(name, &[], scope, false)?;
            normalize::expect(
                &op.basis,
                basis,
                &scope.context,
                name.span,
                &self.program.budget,
            )?;
            return Ok(op);
        }
        if self.local(name).is_some() {
            return Err(SourceError::new(
                "type",
                name.span,
                "static operation requires a function name, not a local value",
            ));
        }
        if let Target::Primitive(id) = self.resolve(name)? {
            self.program
                .budget
                .charge(name.span, id.module.len() + id.name.len() + 2)?;
            let path = format!("{}::{}", id.module, id.name);
            let primitive = primitive::Primitive::lookup(&path).expect("typed primitive target");
            use primitive::Primitive::*;
            if !matches!(primitive, H | X | Z | T | S | Sdg | Tdg | Id | PhaseEighth) {
                return Err(SourceError::new(
                    "effect",
                    name.span,
                    "static sealed operation requires a unary unitary quantum primitive",
                ));
            }
            if !matches!(primitive, Id | PhaseEighth) {
                normalize::expect(
                    basis,
                    &Ty::bit(),
                    &scope.context,
                    name.span,
                    &self.program.budget,
                )?;
            }
            return Ok(Operation {
                basis: self.program.budget.copy_ty(name.span, basis)?,
                meaning: None,
                access: [true; 3],
            });
        }
        let op = self.named_operation(name, &[], scope, false)?;
        normalize::expect(
            &op.basis,
            basis,
            &scope.context,
            name.span,
            &self.program.budget,
        )?;
        Ok(op)
    }
    pub(super) fn qif(
        &mut self,
        control: &Expr,
        target: &Expr,
        zero: &Ident,
        one: &Ident,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        let control_ty = Ty::quantum(Ty::bit());
        self.expr(control, scope, Some(&control_ty))?;
        let target_ty = self.expr(target, scope, None)?;
        let basis = target_ty.quantum_basis().ok_or_else(|| {
            SourceError::new("type", target.span, "qif target requires one Q<A> owner")
        })?;
        for name in [zero, one] {
            let op = self.target_operation(name, basis, scope)?;
            access(&op, Access::Controlled, name.span)?;
        }
        self.obligation(span, ObligationKind::TransformedMeaning)?;
        Ok(Ty::pair(control_ty, target_ty))
    }
    pub(super) fn coherent(
        &mut self,
        binder: &Pattern,
        input: &Expr,
        basis: &BasisExpr,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        let input_ty = self.expr(input, scope, None)?;
        let input_basis = input_ty.quantum_basis().ok_or_else(|| {
            SourceError::new("type", input.span, "coherent lift requires one Q<A> owner")
        })?;
        let mut inner = scope.basis_scope(&self.program.budget, span)?;
        bind(
            binder,
            self.program.budget.copy_ty(span, input_basis)?,
            self.index(),
            &mut inner,
            &self.program.budget,
        )?;
        let output = self.basis_expr(basis, &mut inner)?;
        // Width equality is a source effect fact, never injectivity evidence.
        let equal = if normalize::equivalent(
            input_basis,
            &output,
            &scope.context,
            span,
            &self.program.budget,
        )? {
            true
        } else {
            match (
                self.basis_width(input_basis, span)?,
                self.basis_width(&output, span)?,
            ) {
                (Some(a), Some(b)) => {
                    scope.context.proves_le_budgeted(
                        &a,
                        &b,
                        span,
                        "coherent lift cannot shrink its domain",
                        &mut |span, cells| self.program.budget.sized_charge(span, cells),
                    )? && scope.context.proves_le_budgeted(
                        &b,
                        &a,
                        span,
                        "while checking coherent lift width",
                        &mut |span, cells| self.program.budget.sized_charge(span, cells),
                    )?
                }
                _ => false,
            }
        };
        if !equal {
            self.effects.add(Effect::Iso, span);
        }
        self.obligation(span, ObligationKind::Injectivity)?;
        Ok(Ty::quantum(output))
    }
    fn basis_width(&self, ty: &Ty, span: Span) -> Result<Option<Linear>> {
        self.tick(span)?;
        let mut charge = |span, cells| self.program.budget.sized_charge(span, cells);
        Ok(match &ty.kind {
            Kind::Unit => Some(Linear::constant_budgeted(0, span, &mut charge)?),
            Kind::Bit => Some(Linear::constant_budgeted(1, span, &mut charge)?),
            Kind::Bits(n) => Some(n.copy_budgeted(span, &mut charge)?),
            Kind::Tuple(fields) => {
                let mut total = Linear::constant_budgeted(0, span, &mut charge)?;
                for field in fields {
                    let Some(n) = self.basis_width(field, span)? else {
                        return Ok(None);
                    };
                    total = total.add_budgeted(&n, span, &mut charge)?;
                }
                Some(total)
            }
            Kind::Parameter(_) => None,
            Kind::Q(_) => {
                return Err(SourceError::new(
                    "type",
                    span,
                    "basis width cannot contain quantum owners",
                ));
            }
        })
    }
    pub(super) fn apply_contract(
        &mut self,
        implementation: &Ident,
        specification: &Ident,
        input: &Expr,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        // Preserve the actual function-contract route's input-first order.
        let ty = self.expr(input, scope, None)?;
        let basis = ty.quantum_basis().ok_or_else(|| {
            SourceError::new("type", input.span, "apply_contract requires one Q<A> owner")
        })?;
        let implementation_id = self.contract_function(implementation, basis, scope)?;
        let specification_target = self.resolve(specification)?;
        let specification_id = match specification_target {
            Target::Declaration(meaning) if self.program.decl(meaning).kind == FnKind::Meaning => {
                self.edge(meaning, specification.span)?;
                normalize::expect(
                    basis,
                    &self.program.interfaces[&meaning].result,
                    &scope.context,
                    specification.span,
                    &self.program.budget,
                )?;
                meaning
            }
            _ => self.contract_function(specification, basis, scope)?,
        };
        self.obligation(
            span,
            ObligationKind::FunctionEquality {
                implementation: implementation_id,
                specification: specification_id,
            },
        )?;
        Ok(ty)
    }
    fn contract_function(&mut self, name: &Ident, basis: &Ty, scope: &Scope) -> Result<DefId> {
        if self.local(name).is_some() {
            return Err(SourceError::new(
                "type",
                name.span,
                "apply_contract requires function names, not local values",
            ));
        }
        let Target::Declaration(id) = self.resolve(name)? else {
            return Err(SourceError::new(
                "type",
                name.span,
                "apply_contract requires ordinary functions with inferred Unitary body effects",
            ));
        };
        if matches!(self.program.decl(id).kind, FnKind::Basis | FnKind::Meaning) {
            return Err(SourceError::new(
                "type",
                name.span,
                "apply_contract requires ordinary functions with inferred Unitary body effects",
            ));
        }
        if !self.program.interfaces[&id].statics.is_empty() {
            return Err(SourceError::new(
                "arity",
                name.span,
                "contract functions must be closed",
            ));
        }
        let operation = self.named_operation(name, &[], scope, false)?;
        access(&operation, Access::Apply, name.span)?;
        normalize::expect(
            &operation.basis,
            basis,
            &scope.context,
            name.span,
            &self.program.budget,
        )?;
        Ok(id)
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn computed(
        &mut self,
        source: &Expr,
        function: &Ident,
        logical: Option<&Ident>,
        data: Option<&Ident>,
        ancilla: &Ident,
        body: &Block,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        let source_ty = self.expr(source, scope, None)?;
        let basis = source_ty.quantum_basis().ok_or_else(|| {
            SourceError::new(
                "type",
                source.span,
                "with_computed source requires one Q<A> owner",
            )
        })?;
        if self.local(function).is_some() {
            return Err(SourceError::new(
                "type",
                function.span,
                "with_computed requires a basis function name",
            ));
        }
        let Target::Declaration(predicate) = self.resolve(function)? else {
            return Err(SourceError::new(
                "type",
                function.span,
                "predicate must be a basis function",
            ));
        };
        if self.program.decl(predicate).kind != FnKind::Basis {
            return Err(SourceError::new(
                "type",
                function.span,
                "predicate must be a basis function",
            ));
        }
        let (params, result, _) = self.specialize(predicate, &[], scope, function.span, false)?;
        if params.len() != 1 {
            return Err(SourceError::new(
                "arity",
                function.span,
                format!(
                    "with_computed predicate requires exactly one explicit basis parameter; found {} parameters",
                    params.len()
                ),
            ));
        }
        let predicate_mismatch = |mut error: SourceError| {
            if error.code == "type" {
                error.message = format!(
                    "with_computed predicate type mismatch: expected `{} -> Bit`, found `{} -> {}`",
                    basis.display(Stage::Basis),
                    params[0].display(Stage::Basis),
                    result.display(Stage::Basis)
                );
            }
            error
        };
        normalize::expect(
            &params[0],
            basis,
            &scope.context,
            function.span,
            &self.program.budget,
        )
        .map_err(&predicate_mismatch)?;
        normalize::expect(
            &result,
            &Ty::bit(),
            &scope.context,
            function.span,
            &self.program.budget,
        )
        .map_err(&predicate_mismatch)?;
        let mut inner = scope.copy(&self.program.budget, span)?;
        let ancilla_ty = Ty::quantum(Ty::bit());
        let expected = if let (Some(logical), Some(data)) = (logical, data) {
            if data.text == ancilla.text {
                return Err(SourceError::new(
                    "ownership",
                    ancilla.span,
                    "certified data and auxiliary binders must be distinct",
                ));
            }
            let operation = self.target_operation(logical, basis, scope)?;
            access(&operation, Access::Apply, logical.span)?;
            let identity = match self.index().table.usage(self.index().usage(logical)).target {
                ResolvedUse::Global(target) => OperationIdentity::Global(target),
                ResolvedUse::Local(id) => OperationIdentity::Formal(
                    self.program
                        .budget
                        .key(logical.span, self.index().table.key(id))?,
                ),
                ResolvedUse::Unresolved => {
                    return Err(SourceError::new(
                        "name",
                        logical.span,
                        "unresolved logical operation",
                    ));
                }
            };
            self.obligation(span, ObligationKind::CertifiedClean { logical: identity })?;
            inner.values.clear();
            bind_name(
                data,
                self.program.budget.copy_ty(span, &source_ty)?,
                self.index(),
                &mut inner,
                &self.program.budget,
                data.span,
            )?;
            Ty::pair(self.program.budget.copy_ty(span, &source_ty)?, ancilla_ty)
        } else {
            inner.values.retain(|_, value| !value.ty.linear());
            self.obligation(span, ObligationKind::ProtectedClean)?;
            ancilla_ty
        };
        bind_name(
            ancilla,
            Ty::quantum(Ty::bit()),
            self.index(),
            &mut inner,
            &self.program.budget,
            ancilla.span,
        )?;
        let surrounding = std::mem::replace(&mut self.effects, BodyEffects::new(body.span));
        let checked = self.block(body, &mut inner, None);
        let region = std::mem::replace(&mut self.effects, surrounding);
        let found = match checked {
            Ok(found) => found,
            Err(error) => {
                return Err(self.computed_capture_error(
                    error,
                    scope,
                    logical.is_some() && data.is_some(),
                )?);
            }
        };
        if let Some(key) = self.live_owner(&inner, body.span)? {
            return Err(SourceError::new(
                "ownership",
                self.index().table.binder(key.id).span,
                format!(
                    "quantum ownership `{}` was not returned or explicitly consumed",
                    key.name
                ),
            ));
        }
        normalize::expect(
            &found,
            &expected,
            &inner.context,
            body.result.span,
            &self.program.budget,
        )?;
        self.program
            .budget
            .charge(body.span, region.storage_cells() + 1)?;
        self.effects.merge(&region);
        self.program
            .unitary_regions
            .push((self.definition, body.span, region));
        // Exact returned-register identity and clean release remain obligations
        // for the actual circuit/evidence consumer, not type/name evidence.
        Ok(source_ty)
    }

    /// Explain a rejected use only; successful body checking performs no extra
    /// traversal, cloning, metadata allocation or work-budget charge.
    fn computed_capture_error(
        &self,
        mut error: SourceError,
        scope: &Scope,
        all: bool,
    ) -> Result<SourceError> {
        if error.code != "ownership" {
            return Ok(error);
        }
        let Some(id) = self
            .index()
            .table
            .local_use_at_span(error.span, || self.tick(error.span))?
        else {
            return Ok(error);
        };
        let key = self.index().table.key(id);
        let Some(binding) = scope.values.get(key) else {
            return Ok(error);
        };
        // The surrounding scope is already after source evaluation. A spent
        // source/outer owner is absent; shadowed body locals have a distinct ID.
        self.program.budget.ty(error.span, &binding.ty)?;
        let quantum = binding.ty.linear();
        if all || quantum {
            let repair = if quantum {
                "include it in the source data with `join` and access it through the data binder of three-argument `with_computed`, or restructure the body"
            } else {
                "use a closed classical expression or restructure the body"
            };
            error.message = format!(
                "with_computed body cannot capture outer binding `{}`; {repair}",
                key.name
            );
        }
        Ok(error)
    }
}
