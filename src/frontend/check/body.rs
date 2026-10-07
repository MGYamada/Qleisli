//! Original body type, owner, capability and dependency judgments.
use super::super::ast::*;
use super::super::ordinary::{self, Boolean, OperandFailure};
use super::super::pattern::{self, BindingContext};
use super::super::resolve::Target;
use super::super::resolve::locals::{BindingKind, ResolvedUse};
use super::super::types::Stage;
use super::*;
use crate::ir::Effect;
use std::borrow::Cow;

// These explanations are attached only after an existing rejection. They do
// not select a physical operation, inspect arguments or change acceptance.
fn disposal_error(span: Span, message: impl std::fmt::Display) -> SourceError {
    SourceError::new(
        "ownership",
        span,
        format!(
            "{message}; implicit quantum destruction is forbidden. Measurement, discard, reset and checked clean discharge are distinct; reset returns a fresh quantum owner."
        ),
    )
}

fn unresolved_function_message(name: &str) -> String {
    let mut message = format!("unresolved function {name}");
    let explanation = match name {
        "drop" | "forget" => {
            "; there is no built-in Rust drop or forget operation. Ordinary Bit/Unit may be unused or matched by _. If a value contains live Q<T>, it must be returned or explicitly consumed; scope exit is not destruction. Measurement, discard, reset and checked clean discharge have distinct meanings; reset returns a fresh owner."
        }
        "clone" | "copy" => {
            "; there is no built-in Rust Clone/Copy operation. Ordinary data such as Bit/Unit is reusable; if a value contains live Q<T>, reusing a description or a basis label does not duplicate that owner."
        }
        "default" => {
            "; there is no built-in Rust Default operation. Ordinary Bit/Unit can be constructed explicitly; quantum preparation is explicit and cannot be inferred from Default. This includes Q<Unit> and products containing quantum owners; zero physical width does not grant Default."
        }
        _ => return message,
    };
    message.push_str(explanation);
    message
}

mod operations;
mod special;

struct PatternBinding<'a, 'ast> {
    scope: &'a mut Scope,
    index: &'a Index<'ast>,
    budget: &'a Budget,
}
impl BindingContext<Pattern> for PatternBinding<'_, '_> {
    type Value = Ty;
    type Size = Linear;
    type Error = SourceError;
    fn linear(&self, value: &Ty) -> bool {
        value.linear()
    }
    fn pattern_type<'v>(&self, value: &'v Ty) -> Cow<'v, Ty> {
        Cow::Borrowed(value)
    }
    fn consume_fields(&mut self, value: Ty) -> Vec<Ty> {
        match value.kind {
            Kind::Tuple(fields) => fields,
            _ => unreachable!("checked product pattern"),
        }
    }
    fn bind_name(&mut self, name: &Ident, span: Span, value: Ty) -> Result<()> {
        bind_name(name, value, self.index, self.scope, self.budget, span)
    }
    fn wildcard_error(&self, span: Span) -> SourceError {
        disposal_error(span, "wildcard would discard quantum ownership")
    }
    fn duplicate_error(&self, span: Span) -> SourceError {
        SourceError::new("binding", span, "duplicate name in binding pattern")
    }
    fn shape_error(&self, span: Span, arity: usize, value: &Ty, actual: &Ty) -> SourceError {
        let help = if value
            .quantum_basis()
            .and_then(Ty::tuple_fields)
            .is_some_and(|fields| fields.len() == 2)
        {
            "; help: a quantum register is one owner; call `split` to obtain its immediate product fields, then split any nested register separately"
        } else {
            ""
        };
        SourceError::new(
            "type",
            span,
            if arity == 0 {
                format!(
                    "empty pattern requires ordinary Unit, found `{}`",
                    actual.display(Stage::Runtime)
                )
            } else {
                format!(
                    "tuple pattern requires a tuple value with the same immediate arity: expected a tuple of {arity} immediate fields, found `{}`{help}",
                    actual.display(Stage::Runtime)
                )
            },
        )
    }
}
pub(super) fn bind(
    pattern: &Pattern,
    value: Ty,
    index: &Index<'_>,
    scope: &mut Scope,
    budget: &Budget,
) -> Result<()> {
    budget.ty(pattern.span, &value)?;
    pattern_work(pattern, budget)?;
    pattern::bind(
        pattern,
        value,
        &mut BTreeSet::new(),
        &mut PatternBinding {
            scope,
            index,
            budget,
        },
    )
}
pub(super) fn pattern_work(pattern: &Pattern, budget: &Budget) -> Result<()> {
    budget.charge(pattern.span, 1)?;
    let mut pending = vec![(pattern, 1usize)];
    while let Some((node, depth)) = pending.pop() {
        budget.charge(node.span, 2)?;
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                node.span,
                "binding pattern exceeds depth 64",
            ));
        }
        if let PatternKind::Tuple(fields) = &node.kind {
            if fields.len() > 64 {
                return Err(SourceError::new(
                    "limit",
                    node.span,
                    "binding tuple exceeds 64 fields",
                ));
            }
            budget.charge(node.span, fields.len())?;
            pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
        } else if let PatternKind::Name(name) = &node.kind {
            budget.charge(name.span, name.text.len() + 1)?;
        }
    }
    Ok(())
}
fn bind_name(
    name: &Ident,
    value: Ty,
    index: &Index<'_>,
    scope: &mut Scope,
    budget: &Budget,
    span: Span,
) -> Result<()> {
    let info = index.table.binder(index.binder(name));
    if let Some(key) = info.shadowed.map(|id| index.table.key(id)) {
        if matches!(
            info.kind,
            super::super::resolve::locals::BindingKind::Runtime
        ) && (scope.naturals.contains_key(key)
            || scope.bases.contains_key(key)
            || scope.operations.contains_key(key))
        {
            return Err(SourceError::new(
                "shadow",
                span,
                format!("binding {} shadows a static parameter/index", name.text),
            ));
        }
        if scope
            .values
            .get(key)
            .is_some_and(|binding| binding.ty.linear())
        {
            return Err(disposal_error(
                span,
                format!("binding {} would drop a live quantum owner", name.text),
            ));
        }
    }
    let size = budget.ty(span, &value)?;
    if let Some(limit) = budget.limits.retained_scope_cells {
        let mut cells = 0usize;
        for (key, retained) in &scope.values {
            budget.charge(span, 1)?;
            if info.shadowed.map(|id| index.table.key(id)) != Some(key) {
                cells = cells
                    .checked_add(budget.ty(span, &retained.ty)?)
                    .ok_or_else(|| SourceError::new("limit", span, "scope type count overflow"))?;
            }
        }
        if cells.checked_add(size).is_none_or(|n| n > limit) {
            return Err(SourceError::new(
                "limit",
                span,
                "scope exceeds 16384 retained type cells",
            ));
        }
    }
    budget.charge(span, 2)?;
    let identity = scope.next_binding.get();
    scope.next_binding.set(
        identity
            .checked_add(1)
            .ok_or_else(|| SourceError::new("limit", span, "binding identity exhausted"))?,
    );
    if let Some(previous) = info.shadowed {
        scope.values.remove(index.table.key(previous));
    }
    scope.values.insert(
        budget.key(span, &info.key)?,
        Binding {
            identity,
            ty: value,
        },
    );
    Ok(())
}

pub(super) fn check(p: &mut Program<'_>, id: DefId) -> Result<(BodyEffects, Vec<(DefId, Span)>)> {
    let declaration = p.decl(id);
    let interface = &p.interfaces[&id];
    let mut scope = declarations::scope(interface, &p.helpers, &p.budget, declaration.span)?;
    let index = &p.indices[&id];
    for (parameter, ty) in declaration.params.iter().zip(&interface.params) {
        bind(
            &parameter.pattern,
            p.budget.copy_ty(parameter.span, ty)?,
            index,
            &mut scope,
            &p.budget,
        )?;
    }
    let expected = p
        .budget
        .copy_ty(declaration.return_type.span, &interface.result)?;
    let mut checker = Checker {
        program: p,
        definition: id,
        effects: BodyEffects::new(declaration.span),
        edges: Vec::new(),
        depth: 0,
    };
    for formal in &checker.program.interfaces[&id].statics {
        checker.program.budget.charge(declaration.span, 1)?;
        if let StaticKind::Operation {
            meaning: Some(meaning),
            ..
        } = formal.kind
        {
            checker.edges.push((meaning, declaration.span));
        }
    }
    match &declaration.body {
        FnBody::Natural(_) => {
            unreachable!("static helpers were checked before runtime declarations")
        }
        FnBody::Basis(body) => {
            let found = checker.basis_expr(body, &mut scope)?;
            normalize::expect(
                &found,
                &expected,
                &scope.context,
                body.span,
                &checker.program.budget,
            )?;
        }
        FnBody::Meaning {
            permutation,
            function,
        } => checker.meaning(*permutation, function, &expected, &scope)?,
        FnBody::Quantum(body) => {
            checker.block(body, &mut scope, Some(&expected))?;
            if let Some(key) = checker.live_owner(&scope, body.span)? {
                return Err(disposal_error(
                    checker.index().table.binder(key.id).span,
                    format!(
                        "quantum ownership `{}` was not returned or explicitly consumed",
                        key.name
                    ),
                ));
            }
        }
    }
    Ok((checker.effects, checker.edges))
}

struct Checker<'p, 'ast> {
    program: &'p mut Program<'ast>,
    definition: DefId,
    effects: BodyEffects,
    edges: Vec<(DefId, Span)>,
    depth: usize,
}
impl Checker<'_, '_> {
    fn index(&self) -> &Index<'_> {
        &self.program.indices[&self.definition]
    }
    fn tick(&self, span: Span) -> Result<()> {
        self.program.budget.charge(span, 1)
    }
    fn live_owner<'s>(&self, scope: &'s Scope, span: Span) -> Result<Option<&'s BinderKey>> {
        let mut first: Option<&BinderKey> = None;
        for (key, binding) in &scope.values {
            self.program.budget.charge(span, 2)?;
            let mut pending = vec![&binding.ty];
            let mut linear = false;
            while let Some(ty) = pending.pop() {
                self.tick(span)?;
                match &ty.kind {
                    Kind::Q(_) => {
                        linear = true;
                        break;
                    }
                    Kind::Tuple(fields) => {
                        self.program.budget.charge(span, fields.len())?;
                        pending.extend(fields);
                    }
                    _ => {}
                }
            }
            if linear && first.is_none_or(|previous| key.id < previous.id) {
                first = Some(key);
            }
        }
        Ok(first)
    }
    fn local(&self, name: &Ident) -> Option<&BinderKey> {
        match self.index().table.usage(self.index().usage(name)).target {
            ResolvedUse::Local(id) => Some(self.index().table.key(id)),
            _ => None,
        }
    }
    fn resolve(&self, name: &Ident) -> Result<Target> {
        match self.index().table.usage(self.index().usage(name)).target {
            ResolvedUse::Global(Target::Declaration(id))
                if self.program.decl(id).kind == FnKind::Static =>
            {
                Err(SourceError::new(
                    "static",
                    name.span,
                    "a Nat helper is available only in static natural expressions",
                ))
            }
            ResolvedUse::Global(target) => Ok(target),
            ResolvedUse::Local(_) => Err(SourceError::new(
                "type",
                name.span,
                "a local value is not callable",
            )),
            ResolvedUse::Unresolved => Err(SourceError::new(
                "name",
                name.span,
                unresolved_function_message(&name.text),
            )),
        }
    }
    fn edge(&mut self, id: DefId, span: Span) -> Result<()> {
        self.tick(span)?;
        self.edges.push((id, span));
        Ok(())
    }
    fn obligation(&mut self, span: Span, kind: ObligationKind) -> Result<()> {
        self.tick(span)?;
        self.program.obligations.push(Obligation {
            definition: self.definition,
            span,
            kind,
        });
        Ok(())
    }
    fn block(&mut self, block: &Block, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        self.tick(block.span)?;
        self.program.budget.charge(block.span, scope.values.len())?;
        let initial = self.program.budget.values(block.span, &scope.values)?;
        let outer: BTreeSet<_> = initial.values().map(|b| b.identity).collect();
        let mut local_naturals = Vec::new();
        for statement in &block.statements {
            self.tick(statement.span)?;
            match &statement.kind {
                StmtKind::StaticLet { name, value } => {
                    let info = self.index().table.binder(self.index().binder(name));
                    if info.shadowed.is_some() {
                        return Err(SourceError::new(
                            "shadow",
                            name.span,
                            "static binding cannot shadow a visible lexical binding",
                        ));
                    }
                    let value =
                        normalize::natural(value, self.index(), scope, None, &self.program.budget)?;
                    let key = self.program.budget.key(name.span, &info.key)?;
                    self.program.budget.charge(name.span, key.name.len() + 2)?;
                    scope.naturals.insert(key.clone(), value);
                    local_naturals.push(key);
                }
                StmtKind::Let { pattern, value } => {
                    let value = self.expr(value, scope, None)?;
                    bind(pattern, value, self.index(), scope, &self.program.budget)?;
                }
                StmtKind::Expr(expr) => {
                    if self.expr(expr, scope, None)?.linear() {
                        return Err(disposal_error(
                            expr.span,
                            "expression statement would discard quantum ownership",
                        ));
                    }
                }
            }
        }
        let result = self.expr(&block.result, scope, expected)?;
        for key in local_naturals {
            scope.naturals.remove(&key);
        }
        for (key, binding) in &scope.values {
            if !outer.contains(&binding.identity) && binding.ty.linear() {
                return Err(disposal_error(
                    self.index().table.binder(key.id).span,
                    format!(
                        "local quantum ownership `{}` escapes neither through the result nor an explicit discard",
                        key.name
                    ),
                ));
            }
        }
        self.program.budget.charge(block.span, initial.len())?;
        scope.values = initial
            .into_iter()
            .filter(|(_, b)| !scope.moved.contains(&b.identity))
            .collect();
        Ok(result)
    }
    fn expr(&mut self, expr: &Expr, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        if self.depth >= 64 {
            return Err(SourceError::new(
                "limit",
                expr.span,
                "source expression exceeds depth 64",
            ));
        }
        self.depth += 1;
        let result = self.expr_inner(expr, scope, expected);
        self.depth -= 1;
        result
    }
    fn expr_inner(&mut self, expr: &Expr, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        let span = expr.span;
        self.tick(span)?;
        let result = match &expr.kind {
            ExprKind::Unit => Ty::unit(),
            ExprKind::Bit(bit) => self.boolean(Boolean::Constant(*bit), &[], scope, span)?,
            ExprKind::Not(a) => self.boolean(Boolean::Not, &[a.as_ref()], scope, span)?,
            ExprKind::And(a, b) => {
                self.boolean(Boolean::And, &[a.as_ref(), b.as_ref()], scope, span)?
            }
            ExprKind::Xor(a, b) => {
                self.boolean(Boolean::Xor, &[a.as_ref(), b.as_ref()], scope, span)?
            }
            ExprKind::Name(name) => {
                let key = self.local(name).ok_or_else(|| {
                    SourceError::new("name", span, format!("unknown value `{}`", name.text))
                })?;
                if matches!(
                    self.index().table.binder(key.id).kind,
                    BindingKind::StaticNatural
                        | BindingKind::StaticBasis
                        | BindingKind::StaticOperation
                        | BindingKind::FoldIndex
                ) {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        format!("static name `{}` is not a runtime value", name.text),
                    ));
                }
                let binding = scope.values.get(key).ok_or_else(|| {
                    SourceError::new(
                        "ownership",
                        span,
                        format!(
                            "quantum ownership `{}` has already been consumed",
                            name.text
                        ),
                    )
                })?;
                let ty = self.program.budget.copy_ty(span, &binding.ty)?;
                let identity = binding.identity;
                if ty.linear() {
                    scope.values.remove(key);
                    scope.moved.insert(identity);
                }
                ty
            }
            ExprKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        span,
                        "source tuple exceeds 64 fields",
                    ));
                }
                self.program.budget.charge(span, fields.len() + 1)?;
                let ts = expected
                    .and_then(Ty::tuple_fields)
                    .filter(|ts| ts.len() == fields.len());
                let mut result = Vec::new();
                let mut cells = 1usize;
                for (i, field) in fields.iter().enumerate() {
                    let ty = self.expr(field, scope, ts.map(|ts| &ts[i]))?;
                    cells = cells
                        .checked_add(self.program.budget.ty(field.span, &ty)?)
                        .ok_or_else(|| {
                            SourceError::new("limit", span, "tuple cell count overflow")
                        })?;
                    if cells > 4096 {
                        return Err(SourceError::new(
                            "limit",
                            span,
                            "inferred tuple exceeds 4096 cells",
                        ));
                    }
                    result.push(ty);
                }
                Ty::tuple(result)
            }
            ExprKind::Call {
                callee,
                static_args,
                args,
            } => self.call(callee, static_args, args, scope, span)?,
            ExprKind::ApplyStatic { operation, input } => {
                let target = self.expr(input, scope, None)?;
                self.transformed_operation(
                    operation,
                    &target,
                    scope,
                    Access::Apply,
                    input.span,
                    span,
                )?;
                self.obligation(span, ObligationKind::TransformedMeaning)?;
                target
            }
            ExprKind::Adjoint { operation, input } => {
                let target = self.expr(input, scope, None)?;
                self.transformed_operation(
                    operation,
                    &target,
                    scope,
                    Access::Adjoint,
                    input.span,
                    span,
                )?;
                self.obligation(span, ObligationKind::TransformedMeaning)?;
                target
            }
            ExprKind::Controlled { operation, args } => {
                if args.len() != 2 {
                    return Err(SourceError::new(
                        "arity",
                        span,
                        "controlled application takes control and target",
                    ));
                }
                let control = Ty::quantum(Ty::bit());
                self.expr(&args[0], scope, Some(&control))?;
                let target = self.expr(&args[1], scope, None)?;
                self.transformed_operation(
                    operation,
                    &target,
                    scope,
                    Access::Controlled,
                    args[1].span,
                    span,
                )?;
                self.obligation(span, ObligationKind::TransformedMeaning)?;
                Ty::pair(control, target)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, scope, Some(&Ty::bit()))?;
                self.branches(None, then_branch, else_branch, scope, expected, span)?
            }
            ExprKind::StaticIf {
                predicate,
                then_branch,
                else_branch,
            } => self.branches(
                Some(predicate),
                then_branch,
                else_branch,
                scope,
                expected,
                span,
            )?,
            ExprKind::StaticFold {
                quantum,
                index,
                start,
                end,
                carry,
                initial,
                body,
            } => self.fold(
                *quantum, index, start, end, carry, initial, body, scope, expected, span,
            )?,
            ExprKind::QuantumIf {
                control,
                target,
                zero,
                one,
            } => self.qif(control, target, zero, one, scope, span)?,
            ExprKind::RepeatStatic {
                count: _,
                function,
                input,
            } => {
                let input = self.expr(input, scope, None)?;
                let basis = input.quantum_basis().ok_or_else(|| {
                    SourceError::new("type", span, "repetition requires one Q<A> owner")
                })?;
                let op = self.target_operation(function, basis, scope)?;
                access(&op, Access::Apply, span)?;
                self.obligation(span, ObligationKind::TransformedMeaning)?;
                input
            }
            ExprKind::ApplyContract {
                implementation,
                specification,
                input,
            } => self.apply_contract(implementation, specification, input, scope, span)?,
            ExprKind::CoherentLift {
                binder,
                input,
                basis,
            } => self.coherent(binder, input, basis, scope, span)?,
            ExprKind::WithComputed {
                source,
                function,
                binder,
                body,
            } => self.computed(source, function, None, None, binder, body, scope, span)?,
            ExprKind::CertifiedComputed {
                source,
                function,
                logical,
                data_binder,
                ancilla_binder,
                body,
            } => self.computed(
                source,
                function,
                Some(logical),
                Some(data_binder),
                ancilla_binder,
                body,
                scope,
                span,
            )?,
        };
        self.program.budget.ty(span, &result)?;
        if let Some(expected) = expected {
            normalize::expect(
                &result,
                expected,
                &scope.context,
                span,
                &self.program.budget,
            )?;
        }
        Ok(result)
    }
    fn boolean(
        &mut self,
        op: Boolean,
        args: &[&Expr],
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        self.program.budget.charge(span, op.arity() + 1)?;
        ordinary::evaluate(
            op,
            args.iter().copied(),
            &mut (&mut *self, &mut *scope),
            |(checker, scope), expr| {
                let ty = checker.expr(expr, scope, None)?;
                checker.program.budget.ty(expr.span, &ty)?;
                Ok(ty)
            },
            Clone::clone,
            |_, failure| match failure {
                OperandFailure::Arity { expected, actual } => SourceError::new(
                    "arity",
                    span,
                    format!("Boolean operation requires {expected} operands, found {actual}"),
                ),
                OperandFailure::Type(ty) => SourceError::new(
                    "type",
                    span,
                    format!(
                        "{} requires ordinary Bit operands: expected `Bit`, found `{}`",
                        op.operator(),
                        ty.display(Stage::Runtime)
                    ),
                ),
            },
        )?;
        Ok(op.result_type())
    }
    fn branches(
        &mut self,
        predicate: Option<&Predicate>,
        yes: &Block,
        no: &Block,
        scope: &mut Scope,
        expected: Option<&Ty>,
        span: Span,
    ) -> Result<Ty> {
        let mut a = scope.copy(&self.program.budget, span)?;
        let mut b = scope.copy(&self.program.budget, span)?;
        if let Some(predicate) = predicate {
            a.context =
                normalize::predicate(predicate, self.index(), scope, true, &self.program.budget)?;
            b.context =
                normalize::predicate(predicate, self.index(), scope, false, &self.program.budget)?;
        }
        let a_ty = self.block(yes, &mut a, expected)?;
        let b_ty = self.block(no, &mut b, expected)?;
        if !self.same_frame(&a.values, &b.values, span)? {
            return Err(SourceError::new(
                "ownership",
                span,
                "branches must consume the same owners and preserve outer binding types",
            ));
        }
        self.program.budget.charge(span, a.moved.len())?;
        scope.values = a.values;
        scope.moved.extend(a.moved);
        if let Some(t) = expected {
            self.program.budget.copy_ty(span, t)
        } else {
            normalize::expect(&b_ty, &a_ty, &scope.context, span, &self.program.budget)?;
            Ok(a_ty)
        }
    }
    fn same_frame(
        &self,
        a: &BTreeMap<BinderKey, Binding>,
        b: &BTreeMap<BinderKey, Binding>,
        span: Span,
    ) -> Result<bool> {
        self.tick(span)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for ((a_key, a_value), (b_key, b_value)) in a.iter().zip(b) {
            self.program
                .budget
                .charge(span, a_key.name.len() + b_key.name.len() + 1)?;
            if a_key != b_key || a_value.identity != b_value.identity {
                return Ok(false);
            }
            let same = a_value.ty.equivalent_by_budgeted(
                &b_value.ty,
                &mut |a, b| {
                    self.program
                        .budget
                        .charge(span, a.terms.len() + b.terms.len() + 1)?;
                    for key in a.terms.keys().chain(b.terms.keys()) {
                        self.program.budget.charge(span, key.name.len())?;
                    }
                    Ok::<_, SourceError>(a == b)
                },
                &mut |cells| self.program.budget.charge(span, cells),
            )?;
            if !same {
                return Ok(false);
            }
        }
        Ok(true)
    }
    #[allow(clippy::too_many_arguments)]
    fn fold(
        &mut self,
        quantum: bool,
        index: &Ident,
        start: &Natural,
        end: &Natural,
        carry: &Pattern,
        initial: &Expr,
        body: &Block,
        scope: &mut Scope,
        expected: Option<&Ty>,
        span: Span,
    ) -> Result<Ty> {
        let info = self.index().table.binder(self.index().binder(index));
        if info.shadowed.is_some() {
            return Err(SourceError::new(
                "name",
                index.span,
                "static fold index shadows an existing name",
            ));
        }
        let key = self.program.budget.key(index.span, &info.key)?;
        let start = normalize::natural(start, self.index(), scope, None, &self.program.budget)?;
        let end = normalize::natural(end, self.index(), scope, None, &self.program.budget)?;
        if !scope.context.proves_le_budgeted(
            &start,
            &end,
            span,
            "static fold requires start <= end",
            &mut |span, cells| self.program.budget.preparation_charge(span, cells),
        )? {
            return Err(SourceError::new(
                "size",
                span,
                "static fold requires start <= end",
            ));
        }
        let carry_ty = self.expr(initial, scope, expected)?;
        if quantum != carry_ty.linear() {
            return Err(SourceError::new(
                "type",
                span,
                if quantum {
                    "qfor carry must contain a quantum owner; use for static for ordinary values"
                } else {
                    "for static cannot thread quantum owners; use qfor static with explicit carry and yield"
                },
            ));
        }
        let mut inner = scope.copy(&self.program.budget, span)?;
        inner.values.retain(|_, binding| !binding.ty.linear());
        let i = Linear::variable_budgeted(&key, span, &mut |span, cells| {
            self.program.budget.preparation_charge(span, cells)
        })?;
        let mut charge = |span, cells| self.program.budget.preparation_charge(span, cells);
        let one = Linear::constant_budgeted(1, span, &mut charge)?;
        let bounds = [
            start.sub_budgeted(&i, span, &mut charge)?,
            i.add_budgeted(&one, span, &mut charge)?
                .sub_budgeted(&end, span, &mut charge)?,
            i.scale_budgeted(-1, span, &mut charge)?,
        ];
        inner.context = inner
            .context
            .push_budgeted(&bounds, span, &mut |span, cells| {
                self.program.budget.preparation_charge(span, cells)
            })?;
        self.program.budget.charge(index.span, 1)?;
        inner.naturals.insert(key, i);
        bind(
            carry,
            self.program.budget.copy_ty(span, &carry_ty)?,
            self.index(),
            &mut inner,
            &self.program.budget,
        )?;
        self.block(body, &mut inner, Some(&carry_ty))?;
        if inner.values.values().any(|b| b.ty.linear()) {
            return Err(SourceError::new(
                "ownership",
                span,
                "fold body leaves a carry owner unconsumed",
            ));
        }
        Ok(carry_ty)
    }
}
fn access(op: &Operation, kind: Access, span: Span) -> Result<()> {
    access_mask(&op.access, kind, span)
}
fn access_mask(mask: &[bool; 3], kind: Access, span: Span) -> Result<()> {
    if mask[super::super::formals::access_index(kind)] {
        Ok(())
    } else {
        Err(SourceError::new(
            "access",
            span,
            format!(
                "missing {} operation access",
                super::super::formals::access_name(kind)
            ),
        ))
    }
}
