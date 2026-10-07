//! Checked static descriptions and actual original callee specialization.
use super::*;
impl Checker<'_, '_> {
    /// Direct runtime transforms preserve the whole owner group. Opaque Op
    /// arguments and constructors continue to use their single-owner basis.
    pub(super) fn transformed_operation(
        &mut self,
        op: &StaticOp,
        target: &Ty,
        scope: &Scope,
        requested: Access,
        target_span: Span,
        span: Span,
    ) -> Result<()> {
        if self.depth >= 64 {
            return Err(SourceError::new(
                "limit",
                op.span,
                "static operation exceeds depth 64",
            ));
        }
        self.depth += 1;
        let checked =
            self.transformed_operation_inner(op, target, scope, requested, target_span, span);
        self.depth -= 1;
        checked
    }
    fn transformed_operation_inner(
        &mut self,
        op: &StaticOp,
        target: &Ty,
        scope: &Scope,
        requested: Access,
        target_span: Span,
        span: Span,
    ) -> Result<()> {
        self.tick(op.span)?;
        match &op.kind {
            StaticOpKind::Repeat(count, child) if self.runtime_group_leaf(child)? => {
                let (Count::Natural(count) | Count::Power(count)) = count;
                normalize::natural(count, self.index(), scope, None, &self.program.budget)?;
                return self.transformed_operation(
                    child,
                    target,
                    scope,
                    requested,
                    target_span,
                    span,
                );
            }
            _ => {}
        }
        let named = match &op.kind {
            StaticOpKind::Name(name) => Some((name, &[][..])),
            StaticOpKind::Specialize { name, arguments } => Some((name, arguments.as_slice())),
            _ => None,
        };
        if let Some((name, arguments)) = named {
            if let ResolvedUse::Global(Target::Declaration(id)) =
                self.index().table.usage(self.index().usage(name)).target
            {
                if matches!(
                    self.program.decl(id).kind,
                    FnKind::Classical | FnKind::Meaning
                ) {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "direct transform requires an ordinary runtime function",
                    ));
                }
                let (mut inputs, result, mask) =
                    self.specialize(id, arguments, scope, name.span, true)?;
                if inputs.is_empty() {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "direct transform requires a nonempty quantum input group",
                    ));
                }
                self.tick(name.span)?;
                let group = if inputs.len() == 1 {
                    inputs.pop().expect("one complete runtime input")
                } else {
                    Ty::tuple(inputs)
                };
                self.program.budget.ty(name.span, &group)?;
                if !runtime_quantum_group(&group, name.span, &self.program.budget)? {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "direct transform requires a complete quantum input group",
                    ));
                }
                normalize::expect(
                    &group,
                    &result,
                    &scope.context,
                    name.span,
                    &self.program.budget,
                )?;
                access_mask(&mask, requested, span)?;
                normalize::expect(
                    target,
                    &group,
                    &scope.context,
                    target_span,
                    &self.program.budget,
                )?;
                self.tick(name.span)?;
                self.effects.require_unitary(id, name.span);
                self.obligation(
                    name.span,
                    ObligationKind::RuntimeGroupProvider { provider: id },
                )?;
                return Ok(());
            }
        }
        let basis = target.quantum_basis().ok_or_else(|| {
            SourceError::new(
                "type",
                target_span,
                if requested == Access::Adjoint {
                    "adjoint requires one Q<A> owner"
                } else {
                    "controlled target requires one Q<A> owner"
                },
            )
        })?;
        let operation = if let StaticOpKind::Name(name) = &op.kind {
            self.target_operation(name, basis, scope)?
        } else {
            self.operation_inner(op, scope)?
        };
        access(&operation, requested, span)?;
        normalize::expect(
            &operation.basis,
            basis,
            &scope.context,
            span,
            &self.program.budget,
        )
    }
    fn runtime_group_leaf(&self, op: &StaticOp) -> Result<bool> {
        let mut leaf = op;
        let mut depth = self.depth;
        loop {
            self.tick(leaf.span)?;
            if depth >= 64 {
                return Err(SourceError::new(
                    "limit",
                    leaf.span,
                    "static operation exceeds depth 64",
                ));
            }
            match &leaf.kind {
                StaticOpKind::Repeat(_, child) => {
                    depth += 1;
                    leaf = child;
                }
                StaticOpKind::Name(name) | StaticOpKind::Specialize { name, .. } => {
                    return Ok(matches!(
                        self.index().table.usage(self.index().usage(name)).target,
                        ResolvedUse::Global(Target::Declaration(_))
                    ));
                }
                _ => return Ok(false),
            }
        }
    }
    fn static_natural(&self, arg: &StaticOp, scope: &Scope) -> Result<Linear> {
        match &arg.kind {
            StaticOpKind::Natural(n) => {
                normalize::natural(n, self.index(), scope, None, &self.program.budget)
            }
            StaticOpKind::Name(name) => {
                let key = self.local(name).ok_or_else(|| {
                    SourceError::new("static", arg.span, "expected natural argument")
                })?;
                let value = scope.naturals.get(key).ok_or_else(|| {
                    SourceError::new("static", arg.span, "expected natural argument")
                })?;
                Ok(value.copy_budgeted(arg.span, &mut |span, cells| {
                    self.program.budget.preparation_charge(span, cells)
                })?)
            }
            _ => Err(SourceError::new(
                "static",
                arg.span,
                "expected natural argument",
            )),
        }
    }
    pub(super) fn specialize(
        &mut self,
        id: DefId,
        args: &[StaticOp],
        scope: &Scope,
        span: Span,
        runtime_recursion: bool,
    ) -> Result<(Vec<Ty>, Ty, [bool; 3])> {
        if self.program.decl(id).kind == FnKind::Static {
            return Err(SourceError::new(
                "static",
                span,
                "a Nat helper cannot be a runtime callee or operation provider",
            ));
        }
        let interface = &self.program.interfaces[&id];
        if args.len() != interface.statics.len() {
            let ordered = interface
                .statics
                .iter()
                .map(|formal| {
                    let category = match formal.kind {
                        StaticKind::Natural => "Nat",
                        StaticKind::Basis => "Basis",
                        StaticKind::Operation { .. } => "Op",
                    };
                    format!("{}: {category}", formal.key.name)
                })
                .collect::<Vec<_>>()
                .join(", ");
            return Err(SourceError::new(
                "static-arity",
                span,
                format!(
                    "{} requires explicit static parameters [{ordered}]; received {} arguments",
                    self.program.resolution.path(id),
                    args.len()
                ),
            ));
        }
        let mut target = Scope {
            helpers: Rc::clone(&scope.helpers),
            naturals: BTreeMap::new(),
            bases: BTreeMap::new(),
            operations: BTreeMap::new(),
            context: self.program.budget.copy_context(span, &scope.context)?,
            values: BTreeMap::new(),
            moved: BTreeSet::new(),
            next_binding: Rc::clone(&scope.next_binding),
        };
        for (formal, arg) in interface.statics.iter().zip(args) {
            self.tick(arg.span)?;
            match &formal.kind {
                StaticKind::Natural => {
                    let value = self.static_natural(arg, scope)?;
                    target
                        .naturals
                        .insert(self.program.budget.key(arg.span, &formal.key)?, value);
                }
                StaticKind::Basis => {
                    let value = match &arg.kind {
                        StaticOpKind::Type(ty) => normalize::ty(
                            ty,
                            self.index(),
                            scope,
                            Stage::Basis,
                            None,
                            &self.program.budget,
                        )?,
                        StaticOpKind::Name(name) => self
                            .local(name)
                            .and_then(|key| scope.bases.get(key))
                            .map(|ty| self.program.budget.copy_ty(arg.span, ty))
                            .transpose()?
                            .ok_or_else(|| {
                                SourceError::new(
                                    "static",
                                    arg.span,
                                    "expected a Basis argument; use type(T) for a concrete type",
                                )
                            })?,
                        _ => {
                            return Err(SourceError::new(
                                "static",
                                arg.span,
                                "expected a Basis argument; use type(T) for a concrete type",
                            ));
                        }
                    };
                    target
                        .bases
                        .insert(self.program.budget.key(arg.span, &formal.key)?, value);
                }
                StaticKind::Operation { .. } => {}
            }
        }
        // Do not hold a borrowed interface while checking actual Op arguments.
        let count = self.program.interfaces[&id].statics.len();
        for (ordinal, arg) in args.iter().enumerate().take(count) {
            let formal = &self.program.interfaces[&id].statics[ordinal];
            let StaticKind::Operation {
                basis,
                meaning,
                access: required,
            } = &formal.kind
            else {
                continue;
            };
            let basis = normalize::substitute(
                basis,
                &target.naturals,
                &target.bases,
                span,
                &self.program.budget,
            )?;
            let meaning = *meaning;
            let required = *required;
            let key = self.program.budget.key(arg.span, &formal.key)?;
            let operation = self.operation(arg, scope)?;
            normalize::expect(
                &operation.basis,
                &basis,
                &scope.context,
                arg.span,
                &self.program.budget,
            )
            .map_err(|error| operation_mismatch(error, &operation.basis, &basis))?;
            for capability in [Access::Apply, Access::Adjoint, Access::Controlled] {
                if required[super::super::super::formals::access_index(capability)] {
                    access(&operation, capability, arg.span)?;
                }
            }
            if let Some(required) = meaning {
                self.obligation(
                    arg.span,
                    ObligationKind::MeaningEquality {
                        required,
                        supplied: operation.meaning,
                    },
                )?;
            }
            target.operations.insert(key, operation);
        }
        let callee = self.program.decl(id);
        let index = &self.program.indices[&id];
        for requirement in &callee.requires {
            if let Requirement::Predicate(predicate) = requirement {
                let counterexample =
                    normalize::predicate(predicate, index, &target, false, &self.program.budget)
                        .map_err(|mut error| {
                            // The original callee predicate is evaluated under the
                            // actual arguments, so a failed substitution belongs
                            // to this caller occurrence, not the callee's file.
                            error.span = span;
                            error.message =
                                format!("substituted callee obligation: {}", error.message);
                            error
                        })?;
                if counterexample.feasible_budgeted(
                    span,
                    "while checking callee natural premise",
                    &mut |span, cells| self.program.budget.preparation_charge(span, cells),
                )? {
                    return Err(SourceError::new(
                        "size",
                        span,
                        "callee natural premise is not implied by caller guards",
                    ));
                }
            }
        }
        if id == self.definition && runtime_recursion {
            let mut decreases = false;
            for formal in &self.program.interfaces[&id].statics {
                if matches!(formal.kind, StaticKind::Natural) {
                    let old = &scope.naturals[&formal.key];
                    let new = &target.naturals[&formal.key];
                    if !scope.context.proves_le_budgeted(
                        new,
                        old,
                        span,
                        "self-recursion must not increase any natural parameter",
                        &mut |span, cells| self.program.budget.preparation_charge(span, cells),
                    )? {
                        return Err(SourceError::new(
                            "cycle",
                            span,
                            "self-recursion must not increase any natural parameter",
                        ));
                    }
                    let successor =
                        new.add_budgeted(&Linear::constant(1), span, &mut |span, cells| {
                            self.program.budget.preparation_charge(span, cells)
                        })?;
                    decreases |= scope.context.proves_le_budgeted(
                        &successor,
                        old,
                        span,
                        "while checking recursive decrease",
                        &mut |span, cells| self.program.budget.preparation_charge(span, cells),
                    )?;
                }
            }
            if !decreases {
                return Err(SourceError::new(
                    "cycle",
                    span,
                    "self-recursion needs a strictly decreasing natural argument",
                ));
            }
            // Only this runtime edge has a successfully checked decrease.
        } else {
            self.edge(id, span)?;
        }
        let interface = &self.program.interfaces[&id];
        self.program.budget.charge(span, interface.params.len())?;
        let params = interface
            .params
            .iter()
            .map(|ty| {
                normalize::substitute(
                    ty,
                    &target.naturals,
                    &target.bases,
                    span,
                    &self.program.budget,
                )
            })
            .collect::<Result<_>>()?;
        let result = normalize::substitute(
            &interface.result,
            &target.naturals,
            &target.bases,
            span,
            &self.program.budget,
        )?;
        // Conservative transparent-provider paths, recorded before code.
        // This includes unused actual Ops; it does not claim maximal inference.
        // Full body/principal-effect and real materialization checks still follow.
        let mut access = [true; 3];
        for operation in target.operations.values() {
            self.tick(span)?;
            access[1] &= operation.access[0] && operation.access[1];
            access[2] &= operation.access.iter().all(|available| *available);
        }
        Ok((params, result, access))
    }
    pub(super) fn call(
        &mut self,
        name: &Ident,
        static_args: &[StaticOp],
        runtime: &[Expr],
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        if let Some(operation) = self.local(name).and_then(|key| scope.operations.get(key)) {
            if !static_args.is_empty() || runtime.len() != 1 {
                return Err(SourceError::new(
                    "arity",
                    span,
                    "operation application takes one quantum argument",
                ));
            }
            access(operation, Access::Apply, span)?;
            let ty = Ty::quantum(self.program.budget.copy_ty(span, &operation.basis)?);
            self.expr(&runtime[0], scope, Some(&ty))?;
            return Ok(ty);
        }
        match self.resolve(name)? {
            Target::Primitive(primitive) => {
                self.program
                    .budget
                    .charge(span, primitive.module.len() + primitive.name.len() + 2)?;
                let path = format!("{}::{}", primitive.module, primitive.name);
                let primitive =
                    primitive::Primitive::lookup(&path).expect("typed sealed resolution");
                if static_args.len() != primitive.natural_arity() {
                    return Err(SourceError::new(
                        "static-arity",
                        span,
                        "primitive static argument arity mismatch",
                    ));
                }
                if runtime.len() != primitive.runtime_arity() {
                    return Err(SourceError::new(
                        "arity",
                        span,
                        "runtime argument arity mismatch",
                    ));
                }
                self.effects.add(primitive.effect(), span);
                if primitive.dependent() {
                    self.program.budget.charge(span, runtime.len())?;
                    let inputs = runtime
                        .iter()
                        .map(|expr| self.expr(expr, scope, None))
                        .collect::<Result<_>>()?;
                    primitive.output(inputs, span, &self.program.budget)
                } else {
                    self.program.budget.charge(span, static_args.len())?;
                    let ns = static_args
                        .iter()
                        .map(|arg| self.static_natural(arg, scope))
                        .collect::<Result<Vec<_>>>()?;
                    let (inputs, result) =
                        primitive.fixed(&ns, &scope.context, span, &self.program.budget)?;
                    for (expr, ty) in runtime.iter().zip(&inputs) {
                        // Only a direct, still-live lexical tuple binding can
                        // carry binding-specific help. Retain its identity,
                        // without copying the owner/type tree.
                        let binding = if ty.quantum_basis().is_some() {
                            if let ExprKind::Name(name) = &expr.kind {
                                self.local(name).and_then(|key| {
                                    scope.values.get(key).and_then(|value| {
                                        (value.ty.linear() && value.ty.tuple_fields().is_some())
                                            .then_some((key.id, name.text.as_str()))
                                    })
                                })
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        self.expr(expr, scope, Some(ty)).map_err(|mut error| {
                            if error.code == "type"
                                && !error.primitive_argument_located
                                && error.span == expr.span
                                && ty.quantum_basis().is_some()
                            {
                                error.primitive_argument_located = true;
                                if let Some((id, name)) = binding {
                                    error.span = self.index().table.binder(id).span;
                                    error.message = format!(
                                        "binding `{name}` contains a tuple of owners: {}; help: destructure the tuple at this binding (for cnot, `let (a, b) = cnot(a, b);`); a single name binds the whole returned tuple",
                                        error.message
                                    );
                                } else {
                                    error.span = span;
                                }
                            }
                            error
                        })?;
                    }
                    Ok(result)
                }
            }
            Target::Declaration(id) => {
                let kind = self.program.decl(id).kind;
                if kind == FnKind::Meaning {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "Meaning declarations are not ordinary runtime callees",
                    ));
                }
                let (inputs, result, _) =
                    self.specialize(id, static_args, scope, span, kind != FnKind::Classical)?;
                self.tick(span)?;
                self.effects.call(id, span);
                if inputs.len() != runtime.len() {
                    return Err(SourceError::new(
                        "arity",
                        span,
                        "runtime argument arity mismatch",
                    ));
                }
                for (expr, ty) in runtime.iter().zip(&inputs) {
                    self.expr(expr, scope, Some(ty))?;
                }
                Ok(result)
            }
        }
    }
    pub(super) fn named_operation(
        &mut self,
        name: &Ident,
        args: &[StaticOp],
        scope: &Scope,
        allow_primitive: bool,
    ) -> Result<Operation> {
        if let Some(operation) = self.local(name).and_then(|key| scope.operations.get(key)) {
            if !args.is_empty() {
                return Err(SourceError::new(
                    "static-arity",
                    name.span,
                    "an Op formal has no static arguments",
                ));
            }
            self.program.budget.ty(name.span, &operation.basis)?;
            return Ok(operation.clone());
        }
        if self.local(name).is_some() {
            return Err(SourceError::new(
                "type",
                name.span,
                "a local or spent runtime value cannot be a static operation",
            ));
        }
        match self.resolve(name)? {
            Target::Primitive(primitive) if allow_primitive => {
                let path = format!("{}::{}", primitive.module, primitive.name);
                let primitive =
                    primitive::Primitive::lookup(&path).expect("resolved typed primitive");
                if primitive.dependent() {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "polymorphic primitive needs the actual target basis",
                    ));
                }
                let ns = args
                    .iter()
                    .map(|arg| self.static_natural(arg, scope))
                    .collect::<Result<Vec<_>>>()?;
                let (inputs, result) =
                    primitive.fixed(&ns, &scope.context, name.span, &self.program.budget)?;
                if primitive.effect() != Effect::Unitary
                    || inputs.len() != 1
                    || !result.is_quantum_owner()
                {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "operation must be a unary quantum endomorphism",
                    ));
                }
                normalize::expect(
                    &inputs[0],
                    &result,
                    &scope.context,
                    name.span,
                    &self.program.budget,
                )?;
                let Kind::Q(basis) = result.kind else {
                    unreachable!("checked unary quantum result");
                };
                Ok(Operation {
                    basis: *basis,
                    meaning: None,
                    access: [true; 3],
                })
            }
            Target::Primitive(primitive) => {
                let mut message =
                    "static provider requires an ordinary fn with inferred Unitary body effect"
                        .to_owned();
                if primitive.module == "std::quantum"
                    && matches!(primitive.name, "h" | "x" | "z" | "t")
                {
                    self.program.budget.charge(
                        name.span,
                        name.text.len().saturating_mul(2).saturating_add(128),
                    )?;
                    message.push_str(&format!("; wrap the gate as `fn wrapped_gate(q: Q<Bit>) -> Q<Bit> {{ {}(q) }}` and pass `[wrapped_gate]`", name.text));
                }
                Err(SourceError::new("type", name.span, message))
            }
            Target::Declaration(id) => {
                if matches!(
                    self.program.decl(id).kind,
                    FnKind::Classical | FnKind::Meaning
                ) {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "static provider requires an ordinary runtime function",
                    ));
                }
                let (inputs, result, access) =
                    self.specialize(id, args, scope, name.span, false)?;
                if inputs.len() != 1 || !result.is_quantum_owner() {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "operation provider requires Q<A> -> Q<A> with one exact quantum input",
                    ));
                }
                normalize::expect(
                    &inputs[0],
                    &result,
                    &scope.context,
                    name.span,
                    &self.program.budget,
                )?;
                self.tick(name.span)?;
                self.effects.require_unitary(id, name.span);
                self.obligation(
                    name.span,
                    ObligationKind::Provider {
                        provider: id,
                        meaning: None,
                    },
                )?;
                let Kind::Q(basis) = result.kind else {
                    unreachable!("checked owner result");
                };
                Ok(Operation {
                    basis: *basis,
                    meaning: None,
                    access,
                })
            }
        }
    }
    pub(super) fn operation(&mut self, op: &StaticOp, scope: &Scope) -> Result<Operation> {
        if self.depth >= 64 {
            return Err(SourceError::new(
                "limit",
                op.span,
                "static operation exceeds depth 64",
            ));
        }
        self.depth += 1;
        let result = self.operation_inner(op, scope);
        self.depth -= 1;
        result
    }
    fn operation_inner(&mut self, op: &StaticOp, scope: &Scope) -> Result<Operation> {
        self.tick(op.span)?;
        match &op.kind {
            StaticOpKind::Name(name) => self.named_operation(name, &[], scope, false),
            StaticOpKind::Specialize { name, arguments } => {
                self.named_operation(name, arguments, scope, false)
            }
            StaticOpKind::Bind {
                implementation,
                meaning,
            } => {
                let mut operation = self.named_operation(implementation, &[], scope, false)?;
                let meaning =
                    declarations::meaning_identity(self.program, self.definition, meaning)?;
                self.edge(meaning, op.span)?;
                normalize::expect(
                    &operation.basis,
                    &self.program.interfaces[&meaning].result,
                    &scope.context,
                    op.span,
                    &self.program.budget,
                )?;
                self.obligation(
                    op.span,
                    ObligationKind::MeaningEquality {
                        required: meaning,
                        supplied: operation.meaning,
                    },
                )?;
                operation.meaning = Some(meaning);
                Ok(operation)
            }
            StaticOpKind::Inverse(child) => {
                let mut child = self.operation(child, scope)?;
                child.access.swap(0, 1);
                child.meaning = None;
                Ok(child)
            }
            StaticOpKind::Controlled(child) => {
                let child = self.operation(child, scope)?;
                let basis = Ty::pair(Ty::bit(), child.basis);
                self.program.budget.ty(op.span, &basis)?;
                Ok(Operation {
                    basis,
                    meaning: None,
                    access: [child.access[2]; 3],
                })
            }
            StaticOpKind::Repeat(count, child) => {
                let (Count::Natural(n) | Count::Power(n)) = count;
                normalize::natural(n, self.index(), scope, None, &self.program.budget)?;
                let mut child = self.operation(child, scope)?;
                child.meaning = None;
                Ok(child)
            }
            StaticOpKind::Then(a, b)
            | StaticOpKind::Tensor(a, b)
            | StaticOpKind::Conjugate(a, b) => {
                let a = self.operation(a, scope)?;
                let b = self.operation(b, scope)?;
                let tensor = matches!(op.kind, StaticOpKind::Tensor(..));
                if !tensor {
                    normalize::expect(
                        &a.basis,
                        &b.basis,
                        &scope.context,
                        op.span,
                        &self.program.budget,
                    )
                    .map_err(|error| operation_mismatch(error, &b.basis, &a.basis))?;
                }
                let access = if matches!(op.kind, StaticOpKind::Conjugate(..)) {
                    std::array::from_fn(|i| a.access[0] && a.access[1] && b.access[i])
                } else {
                    std::array::from_fn(|i| a.access[i] && b.access[i])
                };
                let basis = if tensor {
                    Ty::pair(a.basis, b.basis)
                } else {
                    a.basis
                };
                self.program.budget.ty(op.span, &basis)?;
                Ok(Operation {
                    basis,
                    meaning: None,
                    access,
                })
            }
            StaticOpKind::Type(_) | StaticOpKind::Natural(_) => Err(SourceError::new(
                "static",
                op.span,
                "expected an operation argument",
            )),
        }
    }
}

fn operation_mismatch(mut error: SourceError, actual: &Ty, expected: &Ty) -> SourceError {
    if error.code == "type" {
        error.message = format!(
            "static operation basis mismatch: expected `Op<{}>`, found `Op<{}>`",
            expected.display(Stage::Basis),
            actual.display(Stage::Basis)
        );
    }
    error
}
