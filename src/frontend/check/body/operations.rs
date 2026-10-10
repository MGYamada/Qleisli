//! Checked static descriptions and actual original callee specialization.
use super::*;

pub(super) struct PreparedAccess<'a> {
    pub expression: &'a Expr,
    pub ty: Ty,
}
#[derive(Clone, Copy)]
pub(super) enum CallArguments<'a> {
    Source(RuntimeArguments<'a>),
    Places(&'a [PreparedAccess<'a>]),
}
impl<'a> CallArguments<'a> {
    fn len(self) -> usize {
        match self {
            Self::Source(args) => args.len(),
            Self::Places(args) => args.len(),
        }
    }
    fn get(self, index: usize) -> &'a Expr {
        match self {
            Self::Source(args) => args.get(index),
            Self::Places(args) => args[index].expression,
        }
    }
    fn iter(self) -> impl Iterator<Item = &'a Expr> {
        (0..self.len()).map(move |index| self.get(index))
    }
}
impl Checker<'_, '_> {
    fn call_argument(
        &mut self,
        arguments: CallArguments<'_>,
        index: usize,
        scope: &mut Scope,
        expected: Option<&Ty>,
    ) -> Result<Ty> {
        match arguments {
            CallArguments::Source(args) => self.expr(args.get(index), scope, expected),
            CallArguments::Places(args) => {
                let arg = &args[index];
                if let Some(expected) = expected {
                    normalize::expect(
                        &arg.ty,
                        expected,
                        &scope.context,
                        arg.expression.span,
                        &self.program.budget,
                    )?;
                }
                self.program.budget.copy_ty(arg.expression.span, &arg.ty)
            }
        }
    }
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
                codomain,
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
            let codomain = codomain
                .as_ref()
                .map(|ty| {
                    normalize::substitute(
                        ty,
                        &target.naturals,
                        &target.bases,
                        span,
                        &self.program.budget,
                    )
                })
                .transpose()?;
            let mode = OperationMode {
                arrows: codomain.is_some(),
                ceiling: formal_effect(&codomain, required),
            };
            let meaning = *meaning;
            let required = *required;
            let key = self.program.budget.key(arg.span, &formal.key)?;
            let operation = self.operation_with(arg, scope, mode)?;
            normalize::expect(
                &operation.basis,
                &basis,
                &scope.context,
                arg.span,
                &self.program.budget,
            )
            .map_err(|error| operation_mismatch(error, &operation.basis, &basis))?;
            if let Some(codomain) = &codomain {
                normalize::expect(
                    operation.output(),
                    codomain,
                    &scope.context,
                    arg.span,
                    &self.program.budget,
                )?;
            }
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
        runtime: RuntimeArguments<'_>,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        self.call_arguments(
            name,
            static_args,
            CallArguments::Source(runtime),
            scope,
            span,
        )
    }
    pub(super) fn call_arguments(
        &mut self,
        name: &Ident,
        static_args: &[StaticOp],
        runtime: CallArguments<'_>,
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
            let output = operation
                .codomain
                .as_ref()
                .map(|ty| self.program.budget.copy_ty(span, ty))
                .transpose()?;
            let effect = operation.effect;
            self.call_argument(runtime, 0, scope, Some(&ty))?;
            self.effects.add(effect, span);
            return Ok(output.map(Ty::quantum).unwrap_or(ty));
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
                    let inputs = (0..runtime.len())
                        .map(|index| self.call_argument(runtime, index, scope, None))
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
                    for (index, (expr, ty)) in runtime.iter().zip(&inputs).enumerate() {
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
                        self.call_argument(runtime, index, scope, Some(ty)).map_err(|mut error| {
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
                for (index, ty) in inputs.iter().enumerate() {
                    self.call_argument(runtime, index, scope, Some(ty))?;
                }
                Ok(result)
            }
        }
    }
    pub(super) fn require_access_unitary(
        &mut self,
        name: &Ident,
        scope: &Scope,
        span: Span,
    ) -> Result<()> {
        if self
            .local(name)
            .and_then(|key| scope.operations.get(key))
            .is_none()
        {
            match self.resolve(name)? {
                Target::Declaration(id) => {
                    self.tick(span)?;
                    self.effects.require_unitary(id, span);
                }
                Target::Primitive(primitive) => {
                    self.program
                        .budget
                        .charge(span, primitive.module.len() + primitive.name.len() + 2)?;
                    let path = format!("{}::{}", primitive.module, primitive.name);
                    if primitive::Primitive::lookup(&path)
                        .expect("typed sealed resolution")
                        .effect()
                        != Effect::Unitary
                    {
                        return Err(SourceError::new(
                            "effect",
                            span,
                            "excl requires a coherent Unitary call; measurement, reset, discard and release remain consuming operations",
                        ));
                    }
                }
            }
        }
        Ok(())
    }
    pub(super) fn exclusive_call(
        &mut self,
        name: &Ident,
        static_args: &[StaticOp],
        arguments: &[AccessArgument],
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        if arguments
            .iter()
            .any(|argument| argument.selection.is_some())
        {
            return self.indexed_access_call(name, static_args, arguments, scope, span);
        }
        self.program
            .budget
            .charge(span, arguments.len().saturating_mul(3))?;
        if arguments.is_empty() || arguments.len() > 64 {
            return Err(SourceError::new(
                "arity",
                span,
                "quantum access calls require one to 64 arguments",
            ));
        }
        let mut owners = Vec::new();
        let mut seen = BTreeSet::new();
        for argument in arguments {
            let ExprKind::Name(owner) = &argument.value.kind else {
                return Err(SourceError::new(
                    "unsupported",
                    argument.value.span,
                    "exclusive access currently requires a whole lexical Q<A> owner",
                ));
            };
            let key = self.local(owner).ok_or_else(|| {
                SourceError::new(
                    "ownership",
                    owner.span,
                    "exclusive access requires a live lexical owner",
                )
            })?;
            let binding = scope.values.get(key).ok_or_else(|| {
                SourceError::new(
                    "ownership",
                    owner.span,
                    "exclusive access cannot use a consumed owner",
                )
            })?;
            if binding.ty.quantum_basis().is_none() {
                return Err(SourceError::new(
                    "type",
                    owner.span,
                    "exclusive access requires one Q<A> owner, including zero-width owners",
                ));
            }
            if !seen.insert(binding.identity) {
                return Err(SourceError::new(
                    "ownership",
                    owner.span,
                    "exclusive arguments overlap the same quantum owner",
                ));
            }
            owners.push((
                self.program.budget.key(owner.span, key)?,
                Binding {
                    identity: binding.identity,
                    ty: self.program.budget.copy_ty(owner.span, &binding.ty)?,
                },
            ));
        }
        self.require_access_unitary(name, scope, span)?;
        let result = self.call(
            name,
            static_args,
            RuntimeArguments::Accesses(arguments),
            scope,
            span,
        )?;
        let mut types = owners
            .iter()
            .map(|(_, binding)| self.program.budget.copy_ty(span, &binding.ty))
            .collect::<Result<Vec<_>>>()?;
        let expected = if types.len() == 1 {
            types.pop().expect("one owner")
        } else {
            Ty::tuple(types)
        };
        normalize::expect(
            &result,
            &expected,
            &scope.context,
            span,
            &self.program.budget,
        )
        .map_err(|mut error| {
            error.message = format!(
                "exclusive call must return the same exact ordered owner interface: {}",
                error.message
            );
            error
        })?;
        if arguments
            .iter()
            .any(|argument| argument.access == QuantumAccess::Ctrl)
        {
            // Retain the original obligation even when specialization never
            // visits this declaration, branch, loop body or provider call.
            self.obligation(span, ObligationKind::ControlSectors)?;
        }
        for (key, binding) in owners {
            scope.moved.remove(&binding.identity);
            scope.values.insert(key, binding);
        }
        Ok(Ty::unit())
    }
    pub(super) fn named_operation(
        &mut self,
        name: &Ident,
        args: &[StaticOp],
        scope: &Scope,
        allow_primitive: bool,
    ) -> Result<Operation> {
        self.named_operation_with(name, args, scope, allow_primitive, OperationMode::ENDO)
    }
    fn named_operation_with(
        &mut self,
        name: &Ident,
        args: &[StaticOp],
        scope: &Scope,
        allow_primitive: bool,
        mode: OperationMode,
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
            if let Some(codomain) = &operation.codomain {
                self.program.budget.ty(name.span, codomain)?;
                if !mode.arrows {
                    normalize::expect(
                        codomain,
                        &operation.basis,
                        &scope.context,
                        name.span,
                        &self.program.budget,
                    )?;
                }
            }
            if operation.effect > mode.ceiling {
                return Err(SourceError::new(
                    "effect",
                    name.span,
                    crate::frontend::effects::unitary_required(
                        "opaque operation effect exceeds required Unitary ceiling",
                    ),
                ));
            }
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
                let ports = crate::frontend::types::UnaryInterface::new(&inputs, &result)
                    .expect("checked unary provider arity");
                normalize::expect(
                    ports.input,
                    ports.output,
                    &scope.context,
                    name.span,
                    &self.program.budget,
                )?;
                let Kind::Q(basis) = result.kind else {
                    unreachable!("checked unary quantum result");
                };
                Ok(Operation {
                    basis: *basis,
                    codomain: None,
                    effect: Effect::Unitary,
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
                let (inputs, result, mut access) =
                    self.specialize(id, args, scope, name.span, false)?;
                if inputs.len() != 1 || !inputs[0].is_quantum_owner() || !result.is_quantum_owner()
                {
                    return Err(SourceError::new(
                        "type",
                        name.span,
                        "operation provider requires Q<A> -> Q<A> with one exact quantum input",
                    ));
                }
                let ports = crate::frontend::types::UnaryInterface::new(&inputs, &result)
                    .expect("checked unary provider arity");
                if !mode.arrows {
                    normalize::expect(
                        ports.input,
                        ports.output,
                        &scope.context,
                        name.span,
                        &self.program.budget,
                    )?;
                }
                self.tick(name.span)?;
                self.effects.require_effect(id, mode.ceiling, name.span);
                self.obligation(
                    name.span,
                    ObligationKind::Provider {
                        provider: id,
                        ceiling: mode.ceiling,
                        meaning: None,
                    },
                )?;
                let Kind::Q(basis) = result.kind else {
                    unreachable!("checked owner result");
                };
                let (basis, codomain) = if mode.arrows {
                    let Kind::Q(input) =
                        inputs.into_iter().next().expect("checked unary input").kind
                    else {
                        unreachable!("checked owner input")
                    };
                    (*input, Some(*basis))
                } else {
                    (*basis, None)
                };
                if let Some(codomain) = &codomain {
                    match normalize::expect(
                        codomain,
                        &basis,
                        &scope.context,
                        name.span,
                        &self.program.budget,
                    ) {
                        Ok(()) => {}
                        Err(error) if error.code == "type" => access[2] = false,
                        Err(error) => return Err(error),
                    }
                }
                Ok(Operation {
                    basis,
                    codomain,
                    effect: mode.ceiling,
                    meaning: None,
                    access,
                })
            }
        }
    }
    fn operation_with(
        &mut self,
        op: &StaticOp,
        scope: &Scope,
        mode: OperationMode,
    ) -> Result<Operation> {
        if self.depth >= 64 {
            return Err(SourceError::new(
                "limit",
                op.span,
                "static operation exceeds depth 64",
            ));
        }
        self.depth += 1;
        let result = self.operation_inner_with(op, scope, mode);
        self.depth -= 1;
        result
    }
    fn operation_inner(&mut self, op: &StaticOp, scope: &Scope) -> Result<Operation> {
        self.operation_inner_with(op, scope, OperationMode::ENDO)
    }
    fn operation_inner_with(
        &mut self,
        op: &StaticOp,
        scope: &Scope,
        mode: OperationMode,
    ) -> Result<Operation> {
        self.tick(op.span)?;
        match &op.kind {
            StaticOpKind::Name(name) => self.named_operation_with(name, &[], scope, false, mode),
            StaticOpKind::Specialize { name, arguments } => {
                self.named_operation_with(name, arguments, scope, false, mode)
            }
            StaticOpKind::Bind {
                implementation,
                meaning,
            } => {
                let mut operation =
                    self.named_operation_with(implementation, &[], scope, false, mode)?;
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
                if operation.codomain.is_some() {
                    normalize::expect(
                        operation.output(),
                        &self.program.interfaces[&meaning].result,
                        &scope.context,
                        op.span,
                        &self.program.budget,
                    )?;
                }
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
                let mut child = self.operation_with(child, scope, mode.unitary())?;
                if let Some(codomain) = child.codomain.take() {
                    child.codomain = Some(std::mem::replace(&mut child.basis, codomain));
                }
                // Description construction itself requires the operand's
                // verified adjoint path, even when an outer use masks Apply.
                access(&child, Access::Adjoint, op.span)?;
                child.access.swap(0, 1);
                child.meaning = None;
                Ok(child)
            }
            StaticOpKind::Controlled(child) => {
                let child = self.operation_with(child, scope, mode.unitary())?;
                if let Some(codomain) = &child.codomain {
                    normalize::expect(
                        codomain,
                        &child.basis,
                        &scope.context,
                        op.span,
                        &self.program.budget,
                    )?;
                }
                let basis = Ty::pair(Ty::bit(), child.basis);
                self.program.budget.ty(op.span, &basis)?;
                Ok(Operation {
                    basis,
                    codomain: None,
                    effect: Effect::Unitary,
                    meaning: None,
                    access: [child.access[2]; 3],
                })
            }
            StaticOpKind::Repeat(count, child) => {
                let (Count::Natural(n) | Count::Power(n)) = count;
                normalize::natural(n, self.index(), scope, None, &self.program.budget)?;
                let mut child = self.operation_with(child, scope, mode)?;
                if let Some(codomain) = &child.codomain {
                    normalize::expect(
                        codomain,
                        &child.basis,
                        &scope.context,
                        op.span,
                        &self.program.budget,
                    )?;
                }
                child.meaning = None;
                Ok(child)
            }
            StaticOpKind::Then(a, b)
            | StaticOpKind::Tensor(a, b)
            | StaticOpKind::Conjugate(a, b) => {
                let conjugate = matches!(op.kind, StaticOpKind::Conjugate(..));
                let a =
                    self.operation_with(a, scope, if conjugate { mode.unitary() } else { mode })?;
                let b = self.operation_with(b, scope, mode)?;
                let tensor = matches!(op.kind, StaticOpKind::Tensor(..));
                if !tensor {
                    normalize::expect(
                        a.output(),
                        &b.basis,
                        &scope.context,
                        op.span,
                        &self.program.budget,
                    )
                    .map_err(|error| operation_mismatch(error, &b.basis, a.output()))?;
                    if conjugate {
                        normalize::expect(
                            b.output(),
                            &b.basis,
                            &scope.context,
                            op.span,
                            &self.program.budget,
                        )?;
                    }
                }
                let access = if conjugate {
                    std::array::from_fn(|i| a.access[0] && a.access[1] && b.access[i])
                } else {
                    std::array::from_fn(|i| a.access[i] && b.access[i])
                };
                let effect = a.effect.max(b.effect);
                let codomain = if conjugate || (a.codomain.is_none() && b.codomain.is_none()) {
                    None
                } else if tensor {
                    Some(Ty::pair(
                        self.program.budget.copy_ty(op.span, a.output())?,
                        self.program.budget.copy_ty(op.span, b.output())?,
                    ))
                } else {
                    Some(self.program.budget.copy_ty(op.span, b.output())?)
                };
                let basis = if tensor {
                    Ty::pair(a.basis, b.basis)
                } else {
                    a.basis
                };
                self.program.budget.ty(op.span, &basis)?;
                if let Some(codomain) = &codomain {
                    self.program.budget.ty(op.span, codomain)?;
                }
                Ok(Operation {
                    basis,
                    codomain,
                    effect,
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
