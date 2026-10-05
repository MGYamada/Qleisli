//! Generic preparation checks. No value here crosses the verified IR boundary.
use super::ast::*;
use super::linear::{self, Context, Linear};
use super::primitive::{Guard, Primitive, Size, TypeRule, TypeShape, dependent_output};
use super::{BasisBinding, Error, OperationBinding, ParsedProgram, Result, Span};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

use crate::frontend::resolve::{self, DefId, Failure, Profile, Target};
use crate::frontend::types::Kind;
type Ty = crate::frontend::types::Type<Linear>;
impl Ty {
    fn cells(&self) -> usize {
        self.owner_shape_size()
            .nodes
            .max(self.storage_size(4096, 64).map_or(4097, |size| size.nodes))
    }
    fn depth(&self) -> usize {
        self.owner_shape_size()
            .depth
            .max(self.storage_size(4096, 64).map_or(65, |size| size.depth))
    }
    fn bounded(&self, span: Span) -> Result<()> {
        if self.cells() > 4096 || self.depth() > 64 {
            Err(err(
                "limit",
                span,
                "inferred type exceeds 4096 cells or depth 64",
            ))
        } else {
            Ok(())
        }
    }
}
#[derive(Clone)]
struct Operation {
    ty: Ty,
    access: BTreeSet<String>,
}
#[derive(Clone)]
struct Scope {
    naturals: BTreeMap<BinderKey, Linear>,
    bases: BTreeMap<BinderKey, Ty>,
    operations: BTreeMap<BinderKey, Operation>,
    context: Context,
    values: BTreeMap<BinderKey, Binding>,
    moved: BTreeSet<usize>,
    next_binding: Rc<Cell<usize>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Binding {
    identity: usize,
    ty: Ty,
}
fn err(code: &'static str, span: Span, message: impl Into<String>) -> Error {
    Error::new(code, span, message)
}
// Callee syntax uses the caller's substituted sizes. A capacity failure here
// belongs to the caller's application, not a byte offset in another module.
fn call_capacity<T>(result: Result<T>, span: Span) -> Result<T> {
    result.map_err(|mut error| {
        if error.code == "limit" {
            error.span = span;
            error.message = format!(
                "while checking substituted callee obligation: {}",
                error.message
            );
        }
        error
    })
}
fn all_access() -> BTreeSet<String> {
    ["Apply", "Adjoint", "Controlled"].map(String::from).into()
}
fn basis(b: &Basis, scope: &Scope) -> Result<Ty> {
    b.storage_size(4096, 64).ok_or_else(|| {
        err(
            "limit",
            Span::default(),
            "operation basis exceeds type capacity",
        )
    })?;
    Ok(Ty::quantum(ty(b, scope, Span::default())?))
}
fn ty(t: &Type, scope: &Scope, span: Span) -> Result<Ty> {
    t.storage_size(4096, 64)
        .ok_or_else(|| err("limit", span, "source type exceeds type capacity"))?;
    let mut nodes = 0usize;
    let mut pending = vec![(t, 1usize)];
    while let Some((node, depth)) = pending.pop() {
        match &node.kind {
            Kind::Parameter(parameter) => {
                let replacement = parameter
                    .key
                    .as_ref()
                    .and_then(|key| scope.bases.get(key))
                    .ok_or_else(|| {
                        err(
                            "type",
                            parameter.span,
                            format!(
                                "Basis parameter {} is unavailable in this ordered kind",
                                parameter.name
                            ),
                        )
                    })?;
                let size = replacement
                    .storage_size(4096, 64)
                    .ok_or_else(|| err("limit", span, "substituted Basis exceeds type capacity"))?;
                nodes = nodes.saturating_add(size.nodes);
                if depth.saturating_add(size.depth).saturating_sub(1) > 64 {
                    return Err(err("limit", span, "substituted Basis exceeds depth 64"));
                }
            }
            Kind::Q(child) => pending.push((child, depth)),
            Kind::Tuple(fields) => {
                nodes = nodes.saturating_add(1);
                pending.extend(fields.iter().rev().map(|child| (child, depth + 1)));
            }
            _ => nodes = nodes.saturating_add(1),
        }
        if nodes > 4096 {
            return Err(err(
                "limit",
                span,
                "substituted Basis exceeds 4096 type nodes",
            ));
        }
    }
    let result = t.map_parts(
        &mut |size| linear::natural(size, &scope.naturals, &scope.context),
        &mut |parameter| {
            parameter
                .key
                .as_ref()
                .and_then(|key| scope.bases.get(key))
                .cloned()
                .ok_or_else(|| {
                    err(
                        "type",
                        parameter.span,
                        format!(
                            "Basis parameter {} is unavailable in this ordered kind",
                            parameter.name
                        ),
                    )
                })
        },
    )?;
    result.bounded(span)?;
    Ok(result)
}
fn equivalent(a: &Ty, b: &Ty, context: &Context, span: Span) -> Result<bool> {
    a.equivalent_by(b, &mut |a, b| {
        Ok(
            context.proves_le(a, b, span, "while checking type size equality")?
                && context.proves_le(b, a, span, "while checking type size equality")?,
        )
    })
}
fn expect(actual: &Ty, expected: &Ty, context: &Context, span: Span) -> Result<()> {
    if equivalent(actual, expected, context, span)? {
        Ok(())
    } else {
        Err(err(
            "type",
            span,
            format!(
                "type or tuple/size shape mismatch: expected {:?}, found {:?}",
                expected.sized_debug(),
                actual.sized_debug()
            ),
        ))
    }
}
fn prove(context: &Context, a: &Linear, b: &Linear, span: Span, message: &str) -> Result<()> {
    if context.proves_le(a, b, span, message)? {
        Ok(())
    } else {
        Err(err("size", span, message))
    }
}

fn declaration(f: &Function) -> Result<Scope> {
    let mut names = BTreeSet::new();
    let mut naturals = BTreeMap::new();
    for p in &f.parameters {
        let name = match p {
            Parameter::Natural(n) | Parameter::Basis(n) | Parameter::Operation(n, _) => n,
        };
        if !names.insert(name.name.clone()) {
            return Err(err(
                "name",
                f.span,
                format!("duplicate static parameter {name}"),
            ));
        }
        if matches!(p, Parameter::Natural(_)) {
            naturals.insert(name.key().clone(), Linear::variable(name.key()));
        }
    }
    let mut scope = Scope {
        context: Context::natural(naturals.keys().cloned())?,
        naturals,
        bases: BTreeMap::new(),
        operations: BTreeMap::new(),
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    for requirement in &f.requires {
        if let Requirement::Predicate(p) = requirement {
            scope.context = linear::predicate(p, &scope.naturals, &scope.context, true)?;
        }
    }
    if !scope
        .context
        .feasible(f.span, "while checking declared natural premises")?
    {
        return Err(err(
            "size",
            f.span,
            "inconsistent declared natural premises",
        ));
    }
    let mut preceding_naturals = BTreeSet::new();
    for p in &f.parameters {
        if let Parameter::Natural(name) = p {
            preceding_naturals.insert(name.key().clone());
        }
        if let Parameter::Basis(name) = p {
            scope.bases.insert(
                name.key().clone(),
                Ty::parameter(crate::frontend::types::TypeParameter {
                    key: Some(name.key().clone()),
                    name: name.name.clone(),
                    span: f.span,
                }),
            );
        }
        if let Parameter::Operation(name, b) = p {
            let mut kind_scope = scope.clone();
            kind_scope
                .naturals
                .retain(|key, _| preceding_naturals.contains(key));
            scope.operations.insert(
                name.key().clone(),
                Operation {
                    ty: basis(b, &kind_scope)?,
                    access: BTreeSet::new(),
                },
            );
        }
    }
    for requirement in &f.requires {
        if let Requirement::Access(kind, name, span) = requirement {
            let op = name
                .local
                .as_ref()
                .and_then(|key| scope.operations.get_mut(key))
                .ok_or_else(|| {
                    err(
                        "access",
                        *span,
                        format!("access requirement names no operation parameter: {name}"),
                    )
                })?;
            if !op.access.insert(kind.clone()) {
                return Err(err(
                    "access",
                    *span,
                    "duplicate operation access requirement",
                ));
            }
        }
    }
    let mut arguments = BTreeSet::new();
    for (pattern, t, span) in &f.arguments {
        // Parameter uniqueness covers the complete argument list, not only
        // each individual product pattern. Wildcards introduce no name.
        let mut pending = vec![pattern];
        while let Some(pattern) = pending.pop() {
            match pattern {
                Pattern::Name(name, span) => {
                    if !arguments.insert(&name.name) {
                        return Err(err("name", *span, "duplicate runtime parameter"));
                    }
                }
                Pattern::Tuple(fields, _) => pending.extend(fields.iter().rev()),
                Pattern::Wildcard(_) => {}
            }
        }
        bind(pattern, ty(t, &scope, *span)?, &mut scope)?;
    }
    let _ = ty(&f.result, &scope, f.span)?;
    Ok(scope)
}
fn bind_name(name: &BindingName, t: Ty, span: Span, scope: &mut Scope) -> Result<()> {
    t.bounded(span)?;
    let retained: usize = scope
        .values
        .iter()
        .filter(|(key, _)| name.shadowed.as_ref() != Some(*key))
        .map(|(_, b)| b.ty.cells())
        .sum();
    if retained.saturating_add(t.cells()) > 16_384 {
        return Err(err(
            "limit",
            span,
            "scope exceeds 16384 retained type cells",
        ));
    }
    if name.name == "_"
        || name.shadowed.as_ref().is_some_and(|key| {
            scope.naturals.contains_key(key)
                || scope.bases.contains_key(key)
                || scope.operations.contains_key(key)
        })
    {
        return Err(err(
            "name",
            span,
            format!("binding {name} shadows a static parameter/index or discards a value"),
        ));
    }
    if name
        .shadowed
        .as_ref()
        .and_then(|key| scope.values.get(key))
        .is_some_and(|binding| binding.ty.linear())
    {
        return Err(err(
            "ownership",
            span,
            format!("binding {name} would drop a live quantum owner"),
        ));
    }
    let identity = scope.next_binding.get();
    scope.next_binding.set(
        identity
            .checked_add(1)
            .ok_or_else(|| err("limit", span, "binding identity exhausted"))?,
    );
    if let Some(previous) = &name.shadowed {
        scope.values.remove(previous);
    }
    scope
        .values
        .insert(name.key().clone(), Binding { identity, ty: t });
    Ok(())
}
fn bind(pattern: &Pattern, t: Ty, scope: &mut Scope) -> Result<()> {
    fn go(pattern: &Pattern, t: Ty, scope: &mut Scope, names: &mut BTreeSet<String>) -> Result<()> {
        match (pattern, t.kind) {
            (Pattern::Wildcard(span), kind) => {
                if (Ty { kind }).linear() {
                    return Err(err(
                        "ownership",
                        *span,
                        "wildcard would discard quantum ownership",
                    ));
                }
                Ok(())
            }
            (Pattern::Name(name, span), kind) => {
                if !names.insert(name.name.clone()) {
                    return Err(err("name", *span, "duplicate name in binding pattern"));
                }
                bind_name(name, Ty { kind }, *span, scope)
            }
            (Pattern::Tuple(patterns, span), kind) => {
                let t = Ty { kind };
                if t.pattern_fields(patterns.len()).is_none() {
                    return Err(err(
                        "type",
                        *span,
                        "binding pattern does not preserve tuple arity and nesting",
                    ));
                }
                if let Kind::Tuple(fields) = t.kind {
                    for (p, t) in patterns.iter().zip(fields) {
                        go(p, t, scope, names)?;
                    }
                }
                Ok(())
            }
        }
    }
    go(pattern, t, scope, &mut BTreeSet::new())
}
/// Host entry selection has no module privilege. Providers are selected in the
/// entry module's context, with the same visibility rule as source imports.
fn visible_definition<'a>(
    program: &'a ParsedProgram,
    path: &str,
    requester: Option<&str>,
    span: Span,
) -> Result<(DefId, &'a str, &'a Function)> {
    let id = program.resolution.qualified(path).map_err(|kind| {
        let mut error = ParsedProgram::resolution_error(Failure {
            module: String::new(),
            span,
            kind,
        });
        error.module = None;
        error
    })?;
    let (owner, function) = program.definition(id);
    if !program.resolution.visible(
        id,
        requester.and_then(|name| program.resolution.module(name)),
    ) {
        return Err(
            err("visibility", span, format!("dependency {path} is private"))
                .in_module(requester.unwrap_or(owner)),
        );
    }
    Ok((id, owner, function))
}

pub(super) fn program(program: &mut ParsedProgram) -> Result<()> {
    let mut edges = BTreeMap::new();
    let mut effect_bodies = BTreeMap::new();
    let names: Vec<_> = program.modules.keys().cloned().collect();
    for module in &names {
        let owner = program.resolution.module(module).expect("known module");
        let imports = program
            .resolution
            .imports(owner, &program.syntax[module], Profile::Sized)
            .map_err(ParsedProgram::resolution_error)?;
        let parsed = program.modules.get_mut(module).expect("projected module");
        for function in &mut parsed.functions {
            Arc::make_mut(function.lexical.as_mut().expect("indexed sized function")).bind_globals(
                |name| {
                    program
                        .resolution
                        .local(owner, name)
                        .map(Target::Declaration)
                        .or_else(|| imports.imports.get(name).copied())
                },
            );
        }
        // Source order controls diagnostics; DefId controls identity. They are
        // deliberately independent, including for forward sibling calls.
        for function in &program.modules[module].functions {
            let id = program
                .resolution
                .local(owner, &function.name)
                .expect("projected declaration");
            let result = (|| {
                let mut scope = declaration(function)?;
                let expected = ty(&function.result, &scope, function.span)?;
                let mut checker = Checker {
                    program,
                    definition: id,
                    function,
                    edges: BTreeSet::new(),
                    effects: crate::frontend::effects::BodyEffects::new(function.span),
                };
                checker.block(&function.body, &mut scope, Some(&expected))?;
                if scope.values.values().any(|binding| binding.ty.linear()) {
                    return Err(err(
                        "ownership",
                        function.body.span,
                        "function leaves live quantum arguments unconsumed",
                    ));
                }
                Ok((checker.edges, checker.effects))
            })();
            let (dependencies, body) = result.map_err(|e| e.in_module(module))?;
            effect_bodies.insert(id, body);
            edges.insert(
                id,
                dependencies
                    .into_iter()
                    .map(|id| (id, Span::default()))
                    .collect(),
            );
        }
        program.resolution.set_scope(owner, imports);
    }
    // Every self-call has already passed the symbolic decrease check above.
    if let Some((_, _, path)) = resolve::cycle(edges.keys().copied(), &edges, true) {
        let id = *path.last().expect("cycle target");
        return Err(err(
            "cycle",
            Span::default(),
            "mutually recursive dependency cycle is unsupported",
        )
        .in_module(&program.resolution.declaration(id).name.0));
    }
    let effects = crate::frontend::effects::infer(&effect_bodies).ok_or_else(|| {
        err(
            "effect",
            Span::default(),
            "unresolved typed effect dependency",
        )
    })?;
    // Preserve source-order diagnostics. An annotation never supplies a class
    // to either this solution or a callee during the preceding typed pass.
    for module in &names {
        let owner = program.resolution.module(module).expect("known module");
        for function in &program.modules[module].functions {
            let id = program
                .resolution
                .local(owner, &function.name)
                .expect("known function");
            let declaration =
                &program.syntax[module].decls[program.resolution.declaration(id).ast_index];
            let fact =
                crate::frontend::effects::FunctionEffect::checked(declaration.kind, effects[&id])
                    .ok_or_else(|| {
                    err(
                        "effect",
                        effect_bodies[&id].origin(&effects),
                        crate::frontend::effects::assertion_error(
                            &function.name,
                            declaration.kind,
                            effects[&id],
                        ),
                    )
                    .in_module(module)
                })?;
            for (provider, span) in &effect_bodies[&id].unitary {
                if effects[provider] != Effect::Unitary {
                    return Err(err(
                        "effect",
                        *span,
                        crate::frontend::effects::unitary_required(
                            "operation provider's inferred body effect must be Unitary",
                        ),
                    )
                    .in_module(module));
                }
            }
            program.effects.insert(id, fact);
        }
    }
    for (id, declaration) in program.resolution.declarations() {
        program
            .modules
            .get_mut(&declaration.name.0)
            .expect("known module")
            .functions[declaration.ast_index]
            .effect = effects[&id];
    }
    Ok(())
}

struct Checker<'a> {
    program: &'a ParsedProgram,
    function: &'a Function,
    definition: DefId,
    edges: BTreeSet<DefId>,
    effects: crate::frontend::effects::BodyEffects,
}
impl Checker<'_> {
    fn effect(&mut self, effect: Effect, span: Span) -> Result<()> {
        self.effects.add(effect, span);
        Ok(())
    }
    fn resolve(&mut self, name: &Reference, _scope: &Scope, span: Span) -> Result<Target> {
        let target = match name.target(
            self.function
                .lexical
                .as_ref()
                .expect("indexed sized function"),
        ) {
            ResolvedUse::Local(_) => {
                return Err(err(
                    "name",
                    span,
                    format!("{name} is shadowed or is not a transparent function"),
                ));
            }
            ResolvedUse::Global(target) => target,
            ResolvedUse::Unresolved => {
                return Err(err("name", span, format!("unresolved function {name}")));
            }
        };
        if let Target::Declaration(id) = target {
            self.edges.insert(id);
        }
        Ok(target)
    }

    fn specialize(
        &mut self,
        id: DefId,
        args: &[Argument],
        scope: &Scope,
        span: Span,
        recursion: bool,
    ) -> Result<(Vec<Ty>, Ty, Effect)> {
        let (module, f) = self.program.definition(id);
        if args.len() != f.parameters.len() {
            let parameters = f
                .parameters
                .iter()
                .map(|p| match p {
                    Parameter::Natural(n) => format!("{}: Nat", n.name),
                    Parameter::Basis(n) => format!("{}: Basis", n.name),
                    Parameter::Operation(n, _) => format!("{}: Op", n.name),
                })
                .collect::<Vec<_>>()
                .join(", ");
            return Err(err(
                "static",
                span,
                format!(
                    "wrong number of static arguments for {module}::{}: expected [{parameters}], received {}",
                    f.name,
                    args.len()
                ),
            ));
        }
        let mut target = Scope {
            naturals: BTreeMap::new(),
            bases: BTreeMap::new(),
            operations: BTreeMap::new(),
            context: scope.context.clone(),
            values: BTreeMap::new(),
            moved: BTreeSet::new(),
            next_binding: Rc::clone(&scope.next_binding),
        };
        for (p, a) in f.parameters.iter().zip(args) {
            if let Parameter::Basis(name) = p {
                let basis = match a {
                    Argument::Basis(basis, at) => ty(basis, scope, *at)?,
                    Argument::Natural(Natural {
                        kind: NatKind::Name(reference),
                        ..
                    }) => reference.get(&scope.bases).cloned().ok_or_else(|| {
                        err(
                            "static",
                            span,
                            "expected a Basis argument; use type(T) for a concrete type",
                        )
                    })?,
                    _ => {
                        return Err(err(
                            "static",
                            span,
                            "expected a Basis argument; use type(T) for a concrete type",
                        ));
                    }
                };
                target.bases.insert(name.key().clone(), basis);
            }
            if let Parameter::Natural(name) = p {
                let Argument::Natural(n) = a else {
                    return Err(err("static", span, "expected natural argument"));
                };
                target.naturals.insert(
                    name.key().clone(),
                    linear::natural(n, &scope.naturals, &scope.context)?,
                );
            }
        }
        for (p, a) in f.parameters.iter().zip(args) {
            if let Parameter::Operation(name, b) = p {
                let op = self.operation(a, scope, span)?;
                expect(
                    &op.ty,
                    &call_capacity(basis(b, &target), span)?,
                    &scope.context,
                    span,
                )?;
                target.operations.insert(name.key().clone(), op);
            }
        }
        call_capacity(requirements(f, &target, span), span)?;
        if recursion && id == self.definition {
            let mut decreases = false;
            for p in &f.parameters {
                if let Parameter::Natural(name) = p {
                    let old = &scope.naturals[name.key()];
                    let new = &target.naturals[name.key()];
                    prove(
                        &scope.context,
                        new,
                        old,
                        span,
                        "self-recursion must not increase any natural parameter",
                    )?;
                    decreases |= scope.context.proves_le(
                        &linear::at(
                            new.add(&Linear::constant(1)),
                            span,
                            "while checking recursive decrease",
                        )?,
                        old,
                        span,
                        "while checking recursive decrease",
                    )?;
                }
            }
            if !decreases {
                return Err(err(
                    "cycle",
                    span,
                    "self-recursion needs a strictly decreasing natural argument",
                ));
            }
        }
        Ok((
            f.arguments
                .iter()
                .map(|(_, t, _)| call_capacity(ty(t, &target, span), span))
                .collect::<Result<_>>()?,
            call_capacity(ty(&f.result, &target, span), span)?,
            f.effect,
        ))
    }
    fn operation(&mut self, argument: &Argument, scope: &Scope, span: Span) -> Result<Operation> {
        match argument {
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                ..
            }) if name.get(&scope.operations).is_some() => {
                if name.get(&scope.values).is_some() {
                    return Err(err("name", span, "operation parameter is shadowed"));
                }
                Ok(name.get(&scope.operations).unwrap().clone())
            }
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                span,
                ..
            }) => self.provider(name, &[], scope, *span),
            Argument::Definition(name, args, span) => self.provider(name, args, scope, *span),
            Argument::Repeat(count, child, span) => {
                match count {
                    Count::Natural(n) | Count::Power(n) => {
                        let _ = linear::natural(n, &scope.naturals, &scope.context)?;
                    }
                }
                self.operation(child, scope, *span)
            }
            _ => Err(err("static", span, "expected an operation argument")),
        }
    }
    fn provider(
        &mut self,
        name: &Reference,
        args: &[Argument],
        scope: &Scope,
        span: Span,
    ) -> Result<Operation> {
        let Target::Declaration(id) = self.resolve(name, scope, span)? else {
            return Err(err(
                "unsupported",
                span,
                "primitive operation references are outside this preparation profile",
            ));
        };
        let (inputs, result, effect) = self.specialize(id, args, scope, span, true)?;
        self.effects.require_unitary(id, span);
        let group = match inputs.as_slice() {
            [input] => input.clone(),
            _ => Ty::tuple(inputs.clone()),
        };
        if effect != Effect::Unitary || inputs.is_empty() || !group.quantum_group() {
            return Err(err(
                "type",
                span,
                "operation provider must be unitary and preserve its complete quantum input group",
            ));
        }
        expect(&group, &result, &scope.context, span)?;
        Ok(Operation {
            ty: result,
            access: all_access(),
        })
    }
    fn block(&mut self, block: &Block, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        let initial = scope.values.clone();
        let outer_identities: BTreeSet<_> =
            initial.values().map(|binding| binding.identity).collect();
        for statement in &block.statements {
            match statement {
                Statement::Let(pattern, expr) => {
                    let value = self.expr(expr, scope, None)?;
                    bind(pattern, value, scope)?;
                }
                Statement::Drop(expr) => {
                    if self.expr(expr, scope, None)?.linear() {
                        return Err(err(
                            "ownership",
                            expr.span,
                            "expression statement would discard quantum ownership",
                        ));
                    }
                }
            }
        }
        let result = self.expr(&block.result, scope, expected)?;
        for (name, binding) in &scope.values {
            if !outer_identities.contains(&binding.identity) && binding.ty.linear() {
                return Err(err(
                    "ownership",
                    block.span,
                    format!("block leaves live quantum owner {name}"),
                ));
            }
        }
        // A same-spelling inner declaration is a new binding. Restore only
        // unmoved outer identities; no local owner escapes through its name.
        scope.values = initial
            .into_iter()
            .filter(|(_, binding)| !scope.moved.contains(&binding.identity))
            .collect();
        Ok(result)
    }
    fn expr(&mut self, expr: &Expr, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        let span = expr.span;
        let result = match &expr.kind {
            ExprKind::Unit => Ty::unit(),
            ExprKind::Boolean(operation, operands) => {
                use crate::frontend::ordinary::{self, OperandFailure};
                ordinary::evaluate(
                    *operation,
                    operands.iter(),
                    &mut (&mut *self, &mut *scope),
                    |(checker, scope), operand| checker.expr(operand, scope, None),
                    Clone::clone,
                    |_, failure| match failure {
                        OperandFailure::Arity { expected, actual } => err(
                            "type",
                            span,
                            format!(
                                "Boolean operation requires {expected} operands, found {actual}"
                            ),
                        ),
                        OperandFailure::Type(ty) => err(
                            "type",
                            span,
                            format!(
                                "{} requires ordinary Bit operands, found {:?}",
                                operation.operator(),
                                ty.sized_debug()
                            ),
                        ),
                    },
                )?;
                operation.result_type()
            }
            ExprKind::Name(name) => {
                let binding = name.get(&scope.values).cloned().ok_or_else(|| {
                    err(
                        "ownership",
                        span,
                        format!("unbound or consumed value {name}"),
                    )
                })?;
                if binding.ty.linear() {
                    scope
                        .values
                        .remove(name.local.as_ref().expect("resolved runtime binding"));
                    scope.moved.insert(binding.identity);
                }
                binding.ty
            }
            ExprKind::Tuple(fields) => {
                let types = match expected.map(|t| &t.kind) {
                    Some(Kind::Tuple(ts)) if ts.len() == fields.len() => Some(ts),
                    _ => None,
                };
                let mut result = Vec::new();
                let mut cells = 1usize;
                for (i, e) in fields.iter().enumerate() {
                    let field = self.expr(e, scope, types.map(|ts| &ts[i]))?;
                    cells = cells.saturating_add(field.cells());
                    if cells > 4096 || field.depth() >= 64 {
                        return Err(err(
                            "limit",
                            span,
                            "inferred tuple exceeds 4096 cells or depth 64",
                        ));
                    }
                    result.push(field);
                }
                Ty::tuple(result)
            }
            ExprKind::Call(name, args, runtime) => {
                if let Some(op) = name.get(&scope.operations).cloned() {
                    if !args.is_empty() || runtime.len() != 1 {
                        return Err(err(
                            "type",
                            span,
                            "operation application takes one quantum argument",
                        ));
                    }
                    access(&op, "Apply", span)?;
                    self.expr(&runtime[0], scope, Some(&op.ty))?;
                    op.ty
                } else {
                    let target = self.resolve(name, scope, span)?;
                    match target {
                        Target::Primitive(_) => {
                            let primitive =
                                Primitive::lookup(&self.program.resolution.target_path(target))
                                    .expect("resolved primitive");
                            self.primitive_call(primitive, args, runtime, scope, span)?
                        }
                        Target::Declaration(id) => {
                            let (inputs, result, effect) =
                                self.specialize(id, args, scope, span, true)?;
                            self.effects.call(id, span);
                            self.effect(effect, span)?;
                            if inputs.len() != runtime.len() {
                                return Err(err("type", span, "runtime argument arity mismatch"));
                            }
                            for (expr, t) in runtime.iter().zip(&inputs) {
                                self.expr(expr, scope, Some(t))?;
                            }
                            result
                        }
                    }
                }
            }
            ExprKind::Adjoint(arg, input) => {
                let op = self.operation(arg, scope, span)?;
                access(&op, "Adjoint", span)?;
                self.expr(input, scope, Some(&op.ty))?;
                op.ty
            }
            ExprKind::Controlled(arg, inputs) => {
                let op = self.operation(arg, scope, span)?;
                access(&op, "Controlled", span)?;
                if inputs.len() != 2 {
                    return Err(err(
                        "type",
                        span,
                        "controlled application takes control and target",
                    ));
                }
                self.expr(&inputs[0], scope, Some(&Ty::quantum(Ty::bit())))?;
                self.expr(&inputs[1], scope, Some(&op.ty))?;
                Ty::tuple(vec![Ty::quantum(Ty::bit()), op.ty])
            }
            ExprKind::If(predicate, yes, no) => {
                let mut a = scope.clone();
                let mut b = scope.clone();
                a.context = linear::predicate(predicate, &scope.naturals, &scope.context, true)?;
                b.context = linear::predicate(predicate, &scope.naturals, &scope.context, false)?;
                let a_ty = self.block(yes, &mut a, expected)?;
                let b_ty = self.block(no, &mut b, expected)?;
                if a.values != b.values {
                    return Err(err(
                        "ownership",
                        span,
                        "static branches must consume the same owners and preserve outer binding types",
                    ));
                }
                scope.values = a.values;
                scope.moved.extend(a.moved);
                if let Some(t) = expected {
                    t.clone()
                } else {
                    expect(&b_ty, &a_ty, &scope.context, span)?;
                    a_ty
                }
            }
            ExprKind::Fold {
                index,
                start,
                end,
                carry,
                initial,
                body,
            } => {
                if index.shadowed.is_some() {
                    return Err(err(
                        "name",
                        span,
                        "static fold index shadows an existing name",
                    ));
                }
                let start = linear::natural(start, &scope.naturals, &scope.context)?;
                let end = linear::natural(end, &scope.naturals, &scope.context)?;
                prove(
                    &scope.context,
                    &start,
                    &end,
                    span,
                    "static fold requires start <= end",
                )?;
                let carry_ty = self.expr(initial, scope, expected)?;
                let mut inner = scope.clone();
                // Quantum resources enter a fold only through its explicit carry.
                inner.values.retain(|_, binding| !binding.ty.linear());
                let i = Linear::variable(index.key());
                inner.context = inner.context.push(&[
                    linear::at(start.sub(&i), span, "while checking fold bound")?,
                    linear::at(
                        i.add(&Linear::constant(1)).and_then(|n| n.sub(&end)),
                        span,
                        "while checking fold bound",
                    )?,
                    i.scale(-1)?,
                ]);
                inner.naturals.insert(index.key().clone(), i);
                bind(carry, carry_ty.clone(), &mut inner)?;
                self.block(body, &mut inner, Some(&carry_ty))?;
                if inner.values.values().any(|binding| binding.ty.linear()) {
                    return Err(err(
                        "ownership",
                        span,
                        "fold body leaves a carry owner unconsumed",
                    ));
                }
                carry_ty
            }
        };
        if let Some(t) = expected {
            expect(&result, t, &scope.context, span)?;
        }
        Ok(result)
    }

    fn primitive_call(
        &mut self,
        primitive: Primitive,
        args: &[Argument],
        runtime: &[Expr],
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        let signature = primitive.signature();
        if signature.types.dependent() {
            if args.len() != signature.natural_arity {
                return Err(err(
                    "static",
                    span,
                    "primitive static argument arity mismatch",
                ));
            }
            if runtime.len() != signature.types.runtime_arity() {
                return Err(err("type", span, "runtime argument arity mismatch"));
            }
            self.effect(signature.effect, span)?;
            // Evaluate every argument once in source order before applying
            // the same exact-tree rule used by concrete elaboration.
            let inputs = runtime
                .iter()
                .map(|expr| self.expr(expr, scope, None))
                .collect::<Result<Vec<_>>>()?;
            return dependent_output(signature.types, &inputs.iter().collect::<Vec<_>>(), span);
        }
        let (inputs, result, effect) = primitive_signature(primitive, args, scope, span)?;
        self.effect(effect, span)?;
        if inputs.len() != runtime.len() {
            return Err(err("type", span, "runtime argument arity mismatch"));
        }
        for (expr, ty) in runtime.iter().zip(&inputs) {
            self.expr(expr, scope, Some(ty))?;
        }
        Ok(result)
    }
}
fn access(op: &Operation, kind: &str, span: Span) -> Result<()> {
    if op.access.contains(kind) {
        Ok(())
    } else {
        Err(err(
            "access",
            span,
            format!("missing {kind} operation access"),
        ))
    }
}
fn requirements(f: &Function, scope: &Scope, span: Span) -> Result<()> {
    for requirement in &f.requires {
        match requirement {
            Requirement::Access(kind, name, _) => {
                access(
                    scope
                        .operations
                        .get(name.local.as_ref().ok_or_else(|| {
                            err("access", span, "unresolved operation requirement")
                        })?)
                        .ok_or_else(|| err("access", span, "missing operation argument"))?,
                    kind,
                    span,
                )?
            }
            Requirement::Predicate(p) => {
                let counterexample = linear::predicate(p, &scope.naturals, &scope.context, false)?;
                if counterexample.feasible(span, "while checking callee natural premise")? {
                    return Err(err(
                        "size",
                        span,
                        "callee natural premise is not implied by caller guards",
                    ));
                }
            }
        }
    }
    Ok(())
}
fn primitive_signature(
    primitive: Primitive,
    args: &[Argument],
    scope: &Scope,
    span: Span,
) -> Result<(Vec<Ty>, Ty, Effect)> {
    let signature = primitive.signature();
    let TypeRule::Fixed(inputs, output) = signature.types else {
        return Err(err(
            "type",
            span,
            "primitive requires an inferred quantum input type",
        ));
    };
    if args.len() != signature.natural_arity {
        return Err(err(
            "static",
            span,
            "primitive static argument arity mismatch",
        ));
    }
    let ns: Vec<Linear> = args
        .iter()
        .map(|a| {
            let Argument::Natural(n) = a else {
                return Err(err("static", span, "primitive requires natural arguments"));
            };
            linear::natural(n, &scope.naturals, &scope.context)
        })
        .collect::<Result<_>>()?;
    match signature.guard {
        Guard::None => {}
        Guard::RegisterIndex => prove(
            &scope.context,
            &linear::at(
                ns[1].add(&Linear::constant(1)),
                span,
                "while checking register index",
            )?,
            &ns[0],
            span,
            "register index needs k < n",
        )?,
    }
    fn size(size: Size, ns: &[Linear], span: Span) -> Result<Linear> {
        match size {
            Size::Constant(n) => Ok(Linear::constant(i128::from(n))),
            Size::Argument(index, offset) => linear::at(
                ns[index].add(&Linear::constant(i128::from(offset))),
                span,
                "while checking primitive register size",
            ),
        }
    }
    fn shape(t: TypeShape, ns: &[Linear], span: Span) -> Result<Ty> {
        Ok(match t {
            TypeShape::Unit => Ty::unit(),
            TypeShape::QUnit => Ty::quantum(Ty::unit()),
            TypeShape::Bit => Ty::quantum(Ty::bit()),
            TypeShape::CBit => Ty::bit(),
            TypeShape::Bits(n) => Ty::quantum(Ty::bits(size(n, ns, span)?)),
            TypeShape::CBits(n) => Ty::bits(size(n, ns, span)?),
            TypeShape::Tuple(fields) => Ty::tuple(
                fields
                    .iter()
                    .map(|t| shape(*t, ns, span))
                    .collect::<Result<_>>()?,
            ),
        })
    }
    Ok((
        inputs
            .iter()
            .map(|t| shape(*t, &ns, span))
            .collect::<Result<_>>()?,
        shape(output, &ns, span)?,
        signature.effect,
    ))
}

// Closed bindings are explicit. Diagnostics describe the failed set comparison
// in deterministic order; they cannot supply a substitution or select a provider.
fn check_bindings<V>(
    actual: &BTreeMap<String, V>,
    expected: &BTreeSet<&str>,
    category: &str,
    subject: &str,
    span: Span,
) -> Result<()> {
    if actual.len() == expected.len() && expected.iter().all(|name| actual.contains_key(*name)) {
        return Ok(());
    }
    let missing = expected
        .iter()
        .filter(|name| !actual.contains_key(**name))
        .copied()
        .collect::<Vec<_>>()
        .join(", ");
    let unexpected = actual
        .keys()
        .filter(|name| !expected.contains(name.as_str()))
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(", ");
    Err(err(
        "static",
        span,
        format!(
            "concrete {category} bindings for {subject} must exactly match the declaration; missing [{missing}]; unexpected [{unexpected}]"
        ),
    ))
}

fn concrete_scope(
    f: &Function,
    types: &BTreeMap<String, BasisBinding>,
    naturals: &BTreeMap<String, u32>,
    subject: &str,
) -> Result<Scope> {
    let expected_types = f
        .parameters
        .iter()
        .filter_map(|p| match p {
            Parameter::Basis(name) => Some(name.name.as_str()),
            _ => None,
        })
        .collect();
    check_bindings(types, &expected_types, "Basis", subject, f.span)?;
    let expected: BTreeSet<_> = f
        .parameters
        .iter()
        .filter_map(|p| {
            if let Parameter::Natural(n) = p {
                Some(n.name.as_str())
            } else {
                None
            }
        })
        .collect();
    check_bindings(naturals, &expected, "natural", subject, f.span)?;
    // Concrete entry sizes are diagnostic preparation data, not capacities of a
    // future runtime or coefficient domain. Keep construction bounded and small.
    let scope = Scope {
        bases: f
            .parameters
            .iter()
            .filter_map(|p| match p {
                Parameter::Basis(name) => Some(
                    types[&name.name]
                        .ty
                        .map_sizes(&mut |n| Ok::<_, Error>(Linear::constant(i128::from(*n))))
                        .map(|ty| (name.key().clone(), ty)),
                ),
                _ => None,
            })
            .collect::<Result<_>>()?,
        naturals: f
            .parameters
            .iter()
            .filter_map(|parameter| match parameter {
                Parameter::Natural(name) => Some((
                    name.key().clone(),
                    Linear::constant(i128::from(naturals[&name.name])),
                )),
                Parameter::Operation(..) | Parameter::Basis(_) => None,
            })
            .collect(),
        operations: BTreeMap::new(),
        context: Context::natural([])?,
        values: BTreeMap::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    Ok(scope)
}
pub(super) fn instantiate(
    program: &ParsedProgram,
    entry: &str,
    types: &BTreeMap<String, BasisBinding>,
    naturals: &BTreeMap<String, u32>,
    operations: &BTreeMap<String, OperationBinding>,
) -> Result<(DefId, BTreeMap<String, DefId>)> {
    let (entry_id, module, f) = visible_definition(program, entry, None, Span::default())?;
    let result = (|| {
        let subject = format!("entry {module}::{}", f.name);
        let mut scope = concrete_scope(f, types, naturals, &subject)?;
        let mut provider_ids = BTreeMap::new();
        let expected: BTreeSet<_> = f
            .parameters
            .iter()
            .filter_map(|p| {
                if let Parameter::Operation(n, _) = p {
                    Some(n.name.as_str())
                } else {
                    None
                }
            })
            .collect();
        check_bindings(operations, &expected, "operation", &subject, f.span)?;
        for p in &f.parameters {
            if let Parameter::Operation(name, b) = p {
                let binding = &operations[&name.name];
                let (provider_id, provider_module, provider) =
                    visible_definition(program, &binding.definition, Some(module), f.span)?;
                if provider
                    .parameters
                    .iter()
                    .any(|p| matches!(p, Parameter::Operation(..)))
                {
                    return Err(err(
                        "unsupported",
                        f.span,
                        "concrete providers with operation parameters are unsupported",
                    ));
                }
                provider_ids.insert(name.name.clone(), provider_id);
                let subject = format!(
                    "operation {} provider {provider_module}::{}",
                    name.name, provider.name
                );
                let provider_scope =
                    concrete_scope(provider, &binding.types, &binding.naturals, &subject)?;
                requirements(provider, &provider_scope, f.span)?;
                let output = ty(&provider.result, &provider_scope, provider.span)?;
                if provider.effect != Effect::Unitary {
                    return Err(err(
                        "effect",
                        f.span,
                        crate::frontend::effects::unitary_required(&format!(
                            "operation provider {provider_module}::{} has inferred body effect `{:?}`; Unitary is required",
                            provider.name, provider.effect
                        )),
                    ));
                }
                if provider.arguments.len() != 1 || !output.is_quantum_owner() {
                    return Err(err(
                        "type",
                        f.span,
                        "concrete provider must have one quantum input with the exact output type",
                    ));
                }
                expect(
                    &ty(
                        &provider.arguments[0].1,
                        &provider_scope,
                        provider.arguments[0].2,
                    )?,
                    &output,
                    &scope.context,
                    f.span,
                )?;
                expect(&output, &basis(b, &scope)?, &scope.context, f.span)?;
                scope.operations.insert(
                    name.key().clone(),
                    Operation {
                        ty: output,
                        access: all_access(),
                    },
                );
            }
        }
        requirements(f, &scope, f.span)?;
        for (_, t, _) in &f.arguments {
            let _ = ty(t, &scope, f.span)?;
        }
        let _ = ty(&f.result, &scope, f.span)?;
        Ok((entry_id, provider_ids))
    })();
    result.map_err(|e| e.in_module(module))
}

#[cfg(test)]
mod visibility_tests {
    use super::*;

    #[test]
    fn private_definitions_remain_visible_in_their_own_module() {
        let program = ParsedProgram::parse(BTreeMap::from([(
            "local".into(),
            "use local::f; unitary fn f(q: Q<Bit>) -> Q<Bit> { q }".into(),
        )]))
        .unwrap();
        let span = Span::default();
        assert!(visible_definition(&program, "local::f", Some("local"), span).is_ok());
        for requester in [None, Some("other")] {
            assert_eq!(
                visible_definition(&program, "local::f", requester, span)
                    .unwrap_err()
                    .code(),
                "visibility"
            );
        }
    }
}
