//! Generic preparation checks. No value here crosses the verified IR boundary.
use super::ast::*;
use super::linear::{self, Context, Linear};
use super::primitive::{Guard, Primitive, Size, TypeShape};
use super::{Error, OperationBinding, ParsedProgram, Result, Span};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::frontend::resolve::{self, DefId, Failure, Profile, Target};
use crate::frontend::types::Kind;
type Ty = crate::frontend::types::Type<Linear>;
impl Ty {
    fn cells(&self) -> usize {
        self.owner_shape_size().nodes
    }
    fn depth(&self) -> usize {
        self.owner_shape_size().depth
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
    naturals: BTreeMap<String, Linear>,
    operations: BTreeMap<String, Operation>,
    context: Context,
    values: BTreeMap<String, Binding>,
    shadows: BTreeSet<String>,
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
    Ok(match b {
        Basis::Bit => Ty::quantum(Ty::bit()),
        Basis::Bits(n) => Ty::quantum(Ty::bits(linear::natural(
            n,
            &scope.naturals,
            &scope.context,
        )?)),
    })
}
fn ty(t: &Type, scope: &Scope, span: Span) -> Result<Ty> {
    let result = match t {
        Type::Quantum(b) => basis(b, scope)?,
        Type::CBit => Ty::bit(),
        Type::CBits(n) => Ty::bits(linear::natural(n, &scope.naturals, &scope.context)?),
        Type::Tuple(xs) => Ty::tuple(
            xs.iter()
                .map(|x| ty(x, scope, span))
                .collect::<Result<_>>()?,
        ),
    };
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
            Parameter::Natural(n) | Parameter::Operation(n, _) => n,
        };
        if !names.insert(name.clone()) {
            return Err(err(
                "name",
                f.span,
                format!("duplicate static parameter {name}"),
            ));
        }
        if matches!(p, Parameter::Natural(_)) {
            naturals.insert(name.clone(), Linear::variable(name));
        }
    }
    let mut scope = Scope {
        context: Context::natural(naturals.keys().cloned())?,
        naturals,
        operations: BTreeMap::new(),
        values: BTreeMap::new(),
        shadows: BTreeSet::new(),
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
    for p in &f.parameters {
        if let Parameter::Operation(name, b) = p {
            scope.operations.insert(
                name.clone(),
                Operation {
                    ty: basis(b, &scope)?,
                    access: BTreeSet::new(),
                },
            );
        }
    }
    for requirement in &f.requires {
        if let Requirement::Access(kind, name, span) = requirement {
            let op = scope.operations.get_mut(name).ok_or_else(|| {
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
    for (name, t, span) in &f.arguments {
        if !arguments.insert(name) {
            return Err(err("name", *span, "duplicate runtime parameter"));
        }
        bind_name(name, ty(t, &scope, *span)?, *span, &mut scope)?;
    }
    let _ = ty(&f.result, &scope, f.span)?;
    Ok(scope)
}
fn bind_name(name: &str, t: Ty, span: Span, scope: &mut Scope) -> Result<()> {
    t.bounded(span)?;
    let retained: usize = scope
        .values
        .iter()
        .filter(|(key, _)| key.as_str() != name)
        .map(|(_, b)| b.ty.cells())
        .sum();
    if retained.saturating_add(t.cells()) > 16_384 {
        return Err(err(
            "limit",
            span,
            "scope exceeds 16384 retained type cells",
        ));
    }
    if name == "_" || scope.naturals.contains_key(name) || scope.operations.contains_key(name) {
        return Err(err(
            "name",
            span,
            format!("binding {name} shadows a static parameter/index or discards a value"),
        ));
    }
    if scope
        .values
        .get(name)
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
    scope
        .values
        .insert(name.into(), Binding { identity, ty: t });
    scope.shadows.insert(name.into());
    Ok(())
}
fn bind(pattern: &Pattern, t: Ty, scope: &mut Scope) -> Result<()> {
    fn go(pattern: &Pattern, t: Ty, scope: &mut Scope, names: &mut BTreeSet<String>) -> Result<()> {
        match (pattern, t.kind) {
            (Pattern::Name(name, span), kind) => {
                if !names.insert(name.clone()) {
                    return Err(err("name", *span, "duplicate name in binding pattern"));
                }
                bind_name(name, Ty { kind }, *span, scope)
            }
            (Pattern::Tuple(patterns, span), Kind::Tuple(fields))
                if patterns.len() == fields.len() =>
            {
                for (p, t) in patterns.iter().zip(fields) {
                    go(p, t, scope, names)?;
                }
                let _ = span;
                Ok(())
            }
            (Pattern::Tuple(_, span), _) => Err(err(
                "type",
                *span,
                "binding pattern does not preserve tuple arity and nesting",
            )),
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
    let names: Vec<_> = program.modules.keys().cloned().collect();
    for module in &names {
        let parsed = &program.modules[module];
        let owner = program.resolution.module(module).expect("known module");
        let imports = program
            .resolution
            .imports(owner, &program.syntax[module], Profile::Sized)
            .map_err(ParsedProgram::resolution_error)?;
        let id = program
            .resolution
            .local(owner, &parsed.function.name)
            .expect("projected declaration");
        let result = (|| {
            let mut scope = declaration(&parsed.function)?;
            let expected = ty(&parsed.function.result, &scope, parsed.function.span)?;
            let mut checker = Checker {
                program,
                module,
                definition: id,
                function: &parsed.function,
                imports: &imports.imports,
                edges: BTreeSet::new(),
            };
            checker.block(&parsed.function.body, &mut scope, Some(&expected))?;
            if scope.values.values().any(|binding| binding.ty.linear()) {
                return Err(err(
                    "ownership",
                    parsed.function.body.span,
                    "function leaves live quantum arguments unconsumed",
                ));
            }
            Ok(checker.edges)
        })();
        edges.insert(
            id,
            result
                .map_err(|e| e.in_module(module))?
                .into_iter()
                .map(|id| (id, Span::default()))
                .collect(),
        );
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
    Ok(())
}

struct Checker<'a> {
    program: &'a ParsedProgram,
    module: &'a str,
    function: &'a Function,
    definition: DefId,
    imports: &'a BTreeMap<String, Target>,
    edges: BTreeSet<DefId>,
}
impl Checker<'_> {
    fn effect(&self, effect: Effect, span: Span) -> Result<()> {
        if effect <= self.function.effect {
            Ok(())
        } else {
            Err(err(
                "effect",
                span,
                "declared effect is narrower than the called operation",
            ))
        }
    }
    fn resolve(&mut self, name: &str, scope: &Scope, span: Span) -> Result<Target> {
        if scope.shadows.contains(name)
            || scope.naturals.contains_key(name)
            || scope.operations.contains_key(name)
        {
            return Err(err(
                "name",
                span,
                format!("{name} is shadowed or is not a transparent function"),
            ));
        }
        let owner = self
            .program
            .resolution
            .module(self.module)
            .expect("known module");
        let target = self
            .program
            .resolution
            .local(owner, name)
            .map(Target::Declaration)
            .or_else(|| self.imports.get(name).copied())
            .ok_or_else(|| err("name", span, format!("unresolved function {name}")))?;
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
        let (_, f) = self.program.definition(id);
        if args.len() != f.parameters.len() {
            return Err(err("static", span, "wrong number of static arguments"));
        }
        let mut target = Scope {
            naturals: BTreeMap::new(),
            operations: BTreeMap::new(),
            context: scope.context.clone(),
            values: BTreeMap::new(),
            shadows: BTreeSet::new(),
            moved: BTreeSet::new(),
            next_binding: Rc::clone(&scope.next_binding),
        };
        for (p, a) in f.parameters.iter().zip(args) {
            if let Parameter::Natural(name) = p {
                let Argument::Natural(n) = a else {
                    return Err(err("static", span, "expected natural argument"));
                };
                target.naturals.insert(
                    name.clone(),
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
                target.operations.insert(name.clone(), op);
            }
        }
        call_capacity(requirements(f, &target, span), span)?;
        if recursion && id == self.definition {
            let mut decreases = false;
            for p in &f.parameters {
                if let Parameter::Natural(name) = p {
                    let old = &scope.naturals[name];
                    let new = &target.naturals[name];
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
            }) if scope.operations.contains_key(name) => {
                if scope.values.contains_key(name) {
                    return Err(err("name", span, "operation parameter is shadowed"));
                }
                Ok(scope.operations[name].clone())
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
        name: &str,
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
        let initial_shadows = scope.shadows.clone();
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
        scope.shadows = initial_shadows;
        Ok(result)
    }
    fn expr(&mut self, expr: &Expr, scope: &mut Scope, expected: Option<&Ty>) -> Result<Ty> {
        let span = expr.span;
        let result = match &expr.kind {
            ExprKind::Name(name) => {
                let binding = scope.values.get(name).cloned().ok_or_else(|| {
                    err(
                        "ownership",
                        span,
                        format!("unbound or consumed value {name}"),
                    )
                })?;
                if binding.ty.linear() {
                    scope.values.remove(name);
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
                if let Some(op) = scope.operations.get(name).cloned() {
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
                    let (inputs, result, effect) = match target {
                        Target::Primitive(_) => {
                            let primitive =
                                Primitive::lookup(&self.program.resolution.target_path(target))
                                    .expect("resolved primitive");
                            primitive_signature(primitive, args, scope, span)?
                        }
                        Target::Declaration(id) => self.specialize(id, args, scope, span, true)?,
                    };
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
                if scope.naturals.contains_key(index)
                    || scope.operations.contains_key(index)
                    || scope.shadows.contains(index)
                {
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
                let i = Linear::variable(index);
                inner.context = inner.context.push(&[
                    linear::at(start.sub(&i), span, "while checking fold bound")?,
                    linear::at(
                        i.add(&Linear::constant(1)).and_then(|n| n.sub(&end)),
                        span,
                        "while checking fold bound",
                    )?,
                    i.scale(-1)?,
                ]);
                inner.naturals.insert(index.clone(), i);
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
            Requirement::Access(kind, name, _) => access(
                scope
                    .operations
                    .get(name)
                    .ok_or_else(|| err("access", span, "missing operation argument"))?,
                kind,
                span,
            )?,
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
        signature
            .inputs
            .iter()
            .map(|t| shape(*t, &ns, span))
            .collect::<Result<_>>()?,
        shape(signature.output, &ns, span)?,
        signature.effect,
    ))
}

fn concrete_scope(f: &Function, naturals: &BTreeMap<String, u32>) -> Result<Scope> {
    let expected: BTreeSet<_> = f
        .parameters
        .iter()
        .filter_map(|p| {
            if let Parameter::Natural(n) = p {
                Some(n.clone())
            } else {
                None
            }
        })
        .collect();
    if naturals.keys().cloned().collect::<BTreeSet<_>>() != expected {
        return Err(err(
            "static",
            f.span,
            "concrete natural bindings must exactly match the declaration",
        ));
    }
    // Concrete entry sizes are diagnostic preparation data, not capacities of a
    // future runtime or coefficient domain. Keep construction bounded and small.
    let scope = Scope {
        naturals: naturals
            .iter()
            .map(|(name, n)| (name.clone(), Linear::constant(i128::from(*n))))
            .collect(),
        operations: BTreeMap::new(),
        context: Context::natural([])?,
        values: BTreeMap::new(),
        shadows: BTreeSet::new(),
        moved: BTreeSet::new(),
        next_binding: Rc::new(Cell::new(0)),
    };
    Ok(scope)
}
pub(super) fn instantiate(
    program: &ParsedProgram,
    entry: &str,
    naturals: &BTreeMap<String, u32>,
    operations: &BTreeMap<String, OperationBinding>,
) -> Result<(DefId, BTreeMap<String, DefId>)> {
    let (entry_id, module, f) = visible_definition(program, entry, None, Span::default())?;
    let result = (|| {
        let mut scope = concrete_scope(f, naturals)?;
        let mut provider_ids = BTreeMap::new();
        let expected: BTreeSet<_> = f
            .parameters
            .iter()
            .filter_map(|p| {
                if let Parameter::Operation(n, _) = p {
                    Some(n.clone())
                } else {
                    None
                }
            })
            .collect();
        if operations.keys().cloned().collect::<BTreeSet<_>>() != expected {
            return Err(err(
                "static",
                f.span,
                "concrete operation bindings must exactly match the declaration",
            ));
        }
        for p in &f.parameters {
            if let Parameter::Operation(name, b) = p {
                let binding = &operations[name];
                let (provider_id, _, provider) =
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
                provider_ids.insert(name.clone(), provider_id);
                let provider_scope = concrete_scope(provider, &binding.naturals)?;
                requirements(provider, &provider_scope, f.span)?;
                let output = ty(&provider.result, &provider_scope, provider.span)?;
                if provider.effect != Effect::Unitary
                    || provider.arguments.len() != 1
                    || !output.is_quantum_owner()
                {
                    return Err(err(
                        "type",
                        f.span,
                        "concrete provider must be a single-input quantum unitary",
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
                    name.clone(),
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
