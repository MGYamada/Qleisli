//! Generic preparation checks. No value here crosses the verified IR boundary.
use super::ast::*;
use super::linear::{self, Context, Linear};
use super::{Error, OperationBinding, ParsedProgram, Result, Span};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Bit,
    Bits(Linear),
    CBit,
    CBits(Linear),
    Tuple(Vec<Ty>),
}
impl Ty {
    fn cells(&self) -> usize {
        1 + match self {
            Self::Tuple(fields) => fields.iter().map(Self::cells).sum(),
            _ => 0,
        }
    }
    fn depth(&self) -> usize {
        1 + match self {
            Self::Tuple(fields) => fields.iter().map(Self::depth).max().unwrap_or(0),
            _ => 0,
        }
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
    fn linear(&self) -> bool {
        match self {
            Self::Bit | Self::Bits(_) => true,
            Self::Tuple(xs) => xs.iter().any(Self::linear),
            _ => false,
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
fn all_access() -> BTreeSet<String> {
    ["Apply", "Adjoint", "Controlled"].map(String::from).into()
}
fn basis(b: &Basis, scope: &Scope) -> Result<Ty> {
    Ok(match b {
        Basis::Bit => Ty::Bit,
        Basis::Bits(n) => Ty::Bits(linear::natural(n, &scope.naturals, &scope.context)?),
    })
}
fn ty(t: &Type, scope: &Scope) -> Result<Ty> {
    let result = match t {
        Type::Quantum(b) => basis(b, scope)?,
        Type::CBit => Ty::CBit,
        Type::CBits(n) => Ty::CBits(linear::natural(n, &scope.naturals, &scope.context)?),
        Type::Tuple(xs) => Ty::Tuple(xs.iter().map(|x| ty(x, scope)).collect::<Result<_>>()?),
    };
    result.bounded(Span::default())?;
    Ok(result)
}
fn equivalent(a: &Ty, b: &Ty, context: &Context) -> Result<bool> {
    Ok(match (a, b) {
        (Ty::Bit, Ty::Bit) | (Ty::CBit, Ty::CBit) => true,
        (Ty::Bits(a), Ty::Bits(b)) | (Ty::CBits(a), Ty::CBits(b)) => {
            context.proves_le(a, b)? && context.proves_le(b, a)?
        }
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
            let mut equal = true;
            for (a, b) in a.iter().zip(b) {
                equal &= equivalent(a, b, context)?;
            }
            equal
        }
        _ => false,
    })
}
fn expect(actual: &Ty, expected: &Ty, context: &Context, span: Span) -> Result<()> {
    if equivalent(actual, expected, context)? {
        Ok(())
    } else {
        Err(err(
            "type",
            span,
            format!("type or tuple/size shape mismatch: expected {expected:?}, found {actual:?}"),
        ))
    }
}
fn prove(context: &Context, a: &Linear, b: &Linear, span: Span, message: &str) -> Result<()> {
    if context.proves_le(a, b)? {
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
    if !scope.context.feasible()? {
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
        bind_name(name, ty(t, &scope)?, *span, &mut scope)?;
    }
    let _ = ty(&f.result, &scope)?;
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
        match (pattern, t) {
            (Pattern::Name(name, span), t) => {
                if !names.insert(name.clone()) {
                    return Err(err("name", *span, "duplicate name in binding pattern"));
                }
                bind_name(name, t, *span, scope)
            }
            (Pattern::Tuple(patterns, span), Ty::Tuple(fields))
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
fn definition<'a>(
    program: &'a ParsedProgram,
    path: &str,
    span: Span,
) -> Result<(&'a str, &'a Function)> {
    let (module, name) = path
        .rsplit_once("::")
        .ok_or_else(|| err("module", span, "definition path needs module::function"))?;
    let (module, parsed) = program.modules.get_key_value(module).ok_or_else(|| {
        err(
            "module",
            span,
            format!("missing dependency module {module}"),
        )
    })?;
    if parsed.function.name != name {
        return Err(err("name", span, format!("no function {path}")));
    }
    Ok((module, &parsed.function))
}
fn primitive(path: &str) -> Option<&str> {
    match path {
        "std::quantum::h"
        | "std::quantum::x"
        | "std::quantum::cnot"
        | "std::quantum::phase"
        | "std::quantum::controlled_phase"
        | "std::quantum::init0"
        | "std::observe::measure_z"
        | "std::registers::take_bit"
        | "std::registers::put_bit"
        | "std::registers::empty"
        | "std::registers::consume_empty"
        | "std::classical::empty_bits"
        | "std::classical::prepend_bit" => path.rsplit("::").next(),
        _ => None,
    }
}
fn imports(program: &ParsedProgram, module: &str) -> Result<BTreeMap<String, String>> {
    let source = &program.modules[module];
    let mut result = BTreeMap::new();
    for (path, span) in &source.imports {
        if primitive(path).is_none() {
            let (owner, f) = definition(program, path, *span)?;
            if owner != module && !f.public {
                return Err(err(
                    "visibility",
                    *span,
                    format!("dependency {path} is private"),
                ));
            }
        }
        let name = path.rsplit("::").next().unwrap();
        if name == source.function.name && path != &format!("{module}::{name}") {
            return Err(err("name", *span, "import shadows the local function"));
        }
        if result.insert(name.into(), path.clone()).is_some() {
            return Err(err(
                "name",
                *span,
                format!("ambiguous imported name {name}"),
            ));
        }
    }
    result
        .entry(source.function.name.clone())
        .or_insert_with(|| format!("{module}::{}", source.function.name));
    Ok(result)
}

pub(super) fn program(program: &ParsedProgram) -> Result<()> {
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (module, parsed) in &program.modules {
        let result = (|| {
            let names = imports(program, module)?;
            let mut scope = declaration(&parsed.function)?;
            let expected = ty(&parsed.function.result, &scope)?;
            let mut checker = Checker {
                program,
                module,
                function: &parsed.function,
                imports: names,
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
        edges.insert(module.clone(), result.map_err(|e| e.in_module(module))?);
    }
    fn visit(
        node: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        active: &mut BTreeSet<String>,
        done: &mut BTreeSet<String>,
    ) -> Result<()> {
        if done.contains(node) {
            return Ok(());
        }
        if !active.insert(node.into()) {
            return Err(err(
                "cycle",
                Span::default(),
                "mutually recursive dependency cycle is unsupported",
            )
            .in_module(node));
        }
        for next in &edges[node] {
            if next != node {
                visit(next, edges, active, done)?;
            }
        }
        active.remove(node);
        done.insert(node.into());
        Ok(())
    }
    let mut done = BTreeSet::new();
    for name in edges.keys() {
        visit(name, &edges, &mut BTreeSet::new(), &mut done)?;
    }
    Ok(())
}
struct Checker<'a> {
    program: &'a ParsedProgram,
    module: &'a str,
    function: &'a Function,
    imports: BTreeMap<String, String>,
    edges: BTreeSet<String>,
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
    fn resolve(&mut self, name: &str, scope: &Scope, span: Span) -> Result<String> {
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
        let path = self
            .imports
            .get(name)
            .cloned()
            .ok_or_else(|| err("name", span, format!("unresolved function {name}")))?;
        if primitive(&path).is_none() {
            self.edges
                .insert(definition(self.program, &path, span)?.0.into());
        }
        Ok(path)
    }
    fn specialize(
        &mut self,
        path: &str,
        args: &[Argument],
        scope: &Scope,
        span: Span,
        recursion: bool,
    ) -> Result<(Vec<Ty>, Ty, Effect)> {
        let (_, f) = definition(self.program, path, span)?;
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
                expect(&op.ty, &basis(b, &target)?, &scope.context, span)?;
                target.operations.insert(name.clone(), op);
            }
        }
        requirements(f, &target, span)?;
        if recursion && path == format!("{}::{}", self.module, self.function.name) {
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
                    decreases |= scope
                        .context
                        .proves_le(&new.add(&Linear::constant(1))?, old)?;
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
                .map(|(_, t, _)| ty(t, &target))
                .collect::<Result<_>>()?,
            ty(&f.result, &target)?,
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
        let path = self.resolve(name, scope, span)?;
        if primitive(&path).is_some() {
            return Err(err(
                "unsupported",
                span,
                "primitive operation references are outside this preparation profile",
            ));
        }
        let (inputs, result, effect) = self.specialize(&path, args, scope, span, true)?;
        if effect != Effect::Unitary
            || inputs.len() != 1
            || !matches!(result, Ty::Bit | Ty::Bits(_))
        {
            return Err(err(
                "type",
                span,
                "operation provider must be unitary with one quantum input and identical output",
            ));
        }
        expect(&inputs[0], &result, &scope.context, span)?;
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
                let types = match expected {
                    Some(Ty::Tuple(ts)) if ts.len() == fields.len() => Some(ts),
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
                Ty::Tuple(result)
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
                    let path = self.resolve(name, scope, span)?;
                    let (inputs, result, effect) = if let Some(name) = primitive(&path) {
                        primitive_signature(name, args, scope, span)?
                    } else {
                        self.specialize(&path, args, scope, span, true)?
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
                self.expr(&inputs[0], scope, Some(&Ty::Bit))?;
                self.expr(&inputs[1], scope, Some(&op.ty))?;
                Ty::Tuple(vec![Ty::Bit, op.ty])
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
                    start.sub(&i)?,
                    i.add(&Linear::constant(1))?.sub(&end)?,
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
                if counterexample.feasible()? {
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
    name: &str,
    args: &[Argument],
    scope: &Scope,
    span: Span,
) -> Result<(Vec<Ty>, Ty, Effect)> {
    let arity = match name {
        "phase" | "controlled_phase" | "take_bit" | "put_bit" => 2,
        "prepend_bit" => 1,
        _ => 0,
    };
    if args.len() != arity {
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
    let unitary = Effect::Unitary;
    Ok(match name {
        "h" | "x" | "phase" => (vec![Ty::Bit], Ty::Bit, unitary),
        "cnot" | "controlled_phase" => (
            vec![Ty::Bit, Ty::Bit],
            Ty::Tuple(vec![Ty::Bit, Ty::Bit]),
            unitary,
        ),
        "take_bit" | "put_bit" => {
            let n = &ns[0];
            let k = &ns[1];
            prove(
                &scope.context,
                &k.add(&Linear::constant(1))?,
                n,
                span,
                "register index needs k < n",
            )?;
            let rest = Ty::Bits(n.sub(&Linear::constant(1))?);
            if name == "take_bit" {
                (
                    vec![Ty::Bits(n.clone())],
                    Ty::Tuple(vec![Ty::Bit, rest]),
                    unitary,
                )
            } else {
                (vec![Ty::Bit, rest], Ty::Bits(n.clone()), unitary)
            }
        }
        "empty" => (vec![], Ty::Bits(Linear::constant(0)), unitary),
        "consume_empty" => (
            vec![Ty::Bits(Linear::constant(0))],
            Ty::Tuple(vec![]),
            unitary,
        ),
        "init0" => (vec![], Ty::Bit, Effect::Iso),
        "measure_z" => (vec![Ty::Bit], Ty::CBit, Effect::Observe),
        "empty_bits" => (vec![], Ty::CBits(Linear::constant(0)), unitary),
        "prepend_bit" => (
            vec![Ty::CBit, Ty::CBits(ns[0].clone())],
            Ty::CBits(ns[0].add(&Linear::constant(1))?),
            unitary,
        ),
        _ => return Err(err("unsupported", span, "unsupported primitive")),
    })
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
) -> Result<()> {
    let (module, f) = definition(program, entry, Span::default())?;
    let result = (|| {
        let mut scope = concrete_scope(f, naturals)?;
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
                let (_, provider) = definition(program, &binding.definition, f.span)?;
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
                let provider_scope = concrete_scope(provider, &binding.naturals)?;
                requirements(provider, &provider_scope, f.span)?;
                let output = ty(&provider.result, &provider_scope)?;
                if provider.effect != Effect::Unitary
                    || provider.arguments.len() != 1
                    || !matches!(output, Ty::Bit | Ty::Bits(_))
                {
                    return Err(err(
                        "type",
                        f.span,
                        "concrete provider must be a single-input quantum unitary",
                    ));
                }
                expect(
                    &ty(&provider.arguments[0].1, &provider_scope)?,
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
            let _ = ty(t, &scope)?;
        }
        let _ = ty(&f.result, &scope)?;
        Ok(())
    })();
    result.map_err(|e| e.in_module(module))
}
