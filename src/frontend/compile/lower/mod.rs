//! Source evaluation, lexical scopes, calls, and checked IR construction.
//!
//! Values and their ownership representation live in `value`; sealed operations
//! and classical branch merging have separate implementations. All of them use
//! the same complete register store and ID supply, including suspended callers.

mod branch;
mod certified;
mod classical;
mod function_contract;
mod operations;
mod primitives;
mod scope;
mod transforms;
mod value;

use value::{Binding, Env, Register, Slot, Value, env_size};

use super::*;
use crate::frontend::pattern::{self, BindingContext};
use crate::frontend::raw_state::RawState;
use crate::ir::*;
use std::borrow::Cow;

#[derive(Clone, Copy)]
enum CallArguments<'a> {
    Runtime(&'a [Expr]),
    Classical(&'a [BasisExpr]),
}
impl CallArguments<'_> {
    fn span(self, index: usize) -> Span {
        match self {
            Self::Runtime(args) => args[index].span,
            Self::Classical(args) => args[index].span,
        }
    }
}

#[derive(Clone, Copy)]
struct CallSite<'a> {
    module: &'a str,
    span: Span,
    args: CallArguments<'a>,
}

// Diagnostic metadata only: acceptance still depends solely on raw IR.
// Keys use the independent verifier's operation/branch-index path convention.
type OperationSources = BTreeMap<Vec<usize>, (String, Span)>;

struct TupleBindingOrigin {
    module: String,
    span: Span,
    name: String,
}

fn verification_error(
    compiler: &Compiler<'_>,
    sources: &OperationSources,
    module: &str,
    span: Span,
    failure: crate::interchange::Error,
    limit: bool,
) -> CompileError {
    // Optional post-rejection explanations retain source locations. They never
    // issue an acceptance decision or replace the native rejection category.
    let path: Vec<usize> = failure
        .json_pointer
        .split('/')
        .skip(2)
        .filter_map(|part| match part {
            "then_ops" => Some(0),
            "else_ops" => Some(1),
            _ => part.parse().ok(),
        })
        .collect();
    let (module, span) = (1..=path.len())
        .rev()
        .find_map(|length| sources.get(&path[..length]))
        .map_or((module, span), |(module, span)| (module.as_str(), *span));
    compiler.error(
        module,
        span,
        if limit {
            ErrorCode::Limit
        } else if matches!(failure.code, "io" | "kernel") {
            ErrorCode::Project
        } else {
            ErrorCode::InvalidIr
        },
        match &compiler.checking {
            Some(key) => format!(
                "{failure} while checking {}",
                compiler.resolution.path(*key)
            ),
            None => failure.to_string(),
        },
    )
}

// The register store includes quantum values held by pending arguments and
// suspended callers, not just bindings visible in the current lexical Env.
// Branches snapshot registers/effects, but never rewind the fresh ID supply.
// Every emitted program must still pass the independent IR verifier.
struct Lowerer<'c, 'p> {
    compiler: &'c mut Compiler<'p>,
    raw: RawState<std::convert::Infallible>,
    operation_sources: OperationSources,
    // Diagnostics only; never consulted by ownership, scope or IR checking.
    tuple_binding_origins: Vec<BTreeMap<String, Option<TupleBindingOrigin>>>,
    effect: Effect,
    // Origin of the strongest derived effect; diagnostic metadata only.
    effect_source: Option<(String, Span)>,
    depth: usize,
    bindings: super::operations::Bindings,
}

struct PatternBinding<'a, 'c, 'p> {
    lowerer: &'a mut Lowerer<'c, 'p>,
    module: &'a str,
    env: &'a mut Env,
}
impl BindingContext<Pattern> for PatternBinding<'_, '_, '_> {
    type Value = Value;
    type Size = std::convert::Infallible;
    type Error = CompileError;

    fn linear(&self, value: &Value) -> bool {
        value.owns_quantum()
    }

    fn pattern_type<'v>(&self, value: &'v Value) -> Cow<'v, Ty> {
        Cow::Owned(value.ty())
    }

    fn consume_fields(&mut self, value: Value) -> Vec<Value> {
        value.into_fields().expect("checked nonempty tuple shape")
    }

    fn bind_name(&mut self, name: &Ident, _span: Span, value: Value) -> Result<(), CompileError> {
        let binder = self.lowerer.compiler.locals.binder(name);
        if self
            .lowerer
            .compiler
            .locals
            .info(binder)
            .shadowed
            .and_then(|old| self.env.get(self.lowerer.compiler.locals.key(old)))
            .and_then(Binding::as_ref)
            .is_some_and(Value::owns_quantum)
        {
            return Err(self.lowerer.error(
                self.module,
                name.span,
                ErrorCode::Ownership,
                "binding would hide unconsumed quantum ownership",
            ));
        }
        if let Some(origins) = self.lowerer.tuple_binding_origins.last_mut() {
            // Names (including non-tuples) shadow outer diagnostic metadata.
            // No quantum slot/type tree is copied here.
            origins.insert(
                name.text.clone(),
                matches!(&value, Value::Pair(..) | Value::Tuple(_)).then(|| TupleBindingOrigin {
                    module: self.module.to_owned(),
                    span: name.span,
                    name: name.text.clone(),
                }),
            );
        }
        self.lowerer.bind_env(name, Binding::Live(value), self.env);
        Ok(())
    }

    fn wildcard_error(&self, span: Span) -> CompileError {
        self.lowerer.error(
            self.module,
            span,
            ErrorCode::Ownership,
            "wildcard would discard quantum ownership",
        )
    }

    fn duplicate_error(&self, span: Span) -> CompileError {
        self.lowerer.error(
            self.module,
            span,
            ErrorCode::Ownership,
            "duplicate name in a binding pattern",
        )
    }

    fn shape_error(&self, span: Span, arity: usize, value: &Value, actual: &Ty) -> CompileError {
        let help = if matches!(value, Value::Quantum(..)) {
            "; help: a quantum register is one owner; call `split` to obtain its immediate product fields, then split any nested register separately"
        } else {
            ""
        };
        self.lowerer.error(
            self.module,
            span,
            ErrorCode::TypeMismatch,
            if arity == 0 {
                format!("empty pattern requires ordinary Unit, found `{}`", actual.runtime())
            } else {
                format!("tuple pattern requires a tuple value with the same immediate arity: expected a tuple of {arity} immediate fields, found `{}`{help}", actual.runtime())
            },
        )
    }
}

impl Lowerer<'_, '_> {
    fn bind_env(&self, name: &Ident, value: Binding, env: &mut Env) {
        let id = self.compiler.locals.binder(name);
        if let Some(old) = self.compiler.locals.info(id).shadowed {
            env.remove(self.compiler.locals.key(old));
        }
        env.insert(self.compiler.locals.key(id).clone(), value);
    }

    fn add_effect(&mut self, module: &str, span: Span, effect: Effect) {
        if effect > self.effect {
            self.effect_source = Some((module.to_owned(), span));
        }
        self.effect = self.effect.max(effect);
    }

    fn error(
        &self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: impl Into<String>,
    ) -> CompileError {
        self.compiler.error(module, span, code, message)
    }
    fn token(&mut self) -> TokenId {
        self.raw.token()
    }
    fn wire(&mut self) -> WireId {
        self.raw.wire()
    }
    fn classical(&mut self) -> ClassicalId {
        self.raw.classical()
    }
    fn slot(&mut self) -> Slot {
        self.raw.slot()
    }

    fn register(&mut self, basis: Ty, wires: Vec<WireId>) -> Value {
        let slot = self.raw.register(basis.clone(), wires);
        Value::quantum(slot, basis)
    }

    fn input(
        &mut self,
        ty: &Ty,
        module: &str,
        span: Span,
        quantum: &mut Vec<QuantumPort>,
        classical: &mut Vec<ClassicalId>,
    ) -> Result<Value, CompileError> {
        Ok(match &ty.kind {
            Kind::Unit => Value::Unit,
            Kind::Bit => {
                let id = self.classical();
                classical.push(id);
                Value::Classical(id)
            }
            Kind::Q(basis) => {
                let wires = (0..basis.basis_bits().expect("basis type"))
                    .map(|_| self.wire())
                    .collect();
                let value = self.register((**basis).clone(), wires);
                let Value::Quantum(slot, _) = &value else {
                    unreachable!()
                };
                let reg = &self.raw.registers[slot];
                quantum.push(QuantumPort {
                    token: reg.token,
                    wires: reg.wires.clone(),
                    shape: BasisShape {
                        bits: self.compiler.narrow_u8(
                            module,
                            span,
                            reg.wires.len(),
                            "input width",
                        )?,
                    },
                });
                value
            }
            Kind::Tuple(fields) => Value::tuple(
                fields
                    .iter()
                    .map(|field| self.input(field, module, span, quantum, classical))
                    .collect::<Result<_, _>>()?,
            ),
            Kind::Bits(n) => match *n {},
            Kind::Parameter(_) => {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "unresolved Basis parameter in finite input",
                ));
            }
        })
    }

    fn call_user(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
    ) -> Result<Value, CompileError> {
        let decl = self.compiler.declarations[key];
        let key_name = self.compiler.resolution.declaration(*key).name.clone();
        if self.depth >= MAX_DEPTH {
            return Err(self.error(
                &key_name.0,
                decl.span,
                ErrorCode::Limit,
                "function expansion exceeds the initial depth limit",
            ));
        }
        self.depth += 1;
        // A callee's lexical binders cannot explain the caller's operands.
        let caller_origins = std::mem::take(&mut self.tuple_binding_origins);
        let result = self.call_user_inner(key, args, site);
        self.tuple_binding_origins = caller_origins;
        self.depth -= 1;
        result
    }

    fn call_user_inner(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
    ) -> Result<Value, CompileError> {
        let decl = self.compiler.declarations[key];
        let key_name = self.compiler.resolution.declaration(*key).name.clone();
        self.compiler.tick(&key_name.0, decl.span)?;
        let (params, return_ty) = self.compiler.signature(key)?;
        if decl.kind == FnKind::Meaning {
            return Err(self.error(
                &key_name.0,
                decl.span,
                ErrorCode::TypeMismatch,
                "Meaning declarations are not ordinary runtime callees",
            ));
        }
        if args.len() != params.len() {
            let (module, span) = site.map_or((key_name.0.as_str(), decl.span), |site| {
                (site.module, site.span)
            });
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "function argument count does not match",
            ));
        }
        let mut env = Env::new();
        let mut names = BTreeSet::new();
        for (index, ((param, ty), value)) in decl.params.iter().zip(params).zip(args).enumerate() {
            let (module, span) = site.map_or((key_name.0.as_str(), param.span), |site| {
                (site.module, site.args.span(index))
            });
            self.compiler
                .charge(module, span, value.tree_size().nodes)?;
            if value.ty() != ty {
                let argument = match &param.pattern.kind {
                    PatternKind::Name(name) => format!("argument `{}`", name.text),
                    _ => format!("argument {}", index + 1),
                };
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    format!(
                        "{argument} has the wrong type: expected `{}`, found `{}`",
                        ty.runtime(),
                        value.ty().runtime()
                    ),
                ));
            }
            self.bind(&key_name.0, &param.pattern, value, &mut env, &mut names)?;
        }
        let previous_effect = self.effect;
        let previous_effect_source = self.effect_source.take();
        self.effect = Effect::Unitary;
        let (value, result_span, body_span) = match &decl.body {
            FnBody::Quantum(body) => (
                self.block(&key_name.0, body, &mut env)?,
                body.result.span,
                body.span,
            ),
            FnBody::Basis(body) if decl.kind == FnKind::Classical => (
                self.classical_expr(&key_name.0, body, &mut env)?,
                body.span,
                body.span,
            ),
            _ => unreachable!("complete checked callable declaration"),
        };
        self.compiler
            .charge(&key_name.0, result_span, value.tree_size().nodes)?;
        if value.ty() != return_ty {
            return Err(self.error(
                &key_name.0,
                result_span,
                ErrorCode::TypeMismatch,
                format!(
                    "result does not match the function return type: expected `{}`, found `{}`",
                    return_ty.runtime(),
                    value.ty().runtime()
                ),
            ));
        }
        let mut pending: Vec<_> = decl.params.iter().rev().map(|p| &p.pattern).collect();
        let mut parameter_names = Vec::new();
        while let Some(pattern) = pending.pop() {
            match &pattern.kind {
                PatternKind::Name(name) => parameter_names.push(name),
                PatternKind::Tuple(fields) => pending.extend(fields.iter().rev()),
                PatternKind::Wildcard => {}
            }
        }
        self.no_owned_bindings(&key_name.0, body_span, &env, parameter_names)?;
        let inferred = self.effect;
        let Some(fact) = crate::frontend::effects::FunctionEffect::checked(decl.kind, inferred)
        else {
            let (module, span) = self
                .effect_source
                .as_ref()
                .map_or((key_name.0.as_str(), decl.span), |(module, span)| {
                    (module.as_str(), *span)
                });
            return Err(self.error(
                module,
                span,
                ErrorCode::Effect,
                crate::frontend::effects::assertion_error(&decl.name.text, decl.kind, inferred),
            ));
        };
        let source_fact = self.compiler.effects[key];
        if fact.inferred() > source_fact.inferred() {
            return Err(self.error(
                &key_name.0,
                result_span,
                ErrorCode::Effect,
                "concrete expansion exceeds the complete checked source effect",
            ));
        }
        self.effect = previous_effect;
        self.effect_source = previous_effect_source;
        let (module, span) = site.map_or((key_name.0.as_str(), decl.span), |site| {
            (site.module, site.span)
        });
        self.add_effect(module, span, inferred);
        Ok(value)
    }

    fn no_owned_bindings<'b>(
        &self,
        module: &str,
        fallback: Span,
        env: &Env,
        bindings: impl IntoIterator<Item = &'b Ident>,
    ) -> Result<(), CompileError> {
        if let Some((name, _)) = env
            .iter()
            .find(|(_, value)| value.as_ref().is_some_and(Value::owns_quantum))
        {
            let span = bindings
                .into_iter()
                .find(|binding| binding.text == name.name)
                .map_or(fallback, |binding| binding.span);
            Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                format!("quantum ownership `{name}` was not returned or explicitly consumed"),
            ))
        } else {
            Ok(())
        }
    }

    fn block(&mut self, module: &str, block: &Block, env: &mut Env) -> Result<Value, CompileError> {
        self.tuple_binding_origins.push(BTreeMap::new());
        let result = self.block_inner(module, block, env);
        self.tuple_binding_origins.pop();
        result
    }

    fn block_inner(
        &mut self,
        module: &str,
        block: &Block,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        self.compiler
            .charge(module, block.span, env_size(env).saturating_mul(2))?;
        let mut entry = env.clone();
        let mut local = env.clone();
        for stmt in &block.statements {
            self.compiler.tick(module, stmt.span)?;
            match &stmt.kind {
                // The shared judgment checked this compile-time binding.
                // It has no runtime value or owner in a finite body.
                StmtKind::StaticLet { .. } => {}
                StmtKind::Let { pattern, value } => {
                    let value = self.expr(module, value, &mut local)?;
                    let mut names = BTreeSet::new();
                    self.bind(module, pattern, value, &mut local, &mut names)?;
                }
                StmtKind::Expr(expr) => {
                    let value = self.expr(module, expr, &mut local)?;
                    if value.owns_quantum() {
                        return Err(self.error(
                            module,
                            stmt.span,
                            ErrorCode::Ownership,
                            "expression statement would discard quantum ownership",
                        ));
                    }
                }
            }
        }
        let result = self.expr(module, &block.result, &mut local)?;
        scope::close_scope(&mut entry, &local, &BTreeSet::new()).map_err(|name| {
            let span = self.compiler.locals.info(name.id).span;
            self.error(module, span, ErrorCode::Ownership, format!("local quantum ownership `{name}` escapes neither through the result nor an explicit discard"))
        })?;
        *env = entry;
        Ok(result)
    }

    fn bind(
        &mut self,
        module: &str,
        pattern: &Pattern,
        value: Value,
        env: &mut Env,
        names: &mut BTreeSet<String>,
    ) -> Result<(), CompileError> {
        pattern::bind(
            pattern,
            value,
            names,
            &mut PatternBinding {
                lowerer: self,
                module,
                env,
            },
        )
    }

    // Canonical direct power and inverse share the existing finite transform
    // path. A zero count still checks the real body before repeating its steps.
    fn named_transform(
        &mut self,
        module: &str,
        span: Span,
        function: &Ident,
        count: Option<u16>,
        input: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let value = self.expr(module, input, env)?;
        let slot = self.quantum(module, input.span, &value, false)?;
        let basis = self.raw.registers[&slot].basis.clone();
        let access = if count.is_none() {
            Access::Adjoint
        } else {
            Access::Apply
        };
        let operation = self.operation_steps(module, function, &basis, env, access)?;
        let is_operation = operation.is_some();
        let mut steps = match operation {
            Some(steps) => steps,
            None => self.static_steps(module, function, &basis, env)?,
        };
        let cost = total_size(steps.iter().map(super::circuit::size));
        let mut expected = self.target_meaning(module, function, &basis)?;
        match count {
            None => {
                self.compiler.charge(module, span, cost)?;
                if !is_operation {
                    super::circuit::invert(&mut steps);
                }
                expected = expected
                    .map(|m| m.adjoint(&mut self.compiler.exact_work))
                    .transpose()
                    .map_err(|e| self.compiler.op_error(module, span, e.into()))?;
            }
            Some(count) => {
                self.compiler.charge(
                    module,
                    span,
                    cost.saturating_add(1).saturating_mul(usize::from(count)),
                )?;
                if is_operation
                    && steps.len().saturating_mul(usize::from(count))
                        > crate::contract::MAX_CONTRACT_STEPS
                {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "operation repetition exceeds 1024 steps",
                    ));
                }
                // Bind one body to its independently extracted meaning.
                // Validate serial copies structurally, without constructing U^n.
                self.check_transformed(module, span, &basis, &steps, expected.as_ref())?;
                let body = steps;
                steps = (0..count).flat_map(|_| body.iter().cloned()).collect();
                transforms::check_repeated_steps(&body, &steps, count)
                    .map_err(|e| self.compiler.op_error(module, span, e))?;
                expected = None;
            }
        }
        self.check_transformed(module, span, &basis, &steps, expected.as_ref())?;
        self.apply_circuit(slot, steps);
        Ok(value)
    }

    fn expr(&mut self, module: &str, expr: &Expr, env: &mut Env) -> Result<Value, CompileError> {
        self.compiler.tick(module, expr.span)?;
        if self.depth >= MAX_DEPTH {
            return Err(self.error(
                module,
                expr.span,
                ErrorCode::Limit,
                "expression expansion exceeds the initial depth limit",
            ));
        }
        self.depth += 1;
        let first_operation = self.raw.operations.len();
        let result = self.expr_inner(module, expr, env);
        self.depth -= 1;
        let value = result?;
        // Nested expressions/callees already supplied more precise positions.
        // Fill only the operations emitted directly by this expression.
        for index in first_operation..self.raw.operations.len() {
            self.operation_sources
                .entry(vec![index])
                .or_insert_with(|| (module.to_owned(), expr.span));
        }
        // Values entering an environment are bounded before they can be reused.
        // Constructors combine only previously checked children, so even an
        // over-limit temporary adds at most one layer before being rejected.
        self.compiler
            .check_tree(module, expr.span, value.tree_size())?;
        Ok(value)
    }

    fn expr_inner(
        &mut self,
        module: &str,
        expr: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        match &expr.kind {
            ExprKind::StaticIf { .. } | ExprKind::StaticFold { .. } => Err(self.error(
                module,
                expr.span,
                ErrorCode::Unsupported,
                "expression is outside the finite lowering profile",
            )),
            ExprKind::Controlled { operation, args } => {
                self.controlled_application(module, expr.span, operation, args, env)
            }
            ExprKind::ApplyContract {
                implementation,
                specification,
                input,
            } => {
                let value = self.expr(module, input, env)?;
                self.apply_function_contract(
                    module,
                    expr.span,
                    implementation,
                    specification,
                    value,
                    env,
                )
            }
            ExprKind::ApplyStatic { operation, input } => {
                if let Some((function, count, count_span)) = named_literal_repetition(operation) {
                    let count = u16::try_from(count)
                        .ok()
                        .filter(|count| *count <= 4096)
                        .ok_or_else(|| {
                            self.error(
                                module,
                                count_span,
                                ErrorCode::Limit,
                                "static repetition exceeds the 4096-count limit",
                            )
                        })?;
                    return self.named_transform(
                        module,
                        expr.span,
                        function,
                        Some(count),
                        input,
                        env,
                    );
                }
                let value = self.expr(module, input, env)?;
                let slot = self.quantum(module, input.span, &value, false)?;
                let basis = self.raw.registers[&slot].basis.clone();
                let op = self.operation(module, operation, env)?;
                if op.basis != basis {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "operation and input have different exact basis trees",
                    ));
                }
                let steps = op.steps(module, expr.span, Access::Apply, self.compiler)?;
                self.check_transformed(module, expr.span, &basis, &steps, op.meaning.as_ref())?;
                self.apply_circuit(slot, steps);
                Ok(value)
            }
            ExprKind::Adjoint { operation, input }
                if !matches!(operation.kind, StaticOpKind::Name(_)) =>
            {
                self.constructed_inverse(module, expr.span, operation, input, env)
            }
            ExprKind::Adjoint { input, .. } | ExprKind::RepeatStatic { input, .. } => {
                let function = match &expr.kind {
                    ExprKind::Adjoint {
                        operation:
                            StaticOp {
                                kind: StaticOpKind::Name(name),
                                ..
                            },
                        ..
                    } => name,
                    ExprKind::RepeatStatic { function, .. } => function,
                    _ => {
                        return Err(self.error(
                            module,
                            expr.span,
                            ErrorCode::Unsupported,
                            "finite adjoint requires a function name",
                        ));
                    }
                };
                let count = match expr.kind {
                    ExprKind::RepeatStatic { count, .. } => Some(count),
                    _ => None,
                };
                self.named_transform(module, expr.span, function, count, input, env)
            }
            ExprKind::QuantumIf {
                control,
                target,
                zero,
                one,
            } => {
                let c = self.expr(module, control, env)?;
                self.quantum(module, control.span, &c, true)?;
                let q = self.expr(module, target, env)?;
                let slot = self.quantum(module, target.span, &q, false)?;
                let basis = self.raw.registers[&slot].basis.clone();
                let axes: Vec<_> = (1..=basis.basis_bits().expect("basis")).collect();
                let mut steps = Vec::new();
                let mut operation_arm = false;
                let mut expectations = Vec::new();
                for (name, when_one) in [(zero, false), (one, true)] {
                    let operation =
                        self.operation_steps(module, name, &basis, env, Access::Controlled)?;
                    let is_operation = operation.is_some();
                    operation_arm |= is_operation;
                    let mut arm = match operation {
                        Some(steps) => steps,
                        None => self.static_steps(module, name, &basis, env)?,
                    };
                    expectations.push(
                        if basis.basis_bits().expect("basis") < crate::contract::MAX_CONTRACT_BITS {
                            self.target_meaning(module, name, &basis)?
                        } else {
                            None
                        },
                    );
                    self.compiler.charge(
                        module,
                        expr.span,
                        total_size(arm.iter().map(super::circuit::size)).saturating_add(arm.len()),
                    )?;
                    for step in &mut arm {
                        if is_operation {
                            // The outer predicate is on axis zero. Nested controls
                            // retain their own polarity and shifted axes.
                            for control in &mut step.controls {
                                if control.index == 0 {
                                    control.when_one = when_one;
                                }
                            }
                        } else {
                            super::circuit::remap(step, &axes);
                            step.controls.push(BitControl { index: 0, when_one });
                        }
                    }
                    steps.extend(arm);
                }
                if operation_arm && steps.len() > crate::contract::MAX_CONTRACT_STEPS {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::Limit,
                        "controlled operation circuit exceeds 1024 steps",
                    ));
                }
                let one_meaning = expectations.pop().expect("one arm");
                let zero_meaning = expectations.pop().expect("zero arm");
                let expected = self.qif_meaning(module, expr.span, zero_meaning, one_meaning)?;
                self.check_transformed(
                    module,
                    expr.span,
                    &Ty::pair(Ty::bit(), basis),
                    &steps,
                    expected.as_ref(),
                )?;
                let joined = self.sealed(module, expr.span, "std::quantum", "join", vec![c, q])?;
                let slot = self.quantum(module, expr.span, &joined, false)?;
                self.apply_circuit(slot, steps);
                self.sealed(module, expr.span, "std::quantum", "split", vec![joined])
            }
            ExprKind::Unit => Ok(Value::Unit),
            ExprKind::Bit(_) | ExprKind::Not(_) | ExprKind::And(..) | ExprKind::Xor(..) => {
                use crate::frontend::ordinary::Boolean;
                let (operation, operands): (_, Vec<&Expr>) = match &expr.kind {
                    ExprKind::Bit(value) => (Boolean::Constant(*value), vec![]),
                    ExprKind::Not(input) => (Boolean::Not, vec![input]),
                    ExprKind::And(left, right) => (Boolean::And, vec![left, right]),
                    ExprKind::Xor(left, right) => (Boolean::Xor, vec![left, right]),
                    _ => unreachable!("matched Boolean source expression"),
                };
                self.boolean(
                    module,
                    expr.span,
                    operation,
                    operands.into_iter(),
                    env,
                    |lowerer, operand, env| lowerer.expr(module, operand, env),
                )
            }
            ExprKind::Name(name) => self.read_name(module, name, env),
            ExprKind::Tuple(fields) => Ok(Value::tuple(
                fields
                    .iter()
                    .map(|field| self.expr(module, field, env))
                    .collect::<Result<_, _>>()?,
            )),
            ExprKind::Call {
                callee,
                static_args,
                args,
            } => {
                // Keep legacy ordinary-call resolution and diagnostics. New
                // static calls resolve descriptions after runtime arguments.
                let legacy_target =
                    if static_args.is_empty() && self.bound_operation(callee).is_none() {
                        if self
                            .compiler
                            .locals
                            .local_key(callee)
                            .is_some_and(|key| env.contains_key(key))
                        {
                            return Err(self.error(
                                module,
                                callee.span,
                                ErrorCode::TypeMismatch,
                                "a local value is not callable",
                            ));
                        }
                        Some(self.compiler.resolve(module, callee)?)
                    } else {
                        None
                    };
                let values = args
                    .iter()
                    .map(|arg| self.expr(module, arg, env))
                    .collect::<Result<Vec<_>, _>>()?;
                self.static_name(module, callee, env)?;
                if self.bound_operation(callee).is_some() {
                    if !static_args.is_empty() || values.len() != 1 {
                        return Err(self.error(
                            module,
                            expr.span,
                            ErrorCode::Arity,
                            "operation application requires one quantum argument",
                        ));
                    }
                    let value = values.into_iter().next().expect("one argument");
                    let slot = self.quantum(module, expr.span, &value, false)?;
                    let basis = self.raw.registers[&slot].basis.clone();
                    let steps = self
                        .operation_steps(module, callee, &basis, env, Access::Apply)?
                        .expect("bound operation");
                    self.apply_circuit(slot, steps);
                    return Ok(value);
                }
                let site = CallSite {
                    module,
                    span: expr.span,
                    args: CallArguments::Runtime(args),
                };
                match legacy_target
                    .map(Ok)
                    .unwrap_or_else(|| self.compiler.resolve(module, callee))?
                {
                    Callee::User(key) => {
                        let bindings = self.bind_operations(&key, static_args, env, site)?;
                        self.call_bound(&key, values, Some(site), bindings)
                    }
                    Callee::Sealed(namespace, name) => {
                        if !static_args.is_empty() {
                            return Err(self.error(
                                module,
                                expr.span,
                                ErrorCode::Arity,
                                "sealed operations have no static parameters",
                            ));
                        }
                        self.sealed_with_source(module, expr.span, &namespace, &name, values, args)
                    }
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let value = self.expr(module, condition, env)?;
                let Value::Classical(condition) = value else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        format!(
                            "if requires a Bit condition: expected `Bit`, found `{}`",
                            value.ty().runtime()
                        ),
                    ));
                };
                self.branch(module, expr.span, condition, then_branch, else_branch, env)
            }
            ExprKind::CoherentLift {
                binder,
                input,
                basis,
            } => {
                let input = self.expr(module, input, env)?;
                self.lift(module, expr.span, binder, input, basis)
            }
            ExprKind::WithComputed {
                source,
                function,
                binder,
                body,
            } => {
                let source = self.expr(module, source, env)?;
                if self
                    .compiler
                    .locals
                    .local_key(function)
                    .is_some_and(|key| env.contains_key(key))
                    || self.bound_operation(function).is_some()
                {
                    return Err(self.error(
                        module,
                        function.span,
                        ErrorCode::TypeMismatch,
                        "with_computed requires a classical function name",
                    ));
                }
                self.computed(module, expr.span, source, function, binder, body, env)
            }
            ExprKind::CertifiedComputed {
                source,
                function,
                logical,
                data_binder,
                ancilla_binder,
                body,
            } => {
                let source = self.expr(module, source, env)?;
                self.certified_computed(
                    module,
                    expr.span,
                    source,
                    function,
                    logical,
                    data_binder,
                    ancilla_binder,
                    body,
                    env,
                )
            }
        }
    }

    fn apply_circuit(&mut self, slot: Slot, steps: Vec<CircuitStep>) {
        let output = self.token();
        let reg = self.raw.registers.get_mut(&slot).expect("owned register");
        self.raw.operations.push(RawOp::ApplyUnitary {
            input: reg.token,
            output,
            steps,
        });
        reg.token = output;
    }

    fn static_steps(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
        env: &Env,
    ) -> Result<Vec<CircuitStep>, CompileError> {
        if self
            .compiler
            .locals
            .local_key(name)
            .is_some_and(|key| env.contains_key(key))
            || self.bound_operation(name).is_some()
        {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static operation requires a function name, not a local value",
            ));
        }
        let target = self.compiler.resolve(module, name)?;
        let ty = Ty::quantum(basis.clone());
        match &target {
            Callee::User(key) => {
                if self.compiler.effects.get(key).map(|fact| fact.inferred())
                    != Some(Effect::Unitary)
                {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Effect,
                        crate::frontend::effects::unitary_required(
                            "static operation requires a function with inferred Unitary effect",
                        ),
                    ));
                }
                if !self.compiler.declarations[key].static_params.is_empty() {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Arity,
                        "static target requires a closed function",
                    ));
                }
                let (params, result) = self.compiler.signature(key)?;
                if params != [ty.clone()] || result != ty {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::TypeMismatch,
                        "static operation requires one Q<A> input and the same Q<A> result",
                    ));
                }
            }
            Callee::Sealed(namespace, gate) => {
                if namespace != "std::quantum"
                    || !matches!(
                        gate.as_str(),
                        "h" | "x" | "z" | "t" | "s" | "sdg" | "tdg" | "id" | "phase_eighth"
                    )
                {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Effect,
                        "static sealed operation requires a unary unitary quantum primitive",
                    ));
                }
                if !matches!(gate.as_str(), "id" | "phase_eighth") && *basis != Ty::bit() {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::TypeMismatch,
                        "sealed gate requires Q<Bit>",
                    ));
                }
            }
        }
        self.compiler
            .charge(module, name.span, ty.tree_size().nodes.saturating_mul(3))?;
        let mut inner = Lowerer {
            compiler: self.compiler,
            raw: RawState::new(),
            operation_sources: BTreeMap::new(),
            tuple_binding_origins: Vec::new(),
            effect: Effect::Unitary,
            effect_source: None,
            depth: self.depth,
            bindings: BTreeMap::new(),
        };
        let mut quantum_inputs = vec![];
        let mut classical_inputs = vec![];
        let arg = inner.input(
            &ty,
            module,
            name.span,
            &mut quantum_inputs,
            &mut classical_inputs,
        )?;
        let result = match target {
            Callee::User(key) => inner.call_bound(&key, vec![arg], None, BTreeMap::new())?,
            Callee::Sealed(namespace, gate) => {
                inner.sealed(module, name.span, &namespace, &gate, vec![arg])?
            }
        };
        let slot = inner.quantum(module, name.span, &result, false)?;
        let raw = RawProgram {
            quantum_inputs,
            classical_inputs,
            operations: inner.raw.operations,
            quantum_outputs: vec![inner.raw.registers[&slot].token],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let checked = inner
            .compiler
            .kernel
            .accept_raw_with_budget(raw, &mut inner.compiler.exact_work)
            .map_err(|err| {
                let limit = err.code == "limit";
                verification_error(
                    inner.compiler,
                    &inner.operation_sources,
                    module,
                    name.span,
                    err,
                    limit,
                )
            })?;
        super::circuit::flatten(inner.compiler, module, name.span, &checked)
    }

    fn lift(
        &mut self,
        module: &str,
        span: Span,
        binder: &Pattern,
        input: Value,
        basis: &BasisExpr,
    ) -> Result<Value, CompileError> {
        let slot = self.quantum(module, span, &input, false)?;
        self.compiler
            .charge(module, span, self.raw.registers[&slot].size())?;
        let reg = self.raw.registers[&slot].clone();
        let mut result_ty = None;
        let mut table = Vec::new();
        let mut seen = BTreeSet::new();
        for label in 0..(1u16 << reg.wires.len()) {
            let env = self
                .compiler
                .bind_basis_pattern(module, binder, &reg.basis, label)?;
            let value = self.compiler.eval_basis(module, basis, &env, 0)?;
            if result_ty.as_ref().is_some_and(|ty| *ty != value.ty) {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "basis lift result type varies",
                ));
            }
            result_ty = Some(value.ty);
            if !seen.insert(value.label) {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "coherent basis lift is not injective",
                ));
            }
            table.push(value.label);
        }
        let basis = result_ty.expect("nonempty domain");
        self.compiler
            .charge(module, span, basis.tree_size().nodes)?;
        let bits = basis.basis_bits().expect("basis result");
        if bits < reg.wires.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "basis lift cannot shrink its domain",
            ));
        }
        let mut wires = reg.wires.clone();
        wires.extend((reg.wires.len()..bits).map(|_| self.wire()));
        let output = self.token();
        self.raw.operations.push(RawOp::LiftBasis {
            input: reg.token,
            output,
            output_wires: wires.clone(),
            table,
        });
        self.raw.registers.insert(
            slot,
            Register {
                token: output,
                wires,
                basis: basis.clone(),
            },
        );
        if bits > reg.wires.len() {
            self.add_effect(module, span, Effect::Iso);
        }
        Ok(Value::quantum(slot, basis))
    }

    #[allow(clippy::too_many_arguments)]
    fn computed(
        &mut self,
        module: &str,
        span: Span,
        source: Value,
        function: &Ident,
        binder: &Ident,
        body: &Block,
        env: &Env,
    ) -> Result<Value, CompileError> {
        let source_slot = self.quantum(module, span, &source, false)?;
        let Callee::User(key) = self.compiler.resolve(module, function)? else {
            return Err(self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a classical function",
            ));
        };
        let predicate = self.compiler.basis.get(&key).ok_or_else(|| {
            self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a classical function",
            )
        })?;
        let size = predicate
            .signature_size()
            .saturating_add(predicate.table.len());
        self.compiler.charge(module, function.span, size)?;
        let predicate = self.compiler.basis[&key].clone();
        self.compiler.check_predicate_domain(
            module,
            function.span,
            &predicate,
            &self.raw.registers[&source_slot].basis,
        )?;
        let wire = self.wire();
        let ancilla = self.register(Ty::bit(), vec![wire]);
        let ancilla_slot = self.quantum(module, span, &ancilla, true)?;
        let initial_token = self.raw.registers[&ancilla_slot].token;
        // This first source form exposes only the ancilla and classical outer
        // values. Other quantum registers remain in the surrounding frame.
        self.compiler.charge(module, body.span, env_size(env))?;
        let mut local: Env = env
            .iter()
            .map(|(name, binding)| {
                let visible = if binding.as_ref().is_some_and(Value::owns_quantum) {
                    binding.hidden()
                } else {
                    binding.clone()
                };
                (name.clone(), visible)
            })
            .collect();
        self.bind_env(binder, Binding::Live(ancilla), &mut local);
        let start = self.raw.operations.len();
        let previous_effect = self.effect;
        let previous_effect_source = self.effect_source.take();
        self.effect = Effect::Unitary;
        let result = self.block(module, body, &mut local)?;
        self.no_owned_bindings(module, body.span, &local, [binder])?;
        if self.effect != Effect::Unitary {
            return Err(self.error(
                module,
                body.span,
                ErrorCode::Effect,
                "with_computed body must be unitary",
            ));
        }
        self.effect = previous_effect;
        self.effect_source = previous_effect_source;
        if result != Value::quantum(ancilla_slot, Ty::bit()) {
            return Err(self.error(
                module,
                body.span,
                ErrorCode::Ownership,
                "with_computed must return its ancilla ownership",
            ));
        }
        let mut expected_input = initial_token;
        let mut use_ops = Vec::new();
        for operation in &self.raw.operations[start..] {
            match operation {
                RawOp::Gate { gate, input, output } if matches!(gate, SingleGate::Z | SingleGate::T) && *input == expected_input => {
                    use_ops.push(ProtectedUse::ProtectedGate { bit: ProtectedBit { region: ProtectedRegion::Ancilla, index: 0 }, gate: *gate });
                    expected_input = *output;
                }
                _ => return Err(self.error(module, body.span, ErrorCode::Unsupported, "with_computed currently accepts only identity and expanded Z/T gates on its ancilla; for other unitary bodies, use with_computed(source, predicate, logical) { |data, ancilla| ... } and return both owners. The logical operation must satisfy the exact computed-relation contract; adding it does not bypass cleanup checking")),
            }
        }
        self.raw.operations.truncate(start);
        // The temporary gates become one protected operation below; their old
        // operation paths must not label this operation or a later expression.
        self.operation_sources.split_off(&vec![start]);
        let ancilla = self
            .raw
            .registers
            .remove(&ancilla_slot)
            .expect("returned ancilla");
        if ancilla.token != expected_input {
            return Err(self.error(
                module,
                body.span,
                ErrorCode::InvalidIr,
                "ancilla transition does not match its protected gates",
            ));
        }
        let output = self.token();
        let source_reg = self
            .raw
            .registers
            .get_mut(&source_slot)
            .expect("protected source");
        self.raw.operations.push(RawOp::ComputeUseUncompute {
            source: source_reg.token,
            source_out: output,
            targets: vec![],
            ancilla_wires: vec![wire],
            function: predicate.table,
            use_ops,
        });
        source_reg.token = output;
        Ok(source)
    }
}

pub(super) fn lower_function(
    compiler: &mut Compiler<'_>,
    key: &Key,
) -> Result<AcceptedProgram, CompileError> {
    lower_function_inner(compiler, key, BTreeMap::new())
}

fn lower_function_inner(
    compiler: &mut Compiler<'_>,
    key: &Key,
    bindings: super::operations::Bindings,
) -> Result<AcceptedProgram, CompileError> {
    let decl = compiler.declarations[key];
    let key_name = compiler.resolution.declaration(*key).name.clone();
    let (params, _) = compiler.signature(key)?;
    let mut lower = Lowerer {
        compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        tuple_binding_origins: Vec::new(),
        effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings,
    };
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    // Signature types are already bounded; account for constructing their
    // value tree and the register's copy of each quantum basis type.
    lower.compiler.charge(
        &key_name.0,
        decl.span,
        total_size(params.iter().map(|ty| ty.tree_size().nodes)).saturating_mul(2),
    )?;
    let args = params
        .iter()
        .map(|ty| {
            lower.input(
                ty,
                &key_name.0,
                decl.span,
                &mut quantum_inputs,
                &mut classical_inputs,
            )
        })
        .collect::<Result<_, _>>()?;
    let result = lower.call_user(key, args, None)?;
    let mut quantum_outputs = Vec::new();
    let mut classical_outputs = Vec::new();
    fn outputs(
        value: &Value,
        registers: &BTreeMap<Slot, Register>,
        quantum: &mut Vec<TokenId>,
        classical: &mut Vec<ClassicalId>,
    ) {
        match value {
            Value::Quantum(slot, _) => quantum.push(registers[slot].token),
            Value::Classical(id) => classical.push(*id),
            Value::Pair(a, b) => {
                outputs(a, registers, quantum, classical);
                outputs(b, registers, quantum, classical);
            }
            Value::Tuple(fields) => {
                for field in fields {
                    outputs(field, registers, quantum, classical);
                }
            }
            Value::Unit => {}
        }
    }
    outputs(
        &result,
        &lower.raw.registers,
        &mut quantum_outputs,
        &mut classical_outputs,
    );
    let raw = RawProgram {
        quantum_inputs,
        classical_inputs,
        operations: lower.raw.operations,
        quantum_outputs,
        classical_outputs,
        declared_effect: lower.effect,
    };
    lower
        .compiler
        .kernel
        .accept_raw_with_budget(raw, &mut lower.compiler.exact_work)
        .map_err(|failure| {
            let limit = failure.code == "limit";
            verification_error(
                lower.compiler,
                &lower.operation_sources,
                &key_name.0,
                decl.span,
                failure,
                limit,
            )
        })
}
