//! Source evaluation, lexical scopes, calls, and checked IR construction.
//!
//! Values and their ownership representation live in `value`; sealed operations
//! and classical branch merging have separate implementations. All of them use
//! the same complete register store and ID supply, including suspended callers.

mod branch;
mod certified;
mod function_contract;
mod operations;
pub(super) use operations::check_generic;
mod primitives;
mod scope;
mod transforms;
mod value;

use value::{Binding, Env, Register, Slot, Value, env_size};

use super::*;
use crate::ir::*;

#[derive(Clone, Copy)]
struct CallSite<'a> {
    module: &'a str,
    span: Span,
    args: &'a [Expr],
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
            Some(key) => format!("{failure} while checking {}::{}", key.0, key.1),
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
    registers: BTreeMap<Slot, Register>,
    operations: Vec<RawOp>,
    operation_sources: OperationSources,
    // Diagnostics only; never consulted by ownership, scope or IR checking.
    tuple_binding_origins: Vec<BTreeMap<String, Option<TupleBindingOrigin>>>,
    next_token: u32,
    next_wire: u32,
    next_classical: u32,
    next_slot: u32,
    effect: Effect,
    // Origin of the strongest derived effect; diagnostic metadata only.
    effect_source: Option<(String, Span)>,
    depth: usize,
    bindings: super::operations::Bindings,
    abstract_check: bool,
}

impl Lowerer<'_, '_> {
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
        let id = TokenId(self.next_token);
        self.next_token += 1;
        id
    }
    fn wire(&mut self) -> WireId {
        let id = WireId(self.next_wire);
        self.next_wire += 1;
        id
    }
    fn classical(&mut self) -> ClassicalId {
        let id = ClassicalId(self.next_classical);
        self.next_classical += 1;
        id
    }
    fn slot(&mut self) -> Slot {
        let id = self.next_slot;
        self.next_slot += 1;
        id
    }

    fn register(&mut self, basis: Ty, wires: Vec<WireId>) -> Value {
        let slot = self.slot();
        let token = self.token();
        self.registers.insert(
            slot,
            Register {
                token,
                wires,
                basis: basis.clone(),
            },
        );
        Value::Quantum(slot, basis)
    }

    fn input(
        &mut self,
        ty: &Ty,
        module: &str,
        span: Span,
        quantum: &mut Vec<QuantumPort>,
        classical: &mut Vec<ClassicalId>,
    ) -> Result<Value, CompileError> {
        Ok(match ty {
            Ty::Unit => Value::Unit,
            Ty::CBit => {
                let id = self.classical();
                classical.push(id);
                Value::Classical(id)
            }
            Ty::Q(basis) => {
                let wires = (0..basis.basis_bits().expect("basis type"))
                    .map(|_| self.wire())
                    .collect();
                let value = self.register((**basis).clone(), wires);
                let Value::Quantum(slot, _) = &value else {
                    unreachable!()
                };
                let reg = &self.registers[slot];
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
            Ty::Pair(a, b) => {
                let a = self.input(a, module, span, quantum, classical)?;
                let b = self.input(b, module, span, quantum, classical)?;
                Value::pair(a, b)
            }
            Ty::Tuple(fields) => Value::Tuple(
                fields
                    .iter()
                    .map(|field| self.input(field, module, span, quantum, classical))
                    .collect::<Result<_, _>>()?,
            ),
            Ty::Bit => unreachable!("ordinary signature"),
        })
    }

    fn call_user(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
    ) -> Result<Value, CompileError> {
        let decl = self.compiler.declarations[key];
        if self.depth >= MAX_DEPTH {
            return Err(self.error(
                &key.0,
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
        self.compiler.tick(&key.0, decl.span)?;
        let (params, return_ty) = self.compiler.signature(key)?;
        if matches!(decl.kind, FnKind::Basis | FnKind::Meaning) {
            return Err(self.error(
                &key.0,
                decl.span,
                ErrorCode::TypeMismatch,
                "basis functions are used only in basis expressions and with_computed",
            ));
        }
        if args.len() != params.len() {
            let (module, span) =
                site.map_or((key.0.as_str(), decl.span), |site| (site.module, site.span));
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                "function argument count does not match",
            ));
        }
        let mut env = Env::new();
        for (index, ((param, ty), value)) in decl.params.iter().zip(params).zip(args).enumerate() {
            let PatternKind::Name(name) = &param.pattern.kind else {
                unreachable!("ordinary parameters are parsed as names")
            };
            let (module, span) = site.map_or((key.0.as_str(), param.span), |site| {
                (site.module, site.args[index].span)
            });
            self.compiler
                .charge(module, span, value.tree_size().nodes)?;
            if value.ty() != ty {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    format!(
                        "argument `{}` has the wrong type: expected `{ty}`, found `{}`",
                        name.text,
                        value.ty()
                    ),
                ));
            }
            env.insert(name.text.clone(), Binding::Live(value));
        }
        let previous_effect = self.effect;
        let previous_effect_source = self.effect_source.take();
        self.effect = Effect::Unitary;
        let FnBody::Quantum(body) = &decl.body else {
            unreachable!("ordinary function")
        };
        let value = self.block(&key.0, body, &mut env)?;
        self.compiler
            .charge(&key.0, body.result.span, value.tree_size().nodes)?;
        if value.ty() != return_ty {
            return Err(self.error(
                &key.0,
                body.result.span,
                ErrorCode::TypeMismatch,
                format!("result does not match the function return type: expected `{return_ty}`, found `{}`", value.ty()),
            ));
        }
        self.no_owned_bindings(
            &key.0,
            body.span,
            &env,
            decl.params.iter().filter_map(|param| {
                if let PatternKind::Name(name) = &param.pattern.kind {
                    Some(name)
                } else {
                    None
                }
            }),
        )?;
        if self.effect > effect(decl.kind) {
            let (module, span) = self
                .effect_source
                .as_ref()
                .map_or((key.0.as_str(), decl.span), |(module, span)| {
                    (module.as_str(), *span)
                });
            return Err(self.error(
                module,
                span,
                ErrorCode::Effect,
                format!(
                    "body effect `{:?}` exceeds declared `{:?}` effect of `{}`",
                    self.effect,
                    effect(decl.kind),
                    decl.name.text
                ),
            ));
        }
        self.effect = previous_effect;
        self.effect_source = previous_effect_source;
        let (module, span) =
            site.map_or((key.0.as_str(), decl.span), |site| (site.module, site.span));
        self.add_effect(module, span, effect(decl.kind));
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
                .find(|binding| binding.text == *name)
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
        let mut rebound = BTreeSet::new();
        for stmt in &block.statements {
            self.compiler.tick(module, stmt.span)?;
            match &stmt.kind {
                StmtKind::Let { pattern, value } => {
                    let value = self.expr(module, value, &mut local)?;
                    let mut names = BTreeSet::new();
                    self.bind(module, pattern, value, &mut local, &mut names)?;
                    rebound.extend(names);
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
        scope::close_scope(&mut entry, &local, &rebound).map_err(|name| {
            // A direct rebinding supersedes an earlier binder of the same name.
            // Nested scopes diagnose their own locals before returning here.
            let span = block.statements.iter().rev().find_map(|stmt| {
                if let StmtKind::Let { pattern, .. } = &stmt.kind {
                    scope::binding_span(pattern, name)
                } else { None }
            }).unwrap_or(block.span);
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
        match &pattern.kind {
            PatternKind::Wildcard => {
                if value.owns_quantum() {
                    return Err(self.error(
                        module,
                        pattern.span,
                        ErrorCode::Ownership,
                        "wildcard would discard quantum ownership",
                    ));
                }
            }
            PatternKind::Name(name) => {
                if !names.insert(name.text.clone()) {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Ownership,
                        "duplicate name in a binding pattern",
                    ));
                }
                if env
                    .get(&name.text)
                    .and_then(Binding::as_ref)
                    .is_some_and(Value::owns_quantum)
                {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Ownership,
                        "binding would hide unconsumed quantum ownership",
                    ));
                }
                if let Some(origins) = self.tuple_binding_origins.last_mut() {
                    // Names (including non-tuples) shadow outer diagnostic
                    // metadata. No quantum slot/type tree is copied here.
                    origins.insert(
                        name.text.clone(),
                        matches!(&value, Value::Pair(..) | Value::Tuple(_)).then(|| {
                            TupleBindingOrigin {
                                module: module.to_owned(),
                                span: name.span,
                                name: name.text.clone(),
                            }
                        }),
                    );
                }
                env.insert(name.text.clone(), Binding::Live(value));
            }
            PatternKind::Tuple(patterns) => {
                let actual = value.ty();
                let help = if matches!(value, Value::Quantum(..)) {
                    "; help: a quantum register is one owner; call `split` to obtain its immediate product fields, then split any nested register separately"
                } else {
                    ""
                };
                let Some(fields) = value
                    .into_fields()
                    .filter(|fields| fields.len() == patterns.len())
                else {
                    return Err(self.error(
                        module,
                        pattern.span,
                        ErrorCode::TypeMismatch,
                        format!("tuple pattern requires a tuple value with the same immediate arity: expected a tuple of {} immediate fields, found `{actual}`{help}", patterns.len()),
                    ));
                };
                for (pattern, field) in patterns.iter().zip(fields) {
                    self.bind(module, pattern, field, env, names)?;
                }
            }
        }
        Ok(())
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
        let first_operation = self.operations.len();
        let result = self.expr_inner(module, expr, env);
        self.depth -= 1;
        let value = result?;
        // Nested expressions/callees already supplied more precise positions.
        // Fill only the operations emitted directly by this expression.
        for index in first_operation..self.operations.len() {
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
            ExprKind::Adjoint { function, input }
            | ExprKind::RepeatStatic {
                function, input, ..
            } => {
                let value = self.expr(module, input, env)?;
                let slot = self.quantum(module, input.span, &value, false)?;
                let basis = self.registers[&slot].basis.clone();
                let access = if matches!(expr.kind, ExprKind::Adjoint { .. }) {
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
                match &expr.kind {
                    ExprKind::Adjoint { .. } => {
                        self.compiler.charge(module, expr.span, cost)?;
                        if !is_operation {
                            super::circuit::invert(&mut steps);
                        }
                        expected = expected
                            .map(|m| m.adjoint(&mut self.compiler.exact_work))
                            .transpose()
                            .map_err(|e| self.compiler.op_error(module, expr.span, e.into()))?;
                    }
                    ExprKind::RepeatStatic { count, .. } => {
                        self.compiler.charge(
                            module,
                            expr.span,
                            cost.saturating_add(1).saturating_mul(usize::from(*count)),
                        )?;
                        if is_operation
                            && steps.len().saturating_mul(usize::from(*count))
                                > crate::contract::MAX_CONTRACT_STEPS
                        {
                            return Err(self.error(
                                module,
                                expr.span,
                                ErrorCode::Limit,
                                "operation repetition exceeds 1024 steps",
                            ));
                        }
                        // Bind one body to its independently extracted meaning.
                        // Validate serial copies structurally, without constructing U^n.
                        self.check_transformed(
                            module,
                            expr.span,
                            &basis,
                            &steps,
                            expected.as_ref(),
                        )?;
                        let body = steps;
                        steps = (0..*count).flat_map(|_| body.iter().cloned()).collect();
                        transforms::check_repeated_steps(&body, &steps, *count)
                            .map_err(|e| self.compiler.op_error(module, expr.span, e))?;
                        expected = None;
                    }
                    _ => unreachable!(),
                }
                self.check_transformed(module, expr.span, &basis, &steps, expected.as_ref())?;
                self.apply_circuit(slot, steps);
                Ok(value)
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
                let basis = self.registers[&slot].basis.clone();
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
                    &Ty::pair(Ty::Bit, basis),
                    &steps,
                    expected.as_ref(),
                )?;
                let joined = self.sealed(module, expr.span, "std::quantum", "join", vec![c, q])?;
                let slot = self.quantum(module, expr.span, &joined, false)?;
                self.apply_circuit(slot, steps);
                self.sealed(module, expr.span, "std::quantum", "split", vec![joined])
            }
            ExprKind::Unit => Ok(Value::Unit),
            ExprKind::CBit(value) => {
                let output = self.classical();
                self.operations.push(RawOp::ClassicalConst {
                    value: *value,
                    output,
                });
                Ok(Value::Classical(output))
            }
            ExprKind::Not(input) => {
                let value = self.expr(module, input, env)?;
                let Value::Classical(input) = value else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        format!(
                            "not requires a CBit operand: expected `CBit`, found `{}`",
                            value.ty()
                        ),
                    ));
                };
                let output = self.classical();
                self.operations.push(RawOp::ClassicalNot { input, output });
                Ok(Value::Classical(output))
            }
            ExprKind::And(left, right) | ExprKind::Xor(left, right) => {
                let value = self.expr(module, left, env)?;
                let Value::Classical(left) = value else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        format!(
                            "and/xor require CBit operands: expected `CBit`, found `{}`",
                            value.ty()
                        ),
                    ));
                };
                // Both operands are evaluated, left to right. In particular,
                // false AND must still execute effects in its right operand.
                let value = self.expr(module, right, env)?;
                let Value::Classical(right) = value else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        format!(
                            "and/xor require CBit operands: expected `CBit`, found `{}`",
                            value.ty()
                        ),
                    ));
                };
                let output = self.classical();
                self.operations
                    .push(if matches!(expr.kind, ExprKind::And(..)) {
                        RawOp::ClassicalAnd {
                            left,
                            right,
                            output,
                        }
                    } else {
                        RawOp::ClassicalXor {
                            left,
                            right,
                            output,
                        }
                    });
                Ok(Value::Classical(output))
            }
            ExprKind::Name(name) => {
                let binding = env.get_mut(&name.text).ok_or_else(|| {
                    self.error(
                        module,
                        name.span,
                        ErrorCode::UnknownName,
                        format!("unknown value `{}`", name.text),
                    )
                })?;
                let value = match binding {
                    Binding::Live(value) => value,
                    Binding::Consumed => {
                        return Err(self.error(
                            module,
                            name.span,
                            ErrorCode::Ownership,
                            format!(
                                "quantum ownership `{}` has already been consumed",
                                name.text
                            ),
                        ));
                    }
                    Binding::Hidden { quantum } => {
                        let repair = if *quantum {
                            "include it in the source data with `join` and access it through the data binder of three-argument `with_computed`, or restructure the body"
                        } else {
                            "use a closed classical expression or restructure the body"
                        };
                        return Err(self.error(
                            module,
                            name.span,
                            ErrorCode::Ownership,
                            format!(
                                "with_computed body cannot capture outer binding `{}`; {repair}",
                                name.text
                            ),
                        ));
                    }
                };
                self.compiler
                    .charge(module, name.span, value.tree_size().nodes)?;
                Ok(if value.owns_quantum() {
                    binding.take().expect("live value")
                } else {
                    value.clone()
                })
            }
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
                    if static_args.is_empty() && !self.bindings.contains_key(&callee.text) {
                        if env.contains_key(&callee.text) {
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
                if self.bindings.contains_key(&callee.text) {
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
                    let basis = self.registers[&slot].basis.clone();
                    let steps = self
                        .operation_steps(module, callee, &basis, env, Access::Apply)?
                        .expect("bound operation");
                    self.apply_circuit(slot, steps);
                    return Ok(value);
                }
                let site = CallSite {
                    module,
                    span: expr.span,
                    args,
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
                            "if requires a CBit condition: expected `CBit`, found `{}`",
                            value.ty()
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
                if env.contains_key(&function.text) || self.bindings.contains_key(&function.text) {
                    return Err(self.error(
                        module,
                        function.span,
                        ErrorCode::TypeMismatch,
                        "with_computed requires a basis function name",
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
        let reg = self.registers.get_mut(&slot).expect("owned register");
        self.operations.push(RawOp::ApplyUnitary {
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
        if env.contains_key(&name.text) || self.bindings.contains_key(&name.text) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static operation requires a function name, not a local value",
            ));
        }
        let target = self.compiler.resolve(module, name)?;
        let ty = Ty::Q(Box::new(basis.clone()));
        match &target {
            Callee::User(key) => {
                if self.compiler.declarations[key].kind != FnKind::Unitary {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Effect,
                        "static operation requires a unitary function",
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
                if !matches!(gate.as_str(), "id" | "phase_eighth") && *basis != Ty::Bit {
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
            registers: BTreeMap::new(),
            operations: vec![],
            operation_sources: BTreeMap::new(),
            tuple_binding_origins: Vec::new(),
            next_token: 0,
            next_wire: 0,
            next_classical: 0,
            next_slot: 0,
            effect: Effect::Unitary,
            effect_source: None,
            depth: self.depth,
            bindings: BTreeMap::new(),
            abstract_check: self.abstract_check,
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
            operations: inner.operations,
            quantum_outputs: vec![inner.registers[&slot].token],
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
            .charge(module, span, self.registers[&slot].size())?;
        let reg = self.registers[&slot].clone();
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
        self.operations.push(RawOp::LiftBasis {
            input: reg.token,
            output,
            output_wires: wires.clone(),
            table,
        });
        self.registers.insert(
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
        Ok(Value::Quantum(slot, basis))
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
                "predicate must be a basis function",
            ));
        };
        let predicate = self.compiler.basis.get(&key).ok_or_else(|| {
            self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a basis function",
            )
        })?;
        let size = predicate
            .signature_size()
            .saturating_add(predicate.table.len());
        self.compiler.charge(module, function.span, size)?;
        let predicate = self.compiler.basis[&key].clone();
        let mut params = predicate.params.into_iter();
        let mut domain = params.next().unwrap_or(Ty::Unit);
        for param in params {
            domain = Ty::pair(domain, param);
            self.compiler
                .check_tree(module, function.span, domain.tree_size())?;
        }
        if domain != self.registers[&source_slot].basis || predicate.result != Ty::Bit {
            return Err(self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                format!("predicate must map the source basis type to Bit: expected `{} -> Bit`, found `{domain} -> {}`", self.registers[&source_slot].basis, predicate.result),
            ));
        }
        let wire = self.wire();
        let ancilla = self.register(Ty::Bit, vec![wire]);
        let ancilla_slot = self.quantum(module, span, &ancilla, true)?;
        let initial_token = self.registers[&ancilla_slot].token;
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
        local.insert(binder.text.clone(), Binding::Live(ancilla));
        let start = self.operations.len();
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
        if result != Value::Quantum(ancilla_slot, Ty::Bit) {
            return Err(self.error(
                module,
                body.span,
                ErrorCode::Ownership,
                "with_computed must return its ancilla ownership",
            ));
        }
        let mut expected_input = initial_token;
        let mut use_ops = Vec::new();
        for operation in &self.operations[start..] {
            match operation {
                RawOp::Gate { gate, input, output } if matches!(gate, SingleGate::Z | SingleGate::T) && *input == expected_input => {
                    use_ops.push(ProtectedUse::ProtectedGate { bit: ProtectedBit { region: ProtectedRegion::Ancilla, index: 0 }, gate: *gate });
                    expected_input = *output;
                }
                _ => return Err(self.error(module, body.span, ErrorCode::Unsupported, "with_computed currently accepts only identity and expanded Z/T gates on its ancilla; for other unitary bodies, use with_computed(source, predicate, logical) { |data, ancilla| ... } and return both owners. The logical operation must satisfy the exact computed-relation contract; adding it does not bypass cleanup checking")),
            }
        }
        self.operations.truncate(start);
        // The temporary gates become one protected operation below; their old
        // operation paths must not label this operation or a later expression.
        self.operation_sources.split_off(&vec![start]);
        let ancilla = self
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
            .registers
            .get_mut(&source_slot)
            .expect("protected source");
        self.operations.push(RawOp::ComputeUseUncompute {
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
    lower_function_inner(compiler, key, BTreeMap::new(), false)?.ok_or_else(|| {
        compiler.error(
            &key.0,
            compiler.declarations[key].span,
            ErrorCode::InvalidIr,
            "missing concrete program",
        )
    })
}

fn lower_function_inner(
    compiler: &mut Compiler<'_>,
    key: &Key,
    bindings: super::operations::Bindings,
    abstract_check: bool,
) -> Result<Option<AcceptedProgram>, CompileError> {
    let decl = compiler.declarations[key];
    let (params, _) = compiler.signature(key)?;
    let mut lower = Lowerer {
        compiler,
        registers: BTreeMap::new(),
        operations: Vec::new(),
        operation_sources: BTreeMap::new(),
        tuple_binding_origins: Vec::new(),
        next_token: 0,
        next_wire: 0,
        next_classical: 0,
        next_slot: 0,
        effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings,
        abstract_check,
    };
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    // Signature types are already bounded; account for constructing their
    // value tree and the register's copy of each quantum basis type.
    lower.compiler.charge(
        &key.0,
        decl.span,
        total_size(params.iter().map(|ty| ty.tree_size().nodes)).saturating_mul(2),
    )?;
    let args = params
        .iter()
        .map(|ty| {
            lower.input(
                ty,
                &key.0,
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
        &lower.registers,
        &mut quantum_outputs,
        &mut classical_outputs,
    );
    let raw = RawProgram {
        quantum_inputs,
        classical_inputs,
        operations: lower.operations,
        quantum_outputs,
        classical_outputs,
        declared_effect: effect(decl.kind),
    };
    if abstract_check {
        return Ok(None);
    }
    lower
        .compiler
        .kernel
        .accept_raw_with_budget(raw, &mut lower.compiler.exact_work)
        .map(Some)
        .map_err(|failure| {
            let limit = failure.code == "limit";
            verification_error(
                lower.compiler,
                &lower.operation_sources,
                &key.0,
                decl.span,
                failure,
                limit,
            )
        })
}
