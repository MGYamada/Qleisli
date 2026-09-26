//! Source evaluation, lexical scopes, calls, and checked IR construction.
//!
//! Values and their ownership representation live in `value`; sealed operations
//! and classical branch merging have separate implementations. All of them use
//! the same complete register store and ID supply, including suspended callers.

mod branch;
mod certified;
mod function_contract;
mod primitives;
mod scope;
mod value;

use value::{Env, Register, Slot, Value, env_size};

use super::*;
use crate::ir::*;

#[derive(Clone, Copy)]
struct CallSite<'a> {
    module: &'a str,
    span: Span,
    args: &'a [Expr],
}

// The register store includes quantum values held by pending arguments and
// suspended callers, not just bindings visible in the current lexical Env.
// Branches snapshot registers/effects, but never rewind the fresh ID supply.
// Every emitted program must still pass the independent IR verifier.
struct Lowerer<'c, 'p> {
    compiler: &'c mut Compiler<'p>,
    registers: BTreeMap<Slot, Register>,
    operations: Vec<RawOp>,
    next_token: u32,
    next_wire: u32,
    next_classical: u32,
    next_slot: u32,
    effect: Effect,
    depth: usize,
}

impl Lowerer<'_, '_> {
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
        quantum: &mut Vec<QuantumPort>,
        classical: &mut Vec<ClassicalId>,
    ) -> Value {
        match ty {
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
                        bits: reg.wires.len() as u8,
                    },
                });
                value
            }
            Ty::Pair(a, b) => {
                let a = self.input(a, quantum, classical);
                let b = self.input(b, quantum, classical);
                Value::pair(a, b)
            }
            Ty::Bit => unreachable!("ordinary signature"),
        }
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
        let result = self.call_user_inner(key, args, site);
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
        if decl.kind == FnKind::Basis {
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
                    format!("argument `{}` has the wrong type", param.name.text),
                ));
            }
            env.insert(param.name.text.clone(), Some(value));
        }
        let previous_effect = self.effect;
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
                "result does not match the function return type",
            ));
        }
        self.no_owned_bindings(&key.0, body.span, &env)?;
        if self.effect > effect(decl.kind) {
            return Err(self.error(
                &key.0,
                decl.span,
                ErrorCode::Effect,
                "body exceeds the declared function effect",
            ));
        }
        self.effect = previous_effect.max(effect(decl.kind));
        Ok(value)
    }

    fn no_owned_bindings(&self, module: &str, span: Span, env: &Env) -> Result<(), CompileError> {
        if let Some((name, _)) = env
            .iter()
            .find(|(_, value)| value.as_ref().is_some_and(Value::owns_quantum))
        {
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
            self.error(module, block.span, ErrorCode::Ownership, format!("local quantum ownership `{name}` escapes neither through the result nor an explicit discard"))
        })?;
        *env = entry;
        Ok(result)
    }

    fn bind(
        &self,
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
                    .and_then(Option::as_ref)
                    .is_some_and(Value::owns_quantum)
                {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Ownership,
                        "binding would hide unconsumed quantum ownership",
                    ));
                }
                env.insert(name.text.clone(), Some(value));
            }
            PatternKind::Tuple(a, b) => {
                let Value::Pair(left, right) = value else {
                    return Err(self.error(
                        module,
                        pattern.span,
                        ErrorCode::TypeMismatch,
                        "tuple pattern requires a tuple value",
                    ));
                };
                self.bind(module, a, *left, env, names)?;
                self.bind(module, b, *right, env, names)?;
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
        let result = self.expr_inner(module, expr, env);
        self.depth -= 1;
        let value = result?;
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
                let mut steps = self.static_steps(module, function, &basis, env)?;
                let cost = total_size(steps.iter().map(super::circuit::size));
                match &expr.kind {
                    ExprKind::Adjoint { .. } => {
                        self.compiler.charge(module, expr.span, cost)?;
                        super::circuit::invert(&mut steps);
                    }
                    ExprKind::RepeatStatic { count, .. } => {
                        self.compiler.charge(
                            module,
                            expr.span,
                            cost.saturating_add(1).saturating_mul(usize::from(*count)),
                        )?;
                        steps = (0..*count).flat_map(|_| steps.iter().cloned()).collect();
                    }
                    _ => unreachable!(),
                }
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
                for (name, when_one) in [(zero, false), (one, true)] {
                    let mut arm = self.static_steps(module, name, &basis, env)?;
                    self.compiler.charge(
                        module,
                        expr.span,
                        total_size(arm.iter().map(super::circuit::size)).saturating_add(arm.len()),
                    )?;
                    for step in &mut arm {
                        super::circuit::remap(step, &axes);
                        step.controls.push(BitControl { index: 0, when_one });
                    }
                    steps.extend(arm);
                }
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
                let Value::Classical(input) = self.expr(module, input, env)? else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "not requires a CBit operand",
                    ));
                };
                let output = self.classical();
                self.operations.push(RawOp::ClassicalNot { input, output });
                Ok(Value::Classical(output))
            }
            ExprKind::And(left, right) | ExprKind::Xor(left, right) => {
                let Value::Classical(left) = self.expr(module, left, env)? else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "and/xor require CBit operands",
                    ));
                };
                // Both operands are evaluated, left to right. In particular,
                // false AND must still execute effects in its right operand.
                let Value::Classical(right) = self.expr(module, right, env)? else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "and/xor require CBit operands",
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
                let value = binding.as_ref().ok_or_else(|| {
                    self.error(
                        module,
                        name.span,
                        ErrorCode::Ownership,
                        format!(
                            "quantum ownership `{}` has already been consumed",
                            name.text
                        ),
                    )
                })?;
                self.compiler
                    .charge(module, name.span, value.tree_size().nodes)?;
                Ok(if value.owns_quantum() {
                    binding.take().expect("live value")
                } else {
                    value.clone()
                })
            }
            ExprKind::Tuple(a, b) => {
                let a = self.expr(module, a, env)?;
                let b = self.expr(module, b, env)?;
                Ok(Value::pair(a, b))
            }
            ExprKind::Call { callee, args } => {
                if env.contains_key(&callee.text) {
                    return Err(self.error(
                        module,
                        callee.span,
                        ErrorCode::TypeMismatch,
                        "a local value is not callable",
                    ));
                }
                let target = self.compiler.resolve(module, callee)?;
                let values = args
                    .iter()
                    .map(|arg| self.expr(module, arg, env))
                    .collect::<Result<Vec<_>, _>>()?;
                match target {
                    Callee::User(key) => self.call_user(
                        &key,
                        values,
                        Some(CallSite {
                            module,
                            span: expr.span,
                            args,
                        }),
                    ),
                    Callee::Sealed(namespace, name) => {
                        self.sealed(module, expr.span, &namespace, &name, values)
                    }
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let Value::Classical(condition) = self.expr(module, condition, env)? else {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::TypeMismatch,
                        "if requires a CBit condition",
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
                if env.contains_key(&function.text) {
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
        if env.contains_key(&name.text) {
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
                if namespace != "std::quantum" || !matches!(gate.as_str(), "h" | "x" | "z" | "t") {
                    return Err(self.error(
                        module,
                        name.span,
                        ErrorCode::Effect,
                        "static sealed operation must be h, x, z or t",
                    ));
                }
                if *basis != Ty::Bit {
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
            next_token: 0,
            next_wire: 0,
            next_classical: 0,
            next_slot: 0,
            effect: Effect::Unitary,
            depth: self.depth,
        };
        let mut quantum_inputs = vec![];
        let mut classical_inputs = vec![];
        let arg = inner.input(&ty, &mut quantum_inputs, &mut classical_inputs);
        let result = match target {
            Callee::User(key) => inner.call_user(&key, vec![arg], None)?,
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
        let checked = crate::verify(raw).map_err(|err| {
            inner
                .compiler
                .error(module, name.span, ErrorCode::InvalidIr, err.to_string())
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
            self.effect = self.effect.max(Effect::Iso);
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
                "predicate must map the source basis type to Bit",
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
            .map(|(name, value)| {
                (
                    name.clone(),
                    value
                        .as_ref()
                        .filter(|value| !value.owns_quantum())
                        .cloned(),
                )
            })
            .collect();
        local.insert(binder.text.clone(), Some(ancilla));
        let start = self.operations.len();
        let previous_effect = self.effect;
        self.effect = Effect::Unitary;
        let result = self.block(module, body, &mut local)?;
        self.no_owned_bindings(module, body.span, &local)?;
        if self.effect != Effect::Unitary {
            return Err(self.error(
                module,
                body.span,
                ErrorCode::Effect,
                "with_computed body must be unitary",
            ));
        }
        self.effect = previous_effect;
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
                _ => return Err(self.error(module, body.span, ErrorCode::Unsupported, "with_computed currently accepts only identity and expanded Z/T gates on its ancilla")),
            }
        }
        self.operations.truncate(start);
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
) -> Result<VerifiedProgram, CompileError> {
    let decl = compiler.declarations[key];
    let (params, _) = compiler.signature(key)?;
    let mut lower = Lowerer {
        compiler,
        registers: BTreeMap::new(),
        operations: Vec::new(),
        next_token: 0,
        next_wire: 0,
        next_classical: 0,
        next_slot: 0,
        effect: Effect::Unitary,
        depth: 0,
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
        .map(|ty| lower.input(ty, &mut quantum_inputs, &mut classical_inputs))
        .collect();
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
    crate::verify(raw).map_err(|failure| {
        lower
            .compiler
            .error(&key.0, decl.span, ErrorCode::InvalidIr, failure.to_string())
    })
}
