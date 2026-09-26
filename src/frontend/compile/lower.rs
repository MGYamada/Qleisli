use super::basis::BasisValue;
use super::*;
use crate::ir::*;

type Slot = u32;
type Env = BTreeMap<String, Option<Value>>;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Value {
    Unit,
    Classical(ClassicalId),
    Quantum(Slot, Ty),
    Pair(Box<Value>, Box<Value>),
}

impl Value {
    fn ty(&self) -> Ty {
        match self {
            Self::Unit => Ty::Unit,
            Self::Classical(_) => Ty::CBit,
            Self::Quantum(_, basis) => Ty::Q(Box::new(basis.clone())),
            Self::Pair(a, b) => Ty::pair(a.ty(), b.ty()),
        }
    }

    fn owns_quantum(&self) -> bool {
        match self {
            Self::Quantum(..) => true,
            Self::Pair(a, b) => a.owns_quantum() || b.owns_quantum(),
            _ => false,
        }
    }

    fn pair(a: Self, b: Self) -> Self {
        Self::Pair(Box::new(a), Box::new(b))
    }
}

#[derive(Clone)]
struct Register {
    token: TokenId,
    wires: Vec<WireId>,
    basis: Ty,
}

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

    fn call_user(&mut self, key: &Key, args: Vec<Value>) -> Result<Value, CompileError> {
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
        let result = self.call_user_inner(key, args);
        self.depth -= 1;
        result
    }

    fn call_user_inner(&mut self, key: &Key, args: Vec<Value>) -> Result<Value, CompileError> {
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
            return Err(self.error(
                &key.0,
                decl.span,
                ErrorCode::Arity,
                "function argument count does not match",
            ));
        }
        let mut env = Env::new();
        for ((param, ty), value) in decl.params.iter().zip(params).zip(args) {
            if value.ty() != ty {
                return Err(self.error(
                    &key.0,
                    param.span,
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
            .charge(module, block.span, env.len().saturating_mul(2))?;
        let entry = env.clone();
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
        for (name, value) in &local {
            if value.as_ref().is_some_and(Value::owns_quantum)
                && (rebound.contains(name) || entry.get(name) != Some(value))
            {
                return Err(self.error(module, block.span, ErrorCode::Ownership, format!("local quantum ownership `{name}` escapes neither through the result nor an explicit discard")));
            }
        }
        for (name, value) in entry {
            if value.as_ref().is_some_and(Value::owns_quantum)
                && (rebound.contains(&name) || local.get(&name) != Some(&value))
            {
                env.insert(name, None);
            }
        }
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
        result
    }

    fn expr_inner(
        &mut self,
        module: &str,
        expr: &Expr,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        match &expr.kind {
            ExprKind::Unit => Ok(Value::Unit),
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
                let args = args
                    .iter()
                    .map(|arg| self.expr(module, arg, env))
                    .collect::<Result<Vec<_>, _>>()?;
                match target {
                    Callee::User(key) => self.call_user(&key, args),
                    Callee::Sealed(namespace, name) => {
                        self.sealed(module, expr.span, &namespace, &name, args)
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
        }
    }

    fn quantum(
        &self,
        module: &str,
        span: Span,
        value: &Value,
        bit_only: bool,
    ) -> Result<Slot, CompileError> {
        let Value::Quantum(slot, basis) = value else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "operation requires quantum ownership",
            ));
        };
        if bit_only && *basis != Ty::Bit {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "operation requires Q<Bit>",
            ));
        }
        Ok(*slot)
    }

    fn sealed(
        &mut self,
        module: &str,
        span: Span,
        namespace: &str,
        name: &str,
        mut args: Vec<Value>,
    ) -> Result<Value, CompileError> {
        let arity = match name {
            "init0" => 0,
            "cnot" | "join" => 2,
            "toffoli" => 3,
            _ => 1,
        };
        if args.len() != arity {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                format!("{name} requires {arity} arguments"),
            ));
        }
        if namespace == "std::observe" {
            self.effect = Effect::Observe;
        }
        match name {
            "init0" => {
                self.effect = self.effect.max(Effect::Iso);
                let wire = self.wire();
                let value = self.register(Ty::Bit, vec![wire]);
                let slot = self.quantum(module, span, &value, true)?;
                self.operations.push(RawOp::Init0 {
                    output: self.registers[&slot].token,
                    wire,
                });
                Ok(value)
            }
            "h" | "x" | "z" | "t" => {
                let value = args.pop().expect("one argument");
                let slot = self.quantum(module, span, &value, true)?;
                let gate = match name {
                    "h" => SingleGate::H,
                    "x" => SingleGate::X,
                    "z" => SingleGate::Z,
                    _ => SingleGate::T,
                };
                let output = self.token();
                let reg = self.registers.get_mut(&slot).expect("owned register");
                self.operations.push(RawOp::Gate {
                    gate,
                    input: reg.token,
                    output,
                });
                reg.token = output;
                Ok(value)
            }
            "cnot" | "toffoli" => {
                let slots = args
                    .iter()
                    .map(|arg| self.quantum(module, span, arg, true))
                    .collect::<Result<Vec<_>, _>>()?;
                if slots.iter().collect::<BTreeSet<_>>().len() != slots.len() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "gate operands alias one quantum register",
                    ));
                }
                let inputs: Vec<_> = slots
                    .iter()
                    .map(|slot| self.registers[slot].token)
                    .collect();
                let outputs: Vec<_> = slots.iter().map(|_| self.token()).collect();
                self.operations.push(if name == "cnot" {
                    RawOp::Cnot {
                        control: inputs[0],
                        target: inputs[1],
                        control_out: outputs[0],
                        target_out: outputs[1],
                    }
                } else {
                    RawOp::Toffoli {
                        control_a: inputs[0],
                        control_b: inputs[1],
                        target: inputs[2],
                        control_a_out: outputs[0],
                        control_b_out: outputs[1],
                        target_out: outputs[2],
                    }
                });
                for (slot, output) in slots.iter().zip(outputs) {
                    self.registers.get_mut(slot).expect("owned register").token = output;
                }
                let mut args = args.into_iter();
                let a = args.next().expect("first input");
                let b = args.next().expect("second input");
                let pair = Value::pair(a, b);
                Ok(if let Some(target) = args.next() {
                    Value::pair(pair, target)
                } else {
                    pair
                })
            }
            "split" => {
                let value = args.pop().expect("one input");
                let slot = self.quantum(module, span, &value, false)?;
                let reg = self.registers.remove(&slot).expect("owned register");
                let Ty::Pair(a, b) = reg.basis else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "split requires Q<(A, B)>",
                    ));
                };
                let width = a.basis_bits().expect("basis type");
                let left = self.register(*a, reg.wires[..width].to_vec());
                let right = self.register(*b, reg.wires[width..].to_vec());
                let left_slot = self.quantum(module, span, &left, false)?;
                let right_slot = self.quantum(module, span, &right, false)?;
                self.operations.push(RawOp::Split {
                    input: reg.token,
                    left: self.registers[&left_slot].token,
                    right: self.registers[&right_slot].token,
                    left_bits: width as u8,
                });
                Ok(Value::pair(left, right))
            }
            "join" => {
                let a = self.quantum(module, span, &args[0], false)?;
                let b = self.quantum(module, span, &args[1], false)?;
                if a == b {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "join operands alias",
                    ));
                }
                let a = self.registers.remove(&a).expect("owned register");
                let b = self.registers.remove(&b).expect("owned register");
                if a.wires.len() + b.wires.len() > MAX_BITS {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "joined register exceeds 12 bits",
                    ));
                }
                let mut wires = a.wires;
                wires.extend(b.wires);
                let value = self.register(Ty::pair(a.basis, b.basis), wires);
                let slot = self.quantum(module, span, &value, false)?;
                self.operations.push(RawOp::Join {
                    left: a.token,
                    right: b.token,
                    output: self.registers[&slot].token,
                });
                Ok(value)
            }
            "measure_z" | "reset" | "discard" => {
                let value = args.pop().expect("one input");
                let slot = self.quantum(module, span, &value, name != "discard")?;
                let reg = self.registers.remove(&slot).expect("owned register");
                if name == "measure_z" {
                    let output = self.classical();
                    self.operations.push(RawOp::MeasureZ {
                        input: reg.token,
                        output,
                    });
                    Ok(Value::Classical(output))
                } else if name == "discard" {
                    self.operations.push(RawOp::Discard { input: reg.token });
                    Ok(Value::Unit)
                } else {
                    let wire = self.wire();
                    let value = self.register(Ty::Bit, vec![wire]);
                    let slot = self.quantum(module, span, &value, true)?;
                    self.operations.push(RawOp::Reset {
                        input: reg.token,
                        output: self.registers[&slot].token,
                        fresh_wire: wire,
                    });
                    Ok(value)
                }
            }
            _ => Err(self.error(
                module,
                span,
                ErrorCode::Unsupported,
                "unsupported sealed operation",
            )),
        }
    }

    fn lift(
        &mut self,
        module: &str,
        span: Span,
        binder: &Ident,
        input: Value,
        basis: &BasisExpr,
    ) -> Result<Value, CompileError> {
        let slot = self.quantum(module, span, &input, false)?;
        let reg = self.registers[&slot].clone();
        let mut result_ty = None;
        let mut table = Vec::new();
        let mut seen = BTreeSet::new();
        for label in 0..(1u16 << reg.wires.len()) {
            let env = BTreeMap::from([(
                binder.text.clone(),
                BasisValue {
                    ty: reg.basis.clone(),
                    label,
                },
            )]);
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
        let predicate = self.compiler.basis.get(&key).cloned().ok_or_else(|| {
            self.error(
                module,
                function.span,
                ErrorCode::TypeMismatch,
                "predicate must be a basis function",
            )
        })?;
        let domain = predicate
            .params
            .iter()
            .cloned()
            .reduce(Ty::pair)
            .unwrap_or(Ty::Unit);
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

    fn branch(
        &mut self,
        module: &str,
        span: Span,
        condition: ClassicalId,
        then_block: &Block,
        else_block: &Block,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        self.compiler.charge(
            module,
            span,
            env.len()
                .saturating_add(self.registers.len())
                .saturating_mul(2),
        )?;
        let entry_registers = self.registers.clone();
        let outer_ops = std::mem::take(&mut self.operations);
        let entry_effect = self.effect;
        let mut then_env = env.clone();
        let then_result = self.block(module, then_block, &mut then_env)?;
        let then_ops = std::mem::take(&mut self.operations);
        let mut then_registers = std::mem::replace(&mut self.registers, entry_registers.clone());
        let then_effect = self.effect;
        self.effect = entry_effect;
        let mut else_env = env.clone();
        let else_result = self.block(module, else_block, &mut else_env)?;
        let else_ops = std::mem::replace(&mut self.operations, outer_ops);
        let mut else_registers = std::mem::take(&mut self.registers);
        self.effect = self.effect.max(then_effect);
        if then_env != else_env {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "if arms consume different outer quantum bindings",
            ));
        }
        *env = then_env;
        if then_result.ty() != else_result.ty() {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "if arms must return the same type",
            ));
        }
        let mut quantum_phis = Vec::new();
        let mut classical_phis = Vec::new();
        let result = self.merge_results(
            module,
            span,
            then_result,
            else_result,
            &mut then_registers,
            &mut else_registers,
            &mut quantum_phis,
            &mut classical_phis,
        )?;
        if then_registers.len() != else_registers.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "if arms leave incompatible quantum frames",
            ));
        }
        for (slot, then_reg) in then_registers {
            if !entry_registers.contains_key(&slot) {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "branch-local ownership was not returned",
                ));
            }
            let else_reg = else_registers.remove(&slot).ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "if arms leave incompatible quantum frames",
                )
            })?;
            self.merge_register(module, span, slot, then_reg, else_reg, &mut quantum_phis)?;
        }
        self.operations.push(RawOp::ClassicalBranch {
            condition,
            then_ops,
            else_ops,
            quantum_phis,
            classical_phis,
        });
        Ok(result)
    }

    fn merge_register(
        &mut self,
        module: &str,
        span: Span,
        slot: Slot,
        a: Register,
        b: Register,
        phis: &mut Vec<QuantumPhi>,
    ) -> Result<(), CompileError> {
        self.compiler.tick(module, span)?;
        if a.basis != b.basis {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "branch quantum shapes differ",
            ));
        }
        let token = self.token();
        let wires: Vec<_> = (0..a.wires.len()).map(|_| self.wire()).collect();
        phis.push(QuantumPhi {
            then_token: a.token,
            else_token: b.token,
            output: token,
            output_wires: wires.clone(),
        });
        self.registers.insert(
            slot,
            Register {
                token,
                wires,
                basis: a.basis,
            },
        );
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn merge_results(
        &mut self,
        module: &str,
        span: Span,
        a: Value,
        b: Value,
        a_regs: &mut BTreeMap<Slot, Register>,
        b_regs: &mut BTreeMap<Slot, Register>,
        quantum: &mut Vec<QuantumPhi>,
        classical: &mut Vec<ClassicalPhi>,
    ) -> Result<Value, CompileError> {
        match (a, b) {
            (Value::Unit, Value::Unit) => Ok(Value::Unit),
            (Value::Classical(a), Value::Classical(b)) => {
                if a == b {
                    return Ok(Value::Classical(a));
                }
                let output = self.classical();
                classical.push(ClassicalPhi {
                    then_id: a,
                    else_id: b,
                    output,
                });
                Ok(Value::Classical(output))
            }
            (Value::Quantum(a, basis), Value::Quantum(b, _)) => {
                let a = a_regs.remove(&a).ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "then result duplicates quantum ownership",
                    )
                })?;
                let b = b_regs.remove(&b).ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "else result duplicates quantum ownership",
                    )
                })?;
                let slot = self.slot();
                self.merge_register(module, span, slot, a, b, quantum)?;
                Ok(Value::Quantum(slot, basis))
            }
            (Value::Pair(a1, a2), Value::Pair(b1, b2)) => {
                let a =
                    self.merge_results(module, span, *a1, *b1, a_regs, b_regs, quantum, classical)?;
                let b =
                    self.merge_results(module, span, *a2, *b2, a_regs, b_regs, quantum, classical)?;
                Ok(Value::pair(a, b))
            }
            _ => Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "incompatible branch result types",
            )),
        }
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
    let args = params
        .iter()
        .map(|ty| lower.input(ty, &mut quantum_inputs, &mut classical_inputs))
        .collect();
    let result = lower.call_user(key, args)?;
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
