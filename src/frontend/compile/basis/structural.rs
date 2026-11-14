//! Propose controlled XOR directly from the original ordinary predicate.
//! Lean independently derives the predicate and checks the literal circuits.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ordinary::{Boolean, RuntimeExpression, runtime_expression};
use crate::ir::{BitControl, CircuitAction, CircuitStep};
use std::rc::Rc;

struct Parity {
    clauses: Vec<Vec<usize>>,
    cells: usize,
}

impl Parity {
    fn new(clauses: Vec<Vec<usize>>) -> Self {
        let cells = total_size(clauses.iter().map(|controls| controls.len() + 1));
        Self { clauses, cells }
    }
}

enum Value {
    Unit,
    Bit(Parity),
    Word { start: usize, width: usize },
    Tuple(Vec<Rc<Value>>),
}

type Bindings = BTreeMap<BinderKey, Rc<Value>>;

struct Synthesis<'c, 'a> {
    compiler: &'c mut Compiler<'a>,
}

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn propose_structural_predicate(
        &mut self,
        key: Key,
        source: &Ty,
    ) -> Result<Vec<CircuitStep>, CompileError> {
        let previous = self.checking;
        self.checking = Some(key);
        let result = Synthesis { compiler: self }.predicate(key, source);
        self.checking = previous;
        result
    }
}

impl Synthesis<'_, '_> {
    fn unsupported(&self, module: &str, span: Span) -> CompileError {
        self.compiler.error(
            module,
            span,
            ErrorCode::Unsupported,
            "structural predicate synthesis requires a closed Boolean expression over built-in basis inputs",
        )
    }

    fn predicate(&mut self, key: Key, source: &Ty) -> Result<Vec<CircuitStep>, CompileError> {
        let decl = self.compiler.declarations[&key];
        let module = self.compiler.dormant_module(key, decl.span)?;
        let span = decl.span;
        let (params, result) = self.compiler.signature(&key)?;
        if params.as_slice() != std::slice::from_ref(source) || result != Ty::bit() {
            return Err(self.compiler.error(
                &module, span, ErrorCode::TypeMismatch,
                "structural predicate must have one parameter of the exact source basis and return Bit",
            ));
        }
        let mut width = 0;
        let input = self.input(&module, span, source, &mut width)?;
        let value = self.body(&module, key, vec![input], 0)?;
        let parity = self.bit(&module, span, &value)?;
        self.compiler
            .charge(&module, span, parity.cells.saturating_mul(8) + 1)?;
        Ok(parity
            .clauses
            .iter()
            .map(|clause| CircuitStep {
                controls: clause
                    .iter()
                    .map(|axis| BitControl {
                        index: *axis,
                        when_one: true,
                    })
                    .collect(),
                action: CircuitAction::Monomial {
                    indices: vec![width],
                    permutation: vec![1, 0],
                    phases: vec![0, 0],
                },
            })
            .collect())
    }

    fn input(
        &mut self,
        module: &str,
        span: Span,
        ty: &Ty,
        axis: &mut usize,
    ) -> Result<Rc<Value>, CompileError> {
        self.compiler.tick(module, span)?;
        let value = match &ty.kind {
            Kind::Unit => Value::Unit,
            Kind::Bit => {
                let value = Value::Bit(Parity::new(vec![vec![*axis]]));
                *axis += 1;
                value
            }
            Kind::Bits(width) => {
                let start = *axis;
                *axis = axis.checked_add(*width as usize).ok_or_else(|| {
                    self.compiler.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "structural predicate axis overflow",
                    )
                })?;
                Value::Word {
                    start,
                    width: *width as usize,
                }
            }
            Kind::Tuple(fields) => {
                self.compiler.charge(module, span, fields.len())?;
                Value::Tuple(
                    fields
                        .iter()
                        .map(|ty| self.input(module, span, ty, axis))
                        .collect::<Result<_, _>>()?,
                )
            }
            _ => return Err(self.unsupported(module, span)),
        };
        Ok(Rc::new(value))
    }

    fn body(
        &mut self,
        module: &str,
        key: Key,
        args: Vec<Rc<Value>>,
        depth: usize,
    ) -> Result<Rc<Value>, CompileError> {
        let decl = self.compiler.declarations[&key];
        let FnBody::Basis(body) = &decl.body else {
            return Err(self.unsupported(module, decl.span));
        };
        if decl.kind != FnKind::Classical
            || !decl.static_params.is_empty()
            || decl.params.len() != args.len()
        {
            return Err(self.unsupported(module, decl.span));
        }
        let mut bindings = Bindings::new();
        for (param, arg) in decl.params.iter().zip(args) {
            self.bind(module, &param.pattern, arg, &mut bindings)?;
        }
        self.expression(module, body, &bindings, depth)
    }

    fn bind(
        &mut self,
        module: &str,
        pattern: &Pattern,
        value: Rc<Value>,
        bindings: &mut Bindings,
    ) -> Result<(), CompileError> {
        self.compiler.tick(module, pattern.span)?;
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.compiler
                    .charge(module, pattern.span, name.text.len() + bindings.len() + 1)?;
                let locals = self.compiler.locals();
                bindings.insert(locals.key(locals.binder(name)).clone(), value);
            }
            PatternKind::Wildcard => {}
            PatternKind::Tuple(patterns) => {
                let fields = match value.as_ref() {
                    Value::Unit => &[][..],
                    Value::Tuple(fields) => fields.as_slice(),
                    _ => return Err(self.unsupported(module, pattern.span)),
                };
                if fields.len() != patterns.len() {
                    return Err(self.unsupported(module, pattern.span));
                }
                for (child, field) in patterns.iter().zip(fields) {
                    self.bind(module, child, Rc::clone(field), bindings)?;
                }
            }
        }
        Ok(())
    }

    fn expression(
        &mut self,
        module: &str,
        expr: &BasisExpr,
        bindings: &Bindings,
        depth: usize,
    ) -> Result<Rc<Value>, CompileError> {
        self.compiler.tick(module, expr.span)?;
        if depth >= MAX_DEPTH {
            return Err(self.compiler.error(
                module,
                expr.span,
                ErrorCode::Limit,
                "structural predicate synthesis exceeds the initial depth limit",
            ));
        }
        match runtime_expression(expr) {
            RuntimeExpression::Nominal => Err(self.unsupported(module, expr.span)),
            RuntimeExpression::Unit => Ok(Rc::new(Value::Unit)),
            RuntimeExpression::BitIndex { receiver, index } => {
                let word = self.expression(module, receiver, bindings, depth + 1)?;
                match word.as_ref() {
                    Value::Word { start, width } if index < *width => {
                        Ok(Rc::new(Value::Bit(Parity::new(vec![vec![start + index]]))))
                    }
                    _ => Err(self.unsupported(module, expr.span)),
                }
            }
            RuntimeExpression::Name(name) => {
                self.compiler
                    .charge(module, name.span, name.text.len() + bindings.len() + 1)?;
                self.compiler
                    .locals()
                    .local_key(name)
                    .and_then(|key| bindings.get(key))
                    .cloned()
                    .ok_or_else(|| self.unsupported(module, name.span))
            }
            RuntimeExpression::Tuple(fields) => {
                self.compiler.charge(module, expr.span, fields.len())?;
                let values = fields
                    .iter()
                    .map(|item| self.expression(module, item, bindings, depth + 1))
                    .collect::<Result<_, _>>()?;
                Ok(Rc::new(Value::Tuple(values)))
            }
            RuntimeExpression::Call { callee, args } => {
                self.compiler.charge(module, expr.span, args.len() + 1)?;
                let target = self.compiler.resolve(module, callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.expression(module, arg, bindings, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                match target {
                    Callee::Primitive(PrimitiveId::EmptyBits) if args.is_empty() => {
                        Ok(Rc::new(Value::Word { start: 0, width: 0 }))
                    }
                    Callee::User(key) => {
                        let target_module = self.compiler.dormant_module(key, callee.span)?;
                        let previous = self.compiler.checking.replace(key);
                        let result = self.body(&target_module, key, args, depth + 1);
                        self.compiler.checking = previous;
                        result
                    }
                    _ => Err(self.unsupported(module, callee.span)),
                }
            }
            RuntimeExpression::Boolean { operation, inputs } => {
                let value = match inputs {
                    [None, None] => {
                        let Boolean::Constant(value) = operation else {
                            unreachable!("original Boolean arity")
                        };
                        Parity::new(if value { vec![vec![]] } else { vec![] })
                    }
                    [Some(input), None] => {
                        let input = self.expression(module, input, bindings, depth + 1)?;
                        let input = self.bit(module, expr.span, &input)?;
                        self.compiler.charge(module, expr.span, input.cells + 1)?;
                        Parity::new(
                            std::iter::once(vec![])
                                .chain(input.clauses.iter().cloned())
                                .collect(),
                        )
                    }
                    [Some(left), Some(right)] => {
                        let left = self.expression(module, left, bindings, depth + 1)?;
                        let right = self.expression(module, right, bindings, depth + 1)?;
                        let left = self.bit(module, expr.span, &left)?;
                        let right = self.bit(module, expr.span, &right)?;
                        self.combine(module, expr.span, operation, left, right)?
                    }
                    [None, Some(_)] => unreachable!("original Boolean arity"),
                };
                Ok(Rc::new(Value::Bit(value)))
            }
        }
    }

    fn bit<'v>(
        &self,
        module: &str,
        span: Span,
        value: &'v Value,
    ) -> Result<&'v Parity, CompileError> {
        match value {
            Value::Bit(parity) => Ok(parity),
            _ => Err(self.unsupported(module, span)),
        }
    }

    fn combine(
        &mut self,
        module: &str,
        span: Span,
        operation: Boolean,
        left: &Parity,
        right: &Parity,
    ) -> Result<Parity, CompileError> {
        let cells = left.cells.saturating_add(right.cells).saturating_add(1);
        let clauses = match operation {
            Boolean::Xor => {
                self.compiler.charge(module, span, cells)?;
                left.clauses.iter().chain(&right.clauses).cloned().collect()
            }
            Boolean::And => {
                // Charge the full Cartesian product and stable control deduplication before allocation.
                let cost = (left.cells + 1)
                    .saturating_mul(right.cells + 1)
                    .saturating_mul(cells);
                self.compiler.charge(module, span, cost)?;
                let mut clauses = Vec::new();
                for first in &left.clauses {
                    for second in &right.clauses {
                        let mut seen = BTreeSet::new();
                        clauses.push(
                            first
                                .iter()
                                .chain(second)
                                .copied()
                                .filter(|axis| seen.insert(*axis))
                                .collect(),
                        );
                    }
                }
                clauses
            }
            Boolean::Constant(_) | Boolean::Not => unreachable!("binary Boolean expression"),
        };
        Ok(Parity::new(clauses))
    }
}
