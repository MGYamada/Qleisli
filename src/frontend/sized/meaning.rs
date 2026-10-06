//! Exact finite Meaning preparation from checked original source occurrences.
//! This checks every declared target, including unused ones. Tables are
//! untrusted mathematical requests, not provider equality or native evidence.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use crate::frontend::ast::{BasisExpr, Decl, FnBody, FnKind, Ident, Pattern, PatternKind, Span};
use crate::frontend::check::{self, Budget, Interface, Result, SourceError};
use crate::frontend::ordinary::{Boolean, finite};
use crate::frontend::resolve::locals::{BinderKey, Index, ResolvedUse};
use crate::frontend::resolve::{DefId, Resolution, Target};
use crate::frontend::source::SourceCollection;
use crate::frontend::types::{Kind, Type};
use std::collections::BTreeMap;

type Ty = Type<u32>;
type Environment = BTreeMap<BinderKey, Value>;
struct Value {
    ty: Ty,
    label: u16,
}
struct Product {
    fields: Vec<Ty>,
    width: usize,
    label: u16,
}
struct Context<'a, 'ast> {
    sources: &'a SourceCollection,
    resolution: &'a Resolution,
    interfaces: &'a BTreeMap<DefId, Interface>,
    indices: &'a BTreeMap<DefId, Index<'ast>>,
    budget: &'a Budget,
    definition: DefId,
}

pub(super) fn validate<'ast>(
    sources: &SourceCollection,
    resolution: &Resolution,
    interfaces: &BTreeMap<DefId, Interface>,
    indices: &BTreeMap<DefId, Index<'ast>>,
    budget: &Budget,
) -> Result<()> {
    for (id, declaration) in resolution.declarations() {
        budget.charge(Span::default(), 1)?;
        if declaration.kind != FnKind::Meaning {
            continue;
        }
        let context = Context {
            sources,
            resolution,
            interfaces,
            indices,
            budget,
            definition: id,
        };
        context
            .target()
            .map_err(|e| e.in_module(&declaration.name.0))?;
    }
    Ok(())
}

impl<'a, 'ast> Context<'a, 'ast> {
    fn declaration(&self) -> &'a Decl {
        let declaration = self.resolution.declaration(self.definition);
        &self
            .sources
            .get(&declaration.name.0)
            .expect("original source")
            .syntax()
            .decls[declaration.ast_index]
    }
    fn error(&self, span: Span, message: impl Into<String>) -> SourceError {
        SourceError::new("meaning", span, message)
            .in_module(&self.resolution.declaration(self.definition).name.0)
    }
    fn global(&self, name: &Ident) -> Result<DefId> {
        let index = &self.indices[&self.definition];
        match index.table.usage(index.usage(name)).target {
            ResolvedUse::Global(Target::Declaration(id)) => Ok(id),
            _ => Err(self.error(
                name.span,
                "Meaning expressions require a resolved classical function",
            )),
        }
    }
    fn closed(&self, ty: &check::Ty, span: Span) -> Result<Ty> {
        check::close_type_budgeted(
            ty,
            &BTreeMap::new(),
            &BTreeMap::new(),
            span,
            |span, cells| self.budget.charge(span, cells),
        )
    }
    fn copy(&self, ty: &Ty, span: Span) -> Result<Ty> {
        let size = check::type_size_budgeted(ty, 4096, 64, true, span, &mut |span, cells| {
            self.budget.charge(span, cells)
        })?;
        self.budget.charge(span, size.nodes)?;
        Ok(ty.clone())
    }
    fn width(&self, ty: &Ty, span: Span) -> Result<usize> {
        self.budget.charge(span, 1)?;
        let mut pending = vec![ty];
        let mut width = 0usize;
        while let Some(node) = pending.pop() {
            self.budget.charge(span, 1)?;
            let bits = match &node.kind {
                Kind::Unit => 0,
                Kind::Bit => 1,
                Kind::Bits(bits) => usize::try_from(*bits)
                    .map_err(|_| self.error(span, "basis width cannot be represented"))?,
                Kind::Tuple(fields) => {
                    self.budget.charge(span, fields.len())?;
                    pending.extend(fields);
                    0
                }
                _ => return Err(self.error(span, "Meaning requires a closed ordinary basis")),
            };
            width = width.checked_add(bits).ok_or_else(|| {
                SourceError::new("limit", span, "classical Meaning basis width overflow")
            })?;
            if width > 12 {
                return Err(SourceError::new(
                    "limit",
                    span,
                    "classical Meaning evaluation exceeds 12 bits",
                ));
            }
        }
        Ok(width)
    }
    fn bind(&self, pattern: &Pattern, ty: &Ty, label: u16, env: &mut Environment) -> Result<()> {
        self.budget.charge(pattern.span, 1)?;
        match &pattern.kind {
            PatternKind::Name(name) => {
                let ty = self.copy(ty, name.span)?;
                self.budget.charge(name.span, name.text.len() + 1)?;
                let index = &self.indices[&self.definition];
                env.insert(
                    index.table.key(index.binder(name)).clone(),
                    Value { ty, label },
                );
            }
            PatternKind::Wildcard => (),
            PatternKind::Tuple(patterns) => {
                let fields = ty.pattern_fields(patterns.len()).ok_or_else(|| {
                    self.error(
                        pattern.span,
                        "basis pattern has a different exact product tree",
                    )
                })?;
                let mut offset = 0;
                for (pattern, field) in patterns.iter().zip(fields) {
                    let width = self.width(field, pattern.span)?;
                    self.bind(pattern, field, (label >> offset) & ((1 << width) - 1), env)?;
                    offset += width;
                }
            }
        }
        Ok(())
    }
    fn target(&self) -> Result<()> {
        let declaration = self.declaration();
        let FnBody::Meaning {
            permutation,
            function,
        } = &declaration.body
        else {
            unreachable!("checked Meaning declaration")
        };
        let basis = self.closed(&self.interfaces[&self.definition].result, declaration.span)?;
        let width = self.width(&basis, declaration.span)?;
        if width > crate::contract::MAX_CONTRACT_BITS {
            return Err(SourceError::new(
                "limit",
                declaration.span,
                "exact Meanings support at most 6 bits",
            ));
        }
        let id = self.global(function)?;
        let mut child = Context {
            definition: id,
            ..*self
        };
        let target = child.declaration();
        let interface = &self.interfaces[&id];
        self.budget.charge(function.span, interface.params.len())?;
        let domain = interface
            .params
            .iter()
            .map(|ty| child.closed(ty, function.span))
            .collect::<Result<Vec<_>>>()?;
        let result = child.closed(&interface.result, function.span)?;
        let expected = if *permutation {
            self.copy(&basis, declaration.span)?
        } else {
            self.budget.charge(declaration.span, 5)?;
            Ty::tuple(vec![Ty::bit(), Ty::tuple(vec![Ty::bit(), Ty::bit()])])
        };
        if domain != [basis] || result != expected {
            return Err(self.error(
                function.span,
                "meaning function has the wrong exact basis signature",
            ));
        }
        let FnBody::Basis(body) = &target.body else {
            return Err(self.error(function.span, "Meaning requires a classical function body"));
        };
        let dimension = 1usize << width;
        // Reserve all table/collision cells before enumerating the first row.
        self.budget.charge(declaration.span, dimension * 2)?;
        let mut table = Vec::with_capacity(dimension);
        let mut seen = vec![None; dimension];
        for input in 0..dimension {
            let mut env = Environment::new();
            child
                .bind(
                    &target.params[0].pattern,
                    &domain[0],
                    input as u16,
                    &mut env,
                )
                .map_err(|e| e.in_module(&self.resolution.declaration(id).name.0))?;
            let value = finite::evaluate(&mut child, body, &env, 0)
                .map_err(|e| e.in_module(&self.resolution.declaration(id).name.0))?;
            if value.ty != result {
                return Err(
                    child.error(body.span, "Meaning result has a different exact basis tree")
                );
            }
            table.push(value.label);
        }
        for (input, output) in table.into_iter().enumerate() {
            self.budget.charge(declaration.span, 1)?;
            if *permutation {
                let previous = seen.get_mut(usize::from(output)).ok_or_else(|| {
                    self.error(declaration.span, "permutation output is outside its basis")
                })?;
                if let Some(first) = previous.replace(input) {
                    return Err(self.error(
                        declaration.span,
                        format!("permutation inputs {first} and {input} both map to {output}"),
                    ));
                }
            } else if output > 7 {
                return Err(self.error(declaration.span, "phase label is outside zeta_8"));
            }
        }
        Ok(())
    }
}

impl finite::Context for Context<'_, '_> {
    type Value = Value;
    type Environment = Environment;
    type Tuple = Product;
    type Error = SourceError;
    fn enter(&mut self, span: Span, depth: usize) -> Result<()> {
        self.budget.charge(span, 1)?;
        if depth >= 64 {
            return Err(SourceError::new(
                "limit",
                span,
                "classical Meaning evaluation exceeds depth 64",
            ));
        }
        Ok(())
    }
    fn name(&mut self, name: &Ident, env: &Environment) -> Result<Value> {
        let index = &self.indices[&self.definition];
        let ResolvedUse::Local(id) = index.table.usage(index.usage(name)).target else {
            return Err(self.error(name.span, "expected a resolved ordinary basis value"));
        };
        let value = env
            .get(index.table.key(id))
            .ok_or_else(|| self.error(name.span, "missing ordinary basis binding"))?;
        Ok(Value {
            ty: self.copy(&value.ty, name.span)?,
            label: value.label,
        })
    }
    fn unit(&mut self) -> Value {
        Value {
            ty: Ty::unit(),
            label: 0,
        }
    }
    fn bit(&mut self, value: bool) -> Value {
        Value {
            ty: Ty::bit(),
            label: u16::from(value),
        }
    }
    fn tuple(&mut self, _: usize) -> Product {
        Product {
            fields: Vec::new(),
            width: 0,
            label: 0,
        }
    }
    fn push(&mut self, span: Span, tuple: &mut Product, value: Value) -> Result<()> {
        let width = self.width(&value.ty, span)?;
        if tuple.width + width > 12 {
            return Err(SourceError::new(
                "limit",
                span,
                "classical Meaning result exceeds 12 bits",
            ));
        }
        self.budget.charge(span, 1)?;
        tuple.label |= value.label << tuple.width;
        tuple.width += width;
        tuple.fields.push(value.ty);
        Ok(())
    }
    fn product(&mut self, tuple: Product) -> Value {
        Value {
            ty: Ty::tuple(tuple.fields),
            label: tuple.label,
        }
    }
    fn require_bit(&mut self, span: Span, value: &Value) -> Result<()> {
        if value.ty == Ty::bit() {
            Ok(())
        } else {
            Err(self.error(span, "not/xor/and require Bit operands"))
        }
    }
    fn boolean(&mut self, op: Boolean, a: Value, b: Option<Value>) -> Value {
        Value {
            ty: Ty::bit(),
            label: match op {
                Boolean::Not => a.label ^ 1,
                Boolean::And => a.label & b.expect("binary operand").label,
                Boolean::Xor => a.label ^ b.expect("binary operand").label,
                Boolean::Constant(_) => unreachable!("literal handled directly"),
            },
        }
    }
    fn call(
        &mut self,
        span: Span,
        callee: &Ident,
        args: &[BasisExpr],
        env: &Environment,
        depth: usize,
    ) -> Result<Value> {
        let id = self.global(callee)?;
        let interface = &self.interfaces[&id];
        let mut child = Context {
            definition: id,
            ..*self
        };
        let declaration = child.declaration();
        let FnBody::Basis(body) = &declaration.body else {
            return Err(self.error(
                span,
                "Meaning expressions may call only classical functions",
            ));
        };
        if args.len() != interface.params.len() {
            return Err(self.error(span, "classical argument count does not match"));
        }
        let mut bindings = Environment::new();
        for ((arg, param), ty) in args.iter().zip(&declaration.params).zip(&interface.params) {
            let value = finite::evaluate(self, arg, env, depth + 1)?;
            let ty = child
                .closed(ty, arg.span)
                .map_err(|e| e.in_module(&self.resolution.declaration(self.definition).name.0))?;
            if value.ty != ty {
                return Err(self.error(
                    arg.span,
                    "classical argument has a different exact basis tree",
                ));
            }
            child
                .bind(&param.pattern, &ty, value.label, &mut bindings)
                .map_err(|e| e.in_module(&self.resolution.declaration(id).name.0))?;
        }
        let value = finite::evaluate(&mut child, body, &bindings, depth + 1)
            .map_err(|e| e.in_module(&self.resolution.declaration(id).name.0))?;
        let result = child
            .closed(&interface.result, span)
            .map_err(|e| e.in_module(&self.resolution.declaration(self.definition).name.0))?;
        if value.ty != result {
            return Err(self.error(span, "classical result has a different exact basis tree"));
        }
        Ok(value)
    }
    fn finish(&mut self, span: Span, value: Value) -> Result<Value> {
        check::type_size_budgeted(&value.ty, 4096, 64, true, span, &mut |span, cells| {
            self.budget.charge(span, cells)
        })?;
        self.width(&value.ty, span)?;
        Ok(value)
    }
}
