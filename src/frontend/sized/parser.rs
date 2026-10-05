//! Temporary projection of the single common AST into the sized checker profile.
//!
//! This module never reads source text or tokens. Its located rejections are
//! profile restrictions, not a competing grammar or verification authority.
use super::ast::*;
use super::{Error, Result, Span};
use crate::frontend::ast as source;
use crate::frontend::resolve::locals::{Index, UseSiteId};
use std::sync::Arc;

fn unsupported(span: Span, message: &str) -> Error {
    Error::new(
        "unsupported",
        span,
        format!("sized preparation profile: {message}"),
    )
}

pub(super) fn project(module: &source::Module) -> Result<Module> {
    if module.decls.is_empty() {
        return Err(unsupported(
            module.span,
            "requires at least one ordinary function",
        ));
    }
    Ok(Module {
        functions: module
            .decls
            .iter()
            .map(|declaration| project_declaration(declaration, None))
            .collect::<Result<_>>()?,
    })
}

pub(super) fn project_declaration(
    declaration: &source::Decl,
    index: Option<&Index<'_>>,
) -> Result<Function> {
    Projection { index }.function(declaration)
}

struct Projection<'a, 'ast> {
    index: Option<&'a Index<'ast>>,
}
impl Projection<'_, '_> {
    fn binding(&self, name: &source::Ident) -> BindingName {
        let info = self
            .index
            .map(|index| index.table.binder(index.binder(name)));
        BindingName {
            name: name.text.clone(),
            key: info.map(|info| info.key.clone()),
            shadowed: info
                .and_then(|info| info.shadowed)
                .map(|id| self.index.unwrap().table.key(id).clone()),
        }
    }
    fn reference(&self, name: &str, site: Option<UseSiteId>) -> Reference {
        Reference {
            name: name.into(),
            site,
            local: site.and_then(|site| match self.index.unwrap().table.usage(site).target {
                ResolvedUse::Local(id) => Some(self.index.unwrap().table.key(id).clone()),
                ResolvedUse::Global(_) | ResolvedUse::Unresolved => None,
            }),
        }
    }
    fn ident(&self, name: &source::Ident) -> Reference {
        self.reference(&name.text, self.index.map(|index| index.usage(name)))
    }
    fn natural(&self, natural: &source::Natural) -> Natural {
        Natural {
            span: natural.span,
            kind: match &natural.kind {
                source::NatKind::Number(n) => NatKind::Number(*n),
                source::NatKind::Name(name) => NatKind::Name(
                    self.reference(name, self.index.map(|index| index.natural_usage(natural))),
                ),
                source::NatKind::Add(a, b) => {
                    NatKind::Add(Box::new(self.natural(a)), Box::new(self.natural(b)))
                }
                source::NatKind::Sub(a, b) => {
                    NatKind::Sub(Box::new(self.natural(a)), Box::new(self.natural(b)))
                }
                source::NatKind::Mul(a, b) => {
                    NatKind::Mul(Box::new(self.natural(a)), Box::new(self.natural(b)))
                }
            },
        }
    }
    fn predicate(&self, predicate: &source::Predicate) -> Predicate {
        Predicate {
            left: self.natural(&predicate.left),
            comparison: predicate.comparison,
            right: self.natural(&predicate.right),
        }
    }
    fn count(&self, count: &source::Count) -> Count {
        match count {
            source::Count::Natural(n) => Count::Natural(self.natural(n)),
            source::Count::Power(n) => Count::Power(self.natural(n)),
        }
    }
    fn function(&self, declaration: &source::Decl) -> Result<Function> {
        let effect = match declaration.kind {
            source::FnKind::Unitary => Effect::Unitary,
            source::FnKind::Iso => Effect::Iso,
            source::FnKind::Observe => Effect::Observe,
            _ => {
                return Err(unsupported(
                    declaration.span,
                    "requires an ordinary function",
                ));
            }
        };
        let parameters = declaration
            .static_params
            .iter()
            .map(|parameter| {
                Ok(match &parameter.kind {
                    source::StaticParamKind::Natural => {
                        Parameter::Natural(self.binding(&parameter.name))
                    }
                    source::StaticParamKind::Basis => {
                        Parameter::Basis(self.binding(&parameter.name))
                    }
                    source::StaticParamKind::Operation {
                        basis: ty,
                        meaning: None,
                    } => Parameter::Operation(self.binding(&parameter.name), self.basis(ty)?),
                    source::StaticParamKind::Operation {
                        meaning: Some(meaning),
                        ..
                    } => {
                        return Err(unsupported(
                            meaning.span,
                            "meaning-refined operation parameters are not supported",
                        ));
                    }
                })
            })
            .collect::<Result<_>>()?;
        let arguments = declaration
            .params
            .iter()
            .map(|parameter| {
                Ok((
                    self.pattern(&parameter.pattern)?,
                    self.ty(&parameter.ty)?,
                    parameter.pattern.span,
                ))
            })
            .collect::<Result<_>>()?;
        let requires = declaration
            .requires
            .iter()
            .map(|requirement| match requirement {
                source::Requirement::Predicate(predicate) => {
                    Requirement::Predicate(self.predicate(predicate))
                }
                source::Requirement::Access(access) => Requirement::Access(
                    match access.access {
                        source::Access::Apply => "Apply",
                        source::Access::Adjoint => "Adjoint",
                        source::Access::Controlled => "Controlled",
                    }
                    .into(),
                    self.ident(&access.name),
                    access.span,
                ),
            })
            .collect();
        let source::FnBody::Quantum(body) = &declaration.body else {
            return Err(unsupported(declaration.span, "requires a runtime block"));
        };
        Ok(Function {
            lexical: self.index.map(|index| Arc::new(index.table.clone())),
            name: declaration.name.text.clone(),
            effect,
            parameters,
            arguments,
            result: self.ty(&declaration.return_type)?,
            requires,
            body: self.block(body)?,
            span: declaration.span,
        })
    }

    fn basis(&self, ty: &source::Type) -> Result<Basis> {
        self.type_at(ty, crate::frontend::types::Stage::Basis)
    }
    fn ty(&self, ty: &source::Type) -> Result<Type> {
        self.type_at(ty, crate::frontend::types::Stage::Runtime)
    }
    fn type_at(&self, ty: &source::Type, stage: crate::frontend::types::Stage) -> Result<Type> {
        // Check borrowed syntax before recursive projection allocates a second
        // tree. In particular zero-width products must not evade the budget.
        let mut pending = vec![(ty, 1usize)];
        let mut nodes = 0usize;
        while let Some((node, depth)) = pending.pop() {
            if !matches!(node.kind, source::TypeKind::Q(_)) {
                nodes += 1;
            }
            if nodes > 4096 || depth > 64 {
                return Err(Error::new(
                    "limit",
                    node.span,
                    "source type exceeds 4096 nodes or depth 64",
                ));
            }
            match &node.kind {
                source::TypeKind::Tuple(fields) => {
                    if fields.len() > 64 || nodes + pending.len() + fields.len() > 4096 {
                        return Err(Error::new(
                            "limit",
                            node.span,
                            "source tuple exceeds type shape capacity",
                        ));
                    }
                    pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                }
                source::TypeKind::Q(inner) => pending.push((inner, depth + 1)),
                _ => {}
            }
        }
        crate::frontend::types::classify_source(ty, stage, &mut Projection { index: self.index })
    }
    fn pattern(&self, pattern: &source::Pattern) -> Result<Pattern> {
        Ok(match &pattern.kind {
            source::PatternKind::Name(name) => Pattern::Name(self.binding(name), name.span),
            source::PatternKind::Tuple(fields) => Pattern::Tuple(
                fields
                    .iter()
                    .map(|value| self.pattern(value))
                    .collect::<Result<_>>()?,
                pattern.span,
            ),
            source::PatternKind::Wildcard => Pattern::Wildcard(pattern.span),
        })
    }
    fn argument(&self, operation: &source::StaticOp) -> Result<Argument> {
        Ok(match &operation.kind {
            source::StaticOpKind::Type(ty) => Argument::Basis(self.basis(ty)?, operation.span),
            source::StaticOpKind::Name(name) => Argument::Natural(Natural {
                kind: NatKind::Name(self.ident(name)),
                span: name.span,
            }),
            source::StaticOpKind::Natural(n) => Argument::Natural(self.natural(n)),
            source::StaticOpKind::Specialize { name, arguments } => Argument::Definition(
                self.ident(name),
                arguments
                    .iter()
                    .map(|value| self.argument(value))
                    .collect::<Result<_>>()?,
                name.span,
            ),
            source::StaticOpKind::Repeat(count, child) => Argument::Repeat(
                self.count(count),
                Box::new(self.argument(child)?),
                operation.span,
            ),
            _ => {
                return Err(unsupported(
                    operation.span,
                    "unsupported static operation constructor",
                ));
            }
        })
    }
    fn expr(&self, expr: &source::Expr) -> Result<Expr> {
        let kind = match &expr.kind {
            source::ExprKind::Name(name) => ExprKind::Name(self.ident(name)),
            source::ExprKind::Unit => ExprKind::Unit,
            source::ExprKind::Bit(value) => ExprKind::Boolean(Boolean::Constant(*value), vec![]),
            source::ExprKind::Not(input) => {
                ExprKind::Boolean(Boolean::Not, vec![self.expr(input)?])
            }
            source::ExprKind::And(left, right) | source::ExprKind::Xor(left, right) => {
                ExprKind::Boolean(
                    if matches!(expr.kind, source::ExprKind::And(..)) {
                        Boolean::And
                    } else {
                        Boolean::Xor
                    },
                    vec![self.expr(left)?, self.expr(right)?],
                )
            }
            source::ExprKind::Tuple(fields) => ExprKind::Tuple(
                fields
                    .iter()
                    .map(|value| self.expr(value))
                    .collect::<Result<_>>()?,
            ),
            source::ExprKind::Call {
                callee,
                static_args,
                args,
            } => ExprKind::Call(
                self.ident(callee),
                static_args
                    .iter()
                    .map(|value| self.argument(value))
                    .collect::<Result<_>>()?,
                args.iter()
                    .map(|value| self.expr(value))
                    .collect::<Result<_>>()?,
            ),
            source::ExprKind::Adjoint { operation, input } => {
                ExprKind::Adjoint(self.argument(operation)?, Box::new(self.expr(input)?))
            }
            source::ExprKind::Controlled { operation, args } => ExprKind::Controlled(
                self.argument(operation)?,
                args.iter()
                    .map(|value| self.expr(value))
                    .collect::<Result<_>>()?,
            ),
            source::ExprKind::StaticIf {
                predicate,
                then_branch,
                else_branch,
            } => ExprKind::If(
                self.predicate(predicate),
                self.block(then_branch)?,
                self.block(else_branch)?,
            ),
            source::ExprKind::StaticFold {
                index,
                start,
                end,
                carry,
                initial,
                body,
            } => ExprKind::Fold {
                index: self.binding(index),
                start: self.natural(start),
                end: self.natural(end),
                carry: self.pattern(carry)?,
                initial: Box::new(self.expr(initial)?),
                body: self.block(body)?,
            },
            _ => return Err(unsupported(expr.span, "unsupported runtime expression")),
        };
        Ok(Expr {
            kind,
            span: expr.span,
        })
    }
    fn block(&self, block: &source::Block) -> Result<Block> {
        let statements = block
            .statements
            .iter()
            .map(|statement| {
                Ok(match &statement.kind {
                    source::StmtKind::Let {
                        pattern: binder,
                        value,
                    } => Statement::Let(self.pattern(binder)?, self.expr(value)?),
                    source::StmtKind::Expr(value) => Statement::Drop(self.expr(value)?),
                })
            })
            .collect::<Result<_>>()?;
        Ok(Block {
            statements,
            result: Box::new(self.expr(&block.result)?),
            span: block.span,
        })
    }
}

impl crate::frontend::types::SourceTypeContext for Projection<'_, '_> {
    type Size = Natural;
    type Error = Error;
    fn resolve_size(&mut self, size: &source::Natural) -> Result<Natural> {
        Ok(self.natural(size))
    }
    fn resolve_basis(&mut self, name: &source::Ident) -> Result<Type> {
        let reference = self.ident(name);
        if let Some(index) = self.index {
            let usage = index.table.usage(reference.site.unwrap());
            if !matches!(usage.target, ResolvedUse::Local(id) if index.table.binder(id).kind == crate::frontend::resolve::locals::BindingKind::StaticBasis)
            {
                return Err(Error::new(
                    "type",
                    name.span,
                    format!("{} names no Basis parameter", name.text),
                ));
            }
        }
        Ok(Type::parameter(crate::frontend::types::TypeParameter {
            key: reference.local,
            name: name.text.clone(),
            span: name.span,
        }))
    }
    fn quantum_basis_error(&mut self, span: Span) -> Error {
        Error::new(
            "type",
            span,
            "a quantum basis must be an ordinary finite type; nested Q owners are invalid",
        )
    }
    fn checked_node(
        &mut self,
        source: &source::Type,
        stage: crate::frontend::types::Stage,
        ty: &Type,
    ) -> Result<()> {
        if stage == crate::frontend::types::Stage::Basis
            && ty.tuple_fields().is_some_and(|fields| fields.len() < 2)
        {
            return Err(unsupported(
                source.span,
                "quantum tuple basis requires at least two fields",
            ));
        }
        Ok(())
    }
}
