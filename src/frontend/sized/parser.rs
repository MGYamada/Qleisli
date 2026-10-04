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

pub(super) fn project(module: &source::Module, index: Option<&Index<'_>>) -> Result<Module> {
    Projection { index }.module(module)
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
    fn module(&self, module: &source::Module) -> Result<Module> {
        if module.decls.len() != 1 {
            return Err(unsupported(
                module.decls.get(1).map_or(module.span, |d| d.span),
                "permits one function per module until declaration-identity cycle checking is available",
            ));
        }
        let declaration = &module.decls[0];
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
                let source::PatternKind::Name(name) = &parameter.pattern.kind else {
                    return Err(unsupported(
                        parameter.pattern.span,
                        "function parameters must be names",
                    ));
                };
                Ok((self.binding(name), self.ty(&parameter.ty)?, name.span))
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
        Ok(Module {
            function: Function {
                lexical: self.index.map(|index| Arc::new(index.table.clone())),
                name: declaration.name.text.clone(),
                effect,
                parameters,
                arguments,
                result: self.ty(&declaration.return_type)?,
                requires,
                body: self.block(body)?,
                span: declaration.span,
            },
        })
    }

    fn basis(&self, ty: &source::Type) -> Result<Basis> {
        match &ty.kind {
            source::TypeKind::Bit => Ok(Basis::Bit),
            source::TypeKind::Bits(n) => Ok(Basis::Bits(self.natural(n))),
            _ => Err(unsupported(
                ty.span,
                "operation/quantum basis must be Bit or Bits<n>",
            )),
        }
    }
    fn ty(&self, ty: &source::Type) -> Result<Type> {
        Ok(match &ty.kind {
            source::TypeKind::Q(inner) => Type::Quantum(self.basis(inner)?),
            source::TypeKind::CBit => Type::CBit,
            source::TypeKind::CBits(n) => Type::CBits(self.natural(n)),
            source::TypeKind::Tuple(fields) => Type::Tuple(
                fields
                    .iter()
                    .map(|value| self.ty(value))
                    .collect::<Result<_>>()?,
            ),
            _ => return Err(unsupported(ty.span, "unsupported runtime type")),
        })
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
            source::PatternKind::Wildcard => {
                return Err(unsupported(
                    pattern.span,
                    "implicit wildcard discard is unsupported",
                ));
            }
        })
    }
    fn argument(&self, operation: &source::StaticOp) -> Result<Argument> {
        Ok(match &operation.kind {
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
            source::ExprKind::Unit => ExprKind::Tuple(vec![]),
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
