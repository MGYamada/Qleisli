//! Temporary projection of the single common AST into the sized checker profile.
//!
//! This module never reads source text or tokens. Its located rejections are
//! profile restrictions, not a competing grammar or verification authority.
use super::ast::*;
use super::{Error, Result, Span};
use crate::frontend::ast as source;

fn unsupported(span: Span, message: &str) -> Error {
    Error::new(
        "unsupported",
        span,
        format!("sized preparation profile: {message}"),
    )
}

pub(super) fn project(module: &source::Module) -> Result<Module> {
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
                source::StaticParamKind::Natural => Parameter::Natural(parameter.name.text.clone()),
                source::StaticParamKind::Operation {
                    basis: ty,
                    meaning: None,
                } => Parameter::Operation(parameter.name.text.clone(), basis(ty)?),
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
            Ok((name.text.clone(), ty(&parameter.ty)?, name.span))
        })
        .collect::<Result<_>>()?;
    let requires = declaration
        .requires
        .iter()
        .map(|requirement| match requirement {
            source::Requirement::Predicate(predicate) => Requirement::Predicate(predicate.clone()),
            source::Requirement::Access(access) => Requirement::Access(
                match access.access {
                    source::Access::Apply => "Apply",
                    source::Access::Adjoint => "Adjoint",
                    source::Access::Controlled => "Controlled",
                }
                .into(),
                access.name.text.clone(),
                access.span,
            ),
        })
        .collect();
    let source::FnBody::Quantum(body) = &declaration.body else {
        return Err(unsupported(declaration.span, "requires a runtime block"));
    };
    Ok(Module {
        function: Function {
            name: declaration.name.text.clone(),
            effect,
            parameters,
            arguments,
            result: ty(&declaration.return_type)?,
            requires,
            body: block(body)?,
            span: declaration.span,
        },
    })
}

fn basis(ty: &source::Type) -> Result<Basis> {
    match &ty.kind {
        source::TypeKind::Bit => Ok(Basis::Bit),
        source::TypeKind::Bits(n) => Ok(Basis::Bits(n.clone())),
        _ => Err(unsupported(
            ty.span,
            "operation/quantum basis must be Bit or Bits<n>",
        )),
    }
}
fn ty(ty: &source::Type) -> Result<Type> {
    Ok(match &ty.kind {
        source::TypeKind::Q(inner) => Type::Quantum(basis(inner)?),
        source::TypeKind::CBit => Type::CBit,
        source::TypeKind::CBits(n) => Type::CBits(n.clone()),
        source::TypeKind::Tuple(fields) => {
            Type::Tuple(fields.iter().map(self::ty).collect::<Result<_>>()?)
        }
        _ => return Err(unsupported(ty.span, "unsupported runtime type")),
    })
}
fn pattern(pattern: &source::Pattern) -> Result<Pattern> {
    Ok(match &pattern.kind {
        source::PatternKind::Name(name) => Pattern::Name(name.text.clone(), name.span),
        source::PatternKind::Tuple(fields) => Pattern::Tuple(
            fields.iter().map(self::pattern).collect::<Result<_>>()?,
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
fn argument(operation: &source::StaticOp) -> Result<Argument> {
    Ok(match &operation.kind {
        source::StaticOpKind::Name(name) => Argument::Natural(Natural {
            kind: NatKind::Name(name.text.clone()),
            span: name.span,
            depth: 1,
        }),
        source::StaticOpKind::Natural(n) => Argument::Natural(n.clone()),
        source::StaticOpKind::Specialize { name, arguments } => Argument::Definition(
            name.text.clone(),
            arguments.iter().map(argument).collect::<Result<_>>()?,
            name.span,
        ),
        source::StaticOpKind::Repeat(count, child) => {
            Argument::Repeat(count.clone(), Box::new(argument(child)?), operation.span)
        }
        _ => {
            return Err(unsupported(
                operation.span,
                "unsupported static operation constructor",
            ));
        }
    })
}
fn expr(expr: &source::Expr) -> Result<Expr> {
    let kind = match &expr.kind {
        source::ExprKind::Name(name) => ExprKind::Name(name.text.clone()),
        source::ExprKind::Unit => ExprKind::Tuple(vec![]),
        source::ExprKind::Tuple(fields) => {
            ExprKind::Tuple(fields.iter().map(self::expr).collect::<Result<_>>()?)
        }
        source::ExprKind::Call {
            callee,
            static_args,
            args,
        } => ExprKind::Call(
            callee.text.clone(),
            static_args.iter().map(argument).collect::<Result<_>>()?,
            args.iter().map(self::expr).collect::<Result<_>>()?,
        ),
        source::ExprKind::Adjoint { operation, input } => {
            ExprKind::Adjoint(argument(operation)?, Box::new(self::expr(input)?))
        }
        source::ExprKind::Controlled { operation, args } => ExprKind::Controlled(
            argument(operation)?,
            args.iter().map(self::expr).collect::<Result<_>>()?,
        ),
        source::ExprKind::StaticIf {
            predicate,
            then_branch,
            else_branch,
        } => ExprKind::If(predicate.clone(), block(then_branch)?, block(else_branch)?),
        source::ExprKind::StaticFold {
            index,
            start,
            end,
            carry,
            initial,
            body,
        } => ExprKind::Fold {
            index: index.text.clone(),
            start: start.clone(),
            end: end.clone(),
            carry: pattern(carry)?,
            initial: Box::new(self::expr(initial)?),
            body: block(body)?,
        },
        _ => return Err(unsupported(expr.span, "unsupported runtime expression")),
    };
    Ok(Expr {
        kind,
        span: expr.span,
    })
}
fn block(block: &source::Block) -> Result<Block> {
    let statements = block
        .statements
        .iter()
        .map(|statement| {
            Ok(match &statement.kind {
                source::StmtKind::Let {
                    pattern: binder,
                    value,
                } => Statement::Let(pattern(binder)?, expr(value)?),
                source::StmtKind::Expr(value) => Statement::Drop(expr(value)?),
            })
        })
        .collect::<Result<_>>()?;
    Ok(Block {
        statements,
        result: Box::new(expr(&block.result)?),
        span: block.span,
    })
}
