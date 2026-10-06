//! Temporary projection of the single common AST into the sized checker profile.
//!
//! This module never reads source text or tokens. Its located rejections are
//! profile restrictions, not a competing grammar or verification authority.
use super::ast::*;
use super::{Error, Result, Span};
use crate::frontend::ast as source;
use crate::frontend::check::{Budget, StaticHelpers};
use crate::frontend::resolve::Target;
use crate::frontend::resolve::locals::{Index, UseSiteId};

fn unsupported(span: Span, message: &str) -> Error {
    Error::new(
        "unsupported",
        span,
        format!("sized preparation profile: {message}"),
    )
}

pub(super) fn project_declaration(
    declaration: &source::Decl,
    index: &Index<'_>,
    helpers: &StaticHelpers,
    budget: &Budget,
) -> Result<Function> {
    Projection {
        index,
        helpers,
        budget,
    }
    .function(declaration)
}

struct Projection<'a, 'ast> {
    helpers: &'a StaticHelpers,
    index: &'a Index<'ast>,
    budget: &'a Budget,
}
impl Projection<'_, '_> {
    fn charge(&self, span: Span, cells: usize) -> Result<()> {
        self.budget.sized_charge(span, cells)
    }
    fn binding(&self, name: &source::Ident) -> Result<BindingName> {
        let info = self.index.table.binder(self.index.binder(name));
        self.charge(
            name.span,
            2 + name.text.len()
                + info.key.name.len()
                + info
                    .shadowed
                    .map_or(0, |id| 1 + self.index.table.key(id).name.len()),
        )?;
        Ok(BindingName {
            name: name.text.clone(),
            key: Some(info.key.clone()),
            shadowed: info.shadowed.map(|id| self.index.table.key(id).clone()),
        })
    }
    fn reference(&self, name: &str, site: UseSiteId) -> Result<Reference> {
        let local = match self.index.table.usage(site).target {
            ResolvedUse::Local(id) => Some(self.index.table.key(id)),
            ResolvedUse::Global(_) | ResolvedUse::Unresolved => None,
        };
        self.charge(
            self.index.table.usage(site).span,
            1 + name.len() + local.map_or(0, |key| 1 + key.name.len()),
        )?;
        Ok(Reference {
            name: name.into(),
            site: Some(site),
            local: local.cloned(),
        })
    }
    fn ident(&self, name: &source::Ident) -> Result<Reference> {
        self.reference(&name.text, self.index.usage(name))
    }
    fn natural(&self, natural: &source::Natural) -> Result<Natural> {
        self.charge(natural.span, 1)?;
        Ok(Natural {
            span: natural.span,
            kind: match &natural.kind {
                source::NatKind::Call { callee, arguments } => {
                    let ResolvedUse::Global(Target::Declaration(id)) =
                        self.index.table.usage(self.index.usage(callee)).target
                    else {
                        return Err(unsupported(
                            callee.span,
                            "requires a checked static Nat helper",
                        ));
                    };
                    let helper = self.helpers.get(&id).ok_or_else(|| {
                        unsupported(callee.span, "requires a checked static Nat helper")
                    })?;
                    self.charge(natural.span, 1 + arguments.len())?;
                    NatKind::Helper {
                        template: std::sync::Arc::clone(helper),
                        arguments: arguments
                            .iter()
                            .map(|n| self.natural(n))
                            .collect::<Result<_>>()?,
                    }
                }
                source::NatKind::Number(n) => NatKind::Number(*n),
                source::NatKind::Name(name) => {
                    NatKind::Name(self.reference(name, self.index.natural_usage(natural))?)
                }
                source::NatKind::Add(a, b) => {
                    NatKind::Add(Box::new(self.natural(a)?), Box::new(self.natural(b)?))
                }
                source::NatKind::Sub(a, b) => {
                    NatKind::Sub(Box::new(self.natural(a)?), Box::new(self.natural(b)?))
                }
                source::NatKind::Mul(a, b) => {
                    NatKind::Mul(Box::new(self.natural(a)?), Box::new(self.natural(b)?))
                }
            },
        })
    }
    fn predicate(&self, predicate: &source::Predicate) -> Result<Predicate> {
        self.charge(predicate.left.span, 1)?;
        Ok(Predicate {
            left: self.natural(&predicate.left)?,
            comparison: predicate.comparison,
            right: self.natural(&predicate.right)?,
        })
    }
    fn count(&self, count: &source::Count) -> Result<Count> {
        let (source::Count::Natural(n) | source::Count::Power(n)) = count;
        self.charge(n.span, 1)?;
        Ok(match count {
            source::Count::Natural(n) => Count::Natural(self.natural(n)?),
            source::Count::Power(n) => Count::Power(self.natural(n)?),
        })
    }
    fn function(&self, declaration: &source::Decl) -> Result<Function> {
        self.charge(declaration.span, 1)?;
        match declaration.kind {
            source::FnKind::Unitary
            | source::FnKind::Iso
            | source::FnKind::Observe
            | source::FnKind::Inferred
            | source::FnKind::Classical => {}
            _ => {
                return Err(unsupported(
                    declaration.span,
                    "requires an ordinary function",
                ));
            }
        };
        if let Some(meaning) =
            declaration
                .static_params
                .iter()
                .find_map(|parameter| match &parameter.kind {
                    source::StaticParamKind::Operation {
                        meaning: Some(meaning),
                        ..
                    } => Some(meaning),
                    _ => None,
                })
        {
            return Err(unsupported(
                meaning.span,
                "meaning-refined operation parameters are not supported",
            ));
        }
        self.charge(declaration.span, declaration.params.len())?;
        let arguments = declaration
            .params
            .iter()
            .map(|parameter| Ok((self.pattern(&parameter.pattern)?, parameter.pattern.span)))
            .collect::<Result<_>>()?;
        let body = match &declaration.body {
            source::FnBody::Quantum(body) => self.block(body)?,
            source::FnBody::Basis(body) if declaration.kind == source::FnKind::Classical => {
                self.charge(body.span, 2)?;
                Block {
                    statements: vec![],
                    result: Box::new(self.classical_expression(body)?),
                    span: body.span,
                }
            }
            _ => return Err(unsupported(declaration.span, "requires a runtime block")),
        };
        Ok(Function {
            lexical: None,           // Attach the one authoritative Arc<Table> after finish.
            effect: Effect::Unitary, // Private typed-pass placeholder, never published.
            arguments,
            body,
            span: declaration.span,
        })
    }

    fn classical_expression(&self, expression: &source::BasisExpr) -> Result<Expr> {
        use crate::frontend::ordinary::RuntimeExpression;

        // The shared view borrows original identifiers: occurrence lookup must
        // keep their addresses rather than resolve names in a copied AST.
        self.charge(expression.span, 1)?;
        let kind = match crate::frontend::ordinary::runtime_expression(expression) {
            RuntimeExpression::Name(name) => ExprKind::Name(self.ident(name)?),
            RuntimeExpression::Unit => ExprKind::Unit,
            RuntimeExpression::Tuple(fields) => {
                self.charge(expression.span, fields.len())?;
                ExprKind::Tuple(
                    fields
                        .iter()
                        .map(|field| self.classical_expression(field))
                        .collect::<Result<_>>()?,
                )
            }
            RuntimeExpression::Call { callee, args } => {
                self.charge(expression.span, args.len())?;
                ExprKind::Call(
                    self.ident(callee)?,
                    vec![],
                    args.iter()
                        .map(|argument| self.classical_expression(argument))
                        .collect::<Result<_>>()?,
                )
            }
            RuntimeExpression::Boolean { operation, inputs } => {
                self.charge(expression.span, operation.arity())?;
                ExprKind::Boolean(
                    operation,
                    inputs
                        .into_iter()
                        .flatten()
                        .map(|input| self.classical_expression(input))
                        .collect::<Result<_>>()?,
                )
            }
        };
        Ok(Expr {
            kind,
            span: expression.span,
        })
    }

    fn basis(&self, ty: &source::Type) -> Result<Basis> {
        self.type_at(ty, crate::frontend::types::Stage::Basis)
    }
    fn type_at(&self, ty: &source::Type, stage: crate::frontend::types::Stage) -> Result<Type> {
        // Check borrowed syntax before recursive projection allocates a second
        // tree. In particular zero-width products must not evade the budget.
        self.charge(ty.span, 1)?;
        let mut pending = vec![(ty, 1usize)];
        let mut nodes = 0usize;
        while let Some((node, depth)) = pending.pop() {
            self.charge(node.span, 2)?; // Borrowed visit and resulting type cell.
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
                    self.charge(node.span, fields.len())?;
                    pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                }
                source::TypeKind::Q(inner) => {
                    self.charge(node.span, 1)?;
                    pending.push((inner, depth));
                }
                _ => {}
            }
        }
        crate::frontend::types::classify_source(
            ty,
            stage,
            &mut Projection {
                index: self.index,
                helpers: self.helpers,
                budget: self.budget,
            },
        )
    }
    fn pattern(&self, pattern: &source::Pattern) -> Result<Pattern> {
        self.charge(pattern.span, 1)?;
        Ok(match &pattern.kind {
            source::PatternKind::Name(name) => Pattern::Name(self.binding(name)?, name.span),
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
        self.charge(operation.span, 1)?;
        Ok(match &operation.kind {
            source::StaticOpKind::Type(ty) => Argument::Basis(self.basis(ty)?, operation.span),
            source::StaticOpKind::Name(name) => Argument::Natural(Natural {
                kind: NatKind::Name(self.ident(name)?),
                span: name.span,
            }),
            source::StaticOpKind::Natural(n) => Argument::Natural(self.natural(n)?),
            source::StaticOpKind::Specialize { name, arguments } => Argument::Definition(
                self.ident(name)?,
                arguments
                    .iter()
                    .map(|value| self.argument(value))
                    .collect::<Result<_>>()?,
                name.span,
            ),
            source::StaticOpKind::Repeat(count, child) => Argument::Repeat(
                self.count(count)?,
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
        self.charge(expr.span, 1)?;
        let kind = match &expr.kind {
            source::ExprKind::Name(name) => ExprKind::Name(self.ident(name)?),
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
                self.ident(callee)?,
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
                self.predicate(predicate)?,
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
                index: self.binding(index)?,
                start: self.natural(start)?,
                end: self.natural(end)?,
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
        self.charge(block.span, 1)?;
        let statements = block
            .statements
            .iter()
            .map(|statement| {
                self.charge(statement.span, 1)?;
                Ok(match &statement.kind {
                    source::StmtKind::StaticLet { name, value } => {
                        Statement::StaticLet(self.binding(name)?, self.natural(value)?)
                    }
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
        self.natural(size)
    }
    fn resolve_basis(&mut self, name: &source::Ident) -> Result<Type> {
        let reference = self.ident(name)?;
        {
            let index = self.index;
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
        self.charge(name.span, 1 + name.text.len())?;
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
