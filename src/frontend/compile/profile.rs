//! Reject common syntax not implemented by the finite lowering profile.
//! This is a source-profile boundary, not semantic acceptance.
use super::*;

type Failure = (Span, &'static str);
pub(super) fn check(declaration: &Decl, interface: &Interface) -> Result<(), Failure> {
    assert_eq!(declaration.static_params.len(), interface.statics.len());
    assert_eq!(declaration.params.len(), interface.params.len());
    if let Some(domain) = &declaration.meaning_domain {
        ty(domain, interface.meaning_input())?;
    }
    for (parameter, formal) in declaration.static_params.iter().zip(&interface.statics) {
        match &parameter.kind {
            StaticParamKind::Basis => {
                return Err((
                    parameter.name.span,
                    "finite profile does not support opaque Basis parameters",
                ));
            }
            StaticParamKind::Natural => {
                return Err((
                    parameter.name.span,
                    "finite profile does not support static Nat parameters",
                ));
            }
            StaticParamKind::Operation {
                basis, codomain, ..
            } => {
                let StaticKind::Operation {
                    basis: checked_basis,
                    codomain: checked_codomain,
                    ..
                } = &formal.kind
                else {
                    unreachable!("checked finite static category differs")
                };
                ty(basis, checked_basis)?;
                if let Some(codomain) = codomain {
                    ty(
                        codomain,
                        // Common checking canonicalizes A -> A to its
                        // endomorphic form while retaining the original span.
                        checked_codomain.as_ref().unwrap_or(checked_basis),
                    )?;
                }
            }
        }
    }
    for requirement in &declaration.requires {
        if let Requirement::Predicate(p) = requirement {
            return Err((
                p.left.span.cover(p.right.span),
                "finite profile does not support size predicates",
            ));
        }
        if declaration.static_params.is_empty() {
            return Err((
                declaration.span,
                "requires needs static parameters in the finite profile",
            ));
        }
    }
    for (parameter, checked) in declaration.params.iter().zip(&interface.params) {
        ty(&parameter.ty, checked)?;
    }
    ty(&declaration.return_type, &interface.result)?;
    if let FnBody::Quantum(body) = &declaration.body {
        block(body)?;
    }
    Ok(())
}
fn ty(ty: &Type, checked: &check::Ty) -> Result<(), Failure> {
    match &ty.kind {
        TypeKind::Named(_) => {
            return Err((
                ty.span,
                "named Basis types are outside the finite lowering profile",
            ));
        }
        TypeKind::Bits(_) => match &checked.kind {
            Kind::Bits(size) if size.is_exact_zero() => {}
            Kind::Bits(_) => {
                return Err((
                    ty.span,
                    "nonzero register types are outside the finite lowering profile; only Bits<0> is supported",
                ));
            }
            _ => unreachable!("checked register constructor differs"),
        },
        TypeKind::Tuple(fields) => {
            if fields.is_empty() {
                return Err((
                    ty.span,
                    "empty tuple type syntax is outside the finite profile; use Unit",
                ));
            }
            let Kind::Tuple(checked) = &checked.kind else {
                unreachable!("checked tuple constructor differs")
            };
            assert_eq!(fields.len(), checked.len(), "checked tuple arity");
            for (field, checked) in fields.iter().zip(checked) {
                self::ty(field, checked)?;
            }
        }
        TypeKind::Q(inner) => {
            let Kind::Q(checked) = &checked.kind else {
                unreachable!("checked quantum constructor differs")
            };
            self::ty(inner, checked)?;
        }
        _ => {}
    }
    Ok(())
}
fn operation(operation: &StaticOp) -> Result<(), Failure> {
    match &operation.kind {
        StaticOpKind::Type(_) | StaticOpKind::Natural(_) | StaticOpKind::Specialize { .. } => {
            return Err((
                operation.span,
                "static argument is outside the finite lowering profile",
            ));
        }
        StaticOpKind::Repeat(count, child) => {
            if !matches!(
                count,
                Count::Natural(Natural {
                    kind: NatKind::Number(0..=4096),
                    ..
                })
            ) {
                return Err((
                    operation.span,
                    "finite repetition requires a literal count in 0..=4096",
                ));
            }
            self::operation(child)?;
        }
        StaticOpKind::Inverse(a) | StaticOpKind::Controlled(a) => self::operation(a)?,
        StaticOpKind::Then(a, b) | StaticOpKind::Tensor(a, b) | StaticOpKind::Conjugate(a, b) => {
            self::operation(a)?;
            self::operation(b)?;
        }
        _ => {}
    }
    Ok(())
}
fn block(block: &Block) -> Result<(), Failure> {
    if block.implicit_result {
        return Err((
            block.result.span,
            "finite profile requires an explicit final expression",
        ));
    }
    for statement in &block.statements {
        match &statement.kind {
            StmtKind::StaticLet { .. } => {}
            StmtKind::MutableLet { .. } | StmtKind::Assign { .. } => {
                return Err((
                    statement.span,
                    "mutable bindings and place assignment are unsupported",
                ));
            }
            StmtKind::Let { value, .. } => expr(value)?,
            StmtKind::Expr(value) => expr(value)?,
        }
    }
    expr(&block.result)
}
fn expr(expr: &Expr) -> Result<(), Failure> {
    match &expr.kind {
        ExprKind::UnsupportedClosure(_) => {
            return Err((expr.span, "runtime closure values are unsupported"));
        }
        ExprKind::StaticIf { .. } | ExprKind::StaticFold { .. } => {
            return Err((
                expr.span,
                "expression is outside the finite lowering profile",
            ));
        }
        ExprKind::Controlled {
            operation: op,
            args,
        } => {
            operation(op)?;
            for arg in args {
                self::expr(arg)?;
            }
        }
        ExprKind::ApplyStatic {
            operation: op,
            input,
        } => {
            operation(op)?;
            self::expr(input)?;
        }
        ExprKind::Adjoint {
            operation: op,
            input,
        } => {
            operation(op)?;
            self::expr(input)?;
        }
        ExprKind::CoherentLift { input, .. } => self::expr(input)?,
        ExprKind::ApplyContract { input, .. }
        | ExprKind::RepeatStatic { input, .. }
        | ExprKind::Not(input) => self::expr(input)?,
        ExprKind::Tuple(fields) => {
            for field in fields {
                self::expr(field)?;
            }
        }
        ExprKind::And(a, b)
        | ExprKind::Xor(a, b)
        | ExprKind::QuantumIf {
            control: a,
            target: b,
            ..
        } => {
            self::expr(a)?;
            self::expr(b)?;
        }
        ExprKind::Call {
            static_args, args, ..
        } => {
            for op in static_args {
                operation(op)?;
            }
            for arg in args {
                self::expr(arg)?;
            }
        }
        ExprKind::AccessCall {
            static_args, args, ..
        } => {
            for op in static_args {
                operation(op)?;
            }
            for arg in args {
                if arg.selection.is_some() {
                    return Err((
                        arg.value.span,
                        "finite profile does not yet lower indexed quantum access",
                    ));
                }
                self::expr(&arg.value)?;
            }
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            self::expr(condition)?;
            block(then_branch)?;
            block(else_branch)?;
        }
        ExprKind::WithComputed { source, body, .. }
        | ExprKind::CertifiedComputed { source, body, .. } => {
            self::expr(source)?;
            block(body)?;
        }
        ExprKind::Name(_) | ExprKind::Unit | ExprKind::Bit(_) => {}
    }
    Ok(())
}
