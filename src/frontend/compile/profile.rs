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
            StaticParamKind::Basis | StaticParamKind::Natural => {}
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
        // Full instance closure validates every actual (including unused
        // Basis values), original Nat roots and the existing finite limits.
        TypeKind::Named(_) | TypeKind::Bits(_) => {}
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
        StaticOpKind::Type(_) | StaticOpKind::Natural(_) => {}
        StaticOpKind::Specialize { arguments, .. } => {
            for argument in arguments {
                self::operation(argument)?;
            }
        }
        StaticOpKind::Repeat(_, child) => {
            // The original ordinary-u32 count is checked even for a dormant
            // or zero-count child; no AST rewriting supplies a literal.
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
        ExprKind::Variant(_)
        | ExprKind::Record(_)
        | ExprKind::Field { .. }
        | ExprKind::Match(_) => {
            return Err((
                expr.span,
                "ordinary nominal values require their typed native transport",
            ));
        }
        ExprKind::UnsupportedClosure(_) => {
            return Err((expr.span, "runtime closure values are unsupported"));
        }
        ExprKind::StaticIf {
            then_branch,
            else_branch,
            ..
        } => {
            block(then_branch)?;
            block(else_branch)?;
        }
        ExprKind::StaticFold { initial, body, .. } => {
            self::expr(initial)?;
            block(body)?;
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
