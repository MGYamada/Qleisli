use super::*;

#[derive(Clone, Debug)]
pub(super) struct BasisValue {
    pub ty: Ty,
    pub label: u16,
}

impl Compiler<'_> {
    pub(super) fn compile_basis(&mut self, key: &Key) -> Result<BasisFunction, CompileError> {
        let decl = self.declarations[key];
        let (params, result) = self.signature(key)?;
        let bits: usize = params
            .iter()
            .map(|ty| ty.basis_bits().expect("basis parameter"))
            .sum();
        if bits > MAX_BITS {
            return Err(self.error(
                &key.0,
                decl.span,
                ErrorCode::Limit,
                "basis function domain exceeds 12 bits",
            ));
        }
        let FnBody::Basis(body) = &decl.body else {
            unreachable!("basis declaration")
        };
        let mut table = Vec::new();
        for label in 0..(1u16 << bits) {
            let mut env = BTreeMap::new();
            let mut offset = 0;
            for (param, ty) in decl.params.iter().zip(&params) {
                let width = ty.basis_bits().expect("basis type");
                env.insert(
                    param.name.text.clone(),
                    BasisValue {
                        ty: ty.clone(),
                        label: (label >> offset) & ((1 << width) - 1),
                    },
                );
                offset += width;
            }
            let value = self.eval_basis(&key.0, body, &env, 0)?;
            if value.ty != result {
                return Err(self.error(
                    &key.0,
                    body.span,
                    ErrorCode::TypeMismatch,
                    "basis result does not match its declared type",
                ));
            }
            table.push(value.label);
        }
        Ok(BasisFunction {
            params,
            result,
            table,
        })
    }

    pub(super) fn eval_basis(
        &mut self,
        module: &str,
        expr: &BasisExpr,
        env: &BTreeMap<String, BasisValue>,
        depth: usize,
    ) -> Result<BasisValue, CompileError> {
        self.tick(module, expr.span)?;
        if depth >= MAX_DEPTH {
            return Err(self.error(
                module,
                expr.span,
                ErrorCode::Limit,
                "basis evaluation exceeds the initial depth limit",
            ));
        }
        let value = match &expr.kind {
            BasisExprKind::Name(name) => env.get(&name.text).cloned().ok_or_else(|| {
                self.error(
                    module,
                    name.span,
                    ErrorCode::UnknownName,
                    format!("unknown basis value `{}`", name.text),
                )
            })?,
            BasisExprKind::Bit(bit) => BasisValue {
                ty: Ty::Bit,
                label: u16::from(*bit),
            },
            BasisExprKind::Unit => BasisValue {
                ty: Ty::Unit,
                label: 0,
            },
            BasisExprKind::Tuple(a, b) => {
                let a = self.eval_basis(module, a, env, depth + 1)?;
                let b = self.eval_basis(module, b, env, depth + 1)?;
                let a_bits = a.ty.basis_bits().expect("basis value");
                let b_bits = b.ty.basis_bits().expect("basis value");
                if a_bits + b_bits > MAX_BITS {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::Limit,
                        "basis result exceeds 12 bits",
                    ));
                }
                BasisValue {
                    ty: Ty::pair(a.ty, b.ty),
                    label: a.label | (b.label << a_bits),
                }
            }
            BasisExprKind::Not(a) => {
                let a = self.eval_basis(module, a, env, depth + 1)?;
                self.require_bit(module, expr.span, &a)?;
                BasisValue {
                    ty: Ty::Bit,
                    label: a.label ^ 1,
                }
            }
            BasisExprKind::Xor(a, b) | BasisExprKind::And(a, b) => {
                let a = self.eval_basis(module, a, env, depth + 1)?;
                let b = self.eval_basis(module, b, env, depth + 1)?;
                self.require_bit(module, expr.span, &a)?;
                self.require_bit(module, expr.span, &b)?;
                let label = if matches!(expr.kind, BasisExprKind::Xor(..)) {
                    a.label ^ b.label
                } else {
                    a.label & b.label
                };
                BasisValue { ty: Ty::Bit, label }
            }
            BasisExprKind::Call { callee, args } => {
                if env.contains_key(&callee.text) {
                    return Err(self.error(
                        module,
                        callee.span,
                        ErrorCode::TypeMismatch,
                        "a basis value is not callable",
                    ));
                }
                let Callee::User(key) = self.resolve(module, callee)? else {
                    return Err(self.error(
                        module,
                        callee.span,
                        ErrorCode::TypeMismatch,
                        "quantum operation in a basis expression",
                    ));
                };
                let function = self.basis.get(&key).ok_or_else(|| {
                    self.error(
                        module,
                        callee.span,
                        ErrorCode::TypeMismatch,
                        "basis expressions may call only basis functions",
                    )
                })?;
                let params = function.params.clone();
                let result = function.result.clone();
                if args.len() != params.len() {
                    return Err(self.error(
                        module,
                        expr.span,
                        ErrorCode::Arity,
                        "basis argument count does not match",
                    ));
                }
                let mut label = 0;
                let mut offset = 0;
                for (arg, ty) in args.iter().zip(&params) {
                    let value = self.eval_basis(module, arg, env, depth + 1)?;
                    if value.ty != *ty {
                        return Err(self.error(
                            module,
                            arg.span,
                            ErrorCode::TypeMismatch,
                            "basis argument type does not match",
                        ));
                    }
                    label |= usize::from(value.label) << offset;
                    offset += ty.basis_bits().expect("basis parameter");
                }
                BasisValue {
                    ty: result,
                    label: self.basis[&key].table[label],
                }
            }
        };
        Ok(value)
    }

    fn require_bit(
        &self,
        module: &str,
        span: Span,
        value: &BasisValue,
    ) -> Result<(), CompileError> {
        if value.ty == Ty::Bit {
            Ok(())
        } else {
            Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "not/xor/and require Bit operands",
            ))
        }
    }
}
