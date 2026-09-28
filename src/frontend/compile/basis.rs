use super::*;

#[derive(Clone, Debug)]
pub(super) struct BasisValue {
    pub ty: Ty,
    pub label: u16,
}

impl Compiler<'_> {
    /// Bind one finite label through the exact product tree. Wildcards omit
    /// basis information only; the complete lift still checks injectivity.
    pub(super) fn bind_basis_pattern(
        &mut self,
        module: &str,
        pattern: &Pattern,
        ty: &Ty,
        label: u16,
    ) -> Result<BTreeMap<String, BasisValue>, CompileError> {
        let mut env = BTreeMap::new();
        let mut pending = vec![(pattern, ty, label)];
        while let Some((pattern, ty, label)) = pending.pop() {
            self.tick(module, pattern.span)?;
            match &pattern.kind {
                PatternKind::Name(name) => {
                    if env.contains_key(&name.text) {
                        return Err(self.error(
                            module,
                            name.span,
                            ErrorCode::Ownership,
                            "duplicate name in a basis binding pattern",
                        ));
                    }
                    self.charge(module, pattern.span, ty.tree_size().nodes)?;
                    env.insert(
                        name.text.clone(),
                        BasisValue {
                            ty: ty.clone(),
                            label,
                        },
                    );
                }
                PatternKind::Wildcard => {}
                PatternKind::Tuple(left, right) => {
                    let Ty::Pair(a, b) = ty else {
                        return Err(self.error(
                            module,
                            pattern.span,
                            ErrorCode::TypeMismatch,
                            "tuple basis pattern requires a product basis type",
                        ));
                    };
                    let left_bits = a.basis_bits().expect("basis pattern type");
                    let left_label = label & ((1u16 << left_bits) - 1);
                    // Push right first to visit pattern names from left to right.
                    pending.push((right, b, label >> left_bits));
                    pending.push((left, a, left_label));
                }
            }
        }
        Ok(env)
    }

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
                let label = (label >> offset) & ((1 << width) - 1);
                if let PatternKind::Name(name) = &param.pattern.kind {
                    // Retain the existing work accounting for legacy binders.
                    self.charge(&key.0, param.span, ty.tree_size().nodes)?;
                    env.insert(
                        name.text.clone(),
                        BasisValue {
                            ty: ty.clone(),
                            label,
                        },
                    );
                } else {
                    env.extend(self.bind_basis_pattern(&key.0, &param.pattern, ty, label)?);
                }
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
            BasisExprKind::Name(name) => {
                let value = env.get(&name.text).ok_or_else(|| {
                    self.error(
                        module,
                        name.span,
                        ErrorCode::UnknownName,
                        format!("unknown basis value `{}`", name.text),
                    )
                })?;
                self.charge(module, name.span, value.ty.tree_size().nodes)?;
                value.clone()
            }
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
                let size = function.signature_size();
                self.charge(module, expr.span, size)?;
                let function = &self.basis[&key];
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
        // Each child was already checked; at most one bounded tuple layer is
        // constructed before this check, including types inferred from names.
        self.check_tree(module, expr.span, value.ty.tree_size())?;
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
