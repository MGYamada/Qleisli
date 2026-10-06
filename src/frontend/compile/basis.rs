use super::*;

#[derive(Clone, Debug)]
pub(super) struct BasisValue {
    pub ty: Ty,
    pub label: u16,
}

impl Compiler<'_> {
    /// A predicate over one register has one explicit domain parameter. Ordinary
    /// basis calls keep their declared argument-list arity; no tuple is inferred.
    pub(super) fn check_predicate_domain(
        &self,
        module: &str,
        span: Span,
        predicate: &BasisFunction,
        source: &Ty,
    ) -> Result<(), CompileError> {
        let [domain] = predicate.params.as_slice() else {
            return Err(self.error(
                module,
                span,
                ErrorCode::Arity,
                format!(
                    "with_computed predicate requires exactly one explicit basis parameter of type `{source}`; found {} parameters",
                    predicate.params.len()
                ),
            ));
        };
        if domain != source || predicate.result != Ty::bit() {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!(
                    "predicate must map the exact source basis type to Bit: expected `{source} -> Bit`, found `{domain} -> {}`",
                    predicate.result
                ),
            ));
        }
        Ok(())
    }

    /// Bind one finite label through the exact product tree. Wildcards omit
    /// basis information only; the complete lift still checks injectivity.
    pub(super) fn bind_basis_pattern(
        &mut self,
        module: &str,
        pattern: &Pattern,
        ty: &Ty,
        label: u16,
    ) -> Result<BTreeMap<BinderKey, BasisValue>, CompileError> {
        let mut env = BTreeMap::new();
        let mut pending = vec![(pattern, ty, label)];
        while let Some((pattern, ty, label)) = pending.pop() {
            self.tick(module, pattern.span)?;
            match &pattern.kind {
                PatternKind::Name(name) => {
                    if env.keys().any(|key: &BinderKey| key.name == name.text) {
                        return Err(self.error(
                            module,
                            name.span,
                            ErrorCode::Ownership,
                            "duplicate name in a basis binding pattern",
                        ));
                    }
                    self.charge(module, pattern.span, ty.tree_size().nodes)?;
                    env.insert(
                        self.locals.key(self.locals.binder(name)).clone(),
                        BasisValue {
                            ty: ty.clone(),
                            label,
                        },
                    );
                }
                PatternKind::Wildcard => {}
                PatternKind::Tuple(patterns) => {
                    let Some(fields) = ty.pattern_fields(patterns.len()) else {
                        return Err(self.error(
                            module,
                            pattern.span,
                            ErrorCode::TypeMismatch,
                            if patterns.is_empty() {
                                format!("empty basis pattern requires Unit basis, found `{ty}`")
                            } else {
                                "tuple basis pattern requires the same immediate arity as its basis type"
                                    .to_owned()
                            },
                        ));
                    };
                    let mut offset = 0;
                    let mut children = Vec::with_capacity(fields.len());
                    for (pattern, field) in patterns.iter().zip(fields) {
                        let bits = field.basis_bits().expect("basis pattern type");
                        children.push((pattern, field, (label >> offset) & ((1u16 << bits) - 1)));
                        offset += bits;
                    }
                    pending.extend(children.into_iter().rev());
                }
            }
        }
        Ok(env)
    }

    pub(super) fn compile_basis(&mut self, key: &Key) -> Result<BasisFunction, CompileError> {
        let decl = self.declarations[key];
        let key_name = self.resolution.declaration(*key).name.clone();
        let (params, result) = self.signature(key)?;
        let bits: usize = params
            .iter()
            .map(|ty| ty.basis_bits().expect("basis parameter"))
            .sum();
        if bits > MAX_BITS {
            return Err(self.error(
                &key_name.0,
                decl.span,
                ErrorCode::Limit,
                "classical function domain exceeds 12 bits",
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
                    self.charge(&key_name.0, param.span, ty.tree_size().nodes)?;
                    env.insert(
                        self.locals.key(self.locals.binder(name)).clone(),
                        BasisValue {
                            ty: ty.clone(),
                            label,
                        },
                    );
                } else {
                    env.extend(self.bind_basis_pattern(&key_name.0, &param.pattern, ty, label)?);
                }
                offset += width;
            }
            let value = self.eval_basis(&key_name.0, body, &env, 0)?;
            if value.ty != result {
                return Err(self.error(
                    &key_name.0,
                    body.span,
                    ErrorCode::TypeMismatch,
                    format!("basis result does not match its declared type: expected `{result}`, found `{}`", value.ty),
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
        env: &BTreeMap<BinderKey, BasisValue>,
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
                let value = self
                    .locals
                    .local_key(name)
                    .and_then(|key| env.get(key))
                    .ok_or_else(|| {
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
                ty: Ty::bit(),
                label: u16::from(*bit),
            },
            BasisExprKind::Unit => BasisValue {
                ty: Ty::unit(),
                label: 0,
            },
            BasisExprKind::Tuple(fields) => {
                let mut types = Vec::with_capacity(fields.len());
                let mut bits = 0;
                let mut label = 0;
                for field in fields {
                    let value = self.eval_basis(module, field, env, depth + 1)?;
                    let width = value.ty.basis_bits().expect("basis value");
                    if bits + width > MAX_BITS {
                        return Err(self.error(
                            module,
                            expr.span,
                            ErrorCode::Limit,
                            "basis result exceeds 12 bits",
                        ));
                    }
                    label |= value.label << bits;
                    bits += width;
                    types.push(value.ty);
                }
                BasisValue {
                    ty: Ty::tuple(types),
                    label,
                }
            }
            BasisExprKind::Not(a) => {
                let a = self.eval_basis(module, a, env, depth + 1)?;
                self.require_bit(module, expr.span, &a)?;
                BasisValue {
                    ty: Ty::bit(),
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
                BasisValue {
                    ty: Ty::bit(),
                    label,
                }
            }
            BasisExprKind::Call { callee, args } => {
                if self
                    .locals
                    .local_key(callee)
                    .is_some_and(|key| env.contains_key(key))
                {
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
                        "basis expressions may call only classical functions",
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
                            format!(
                                "basis argument type does not match: expected `{ty}`, found `{}`",
                                value.ty
                            ),
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
        if value.ty == Ty::bit() {
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
