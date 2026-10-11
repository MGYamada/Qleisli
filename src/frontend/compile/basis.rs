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
        super::super::ordinary::finite::evaluate(
            &mut LabelContext {
                compiler: self,
                module,
            },
            expr,
            env,
            depth,
        )
    }
}

struct LabelContext<'context, 'source> {
    compiler: &'context mut Compiler<'source>,
    module: &'context str,
}
struct LabelTuple {
    types: Vec<Ty>,
    bits: usize,
    label: u16,
}
impl super::super::ordinary::finite::Context for LabelContext<'_, '_> {
    type Value = BasisValue;
    type Environment = BTreeMap<BinderKey, BasisValue>;
    type Tuple = LabelTuple;
    type Error = CompileError;

    fn enter(&mut self, span: Span, depth: usize) -> Result<(), CompileError> {
        self.compiler.tick(self.module, span)?;
        if depth >= MAX_DEPTH {
            return Err(self.compiler.error(
                self.module,
                span,
                ErrorCode::Limit,
                "basis evaluation exceeds the initial depth limit",
            ));
        }
        Ok(())
    }
    fn name(&mut self, name: &Ident, env: &Self::Environment) -> Result<BasisValue, CompileError> {
        let value = self
            .compiler
            .locals
            .local_key(name)
            .and_then(|key| env.get(key))
            .ok_or_else(|| {
                self.compiler.error(
                    self.module,
                    name.span,
                    ErrorCode::UnknownName,
                    format!("unknown basis value `{}`", name.text),
                )
            })?;
        self.compiler
            .charge(self.module, name.span, value.ty.tree_size().nodes)?;
        Ok(value.clone())
    }
    fn unit(&mut self) -> BasisValue {
        BasisValue {
            ty: Ty::unit(),
            label: 0,
        }
    }
    fn bit(&mut self, value: bool) -> BasisValue {
        BasisValue {
            ty: Ty::bit(),
            label: u16::from(value),
        }
    }
    fn tuple(&mut self, fields: usize) -> LabelTuple {
        LabelTuple {
            types: Vec::with_capacity(fields),
            bits: 0,
            label: 0,
        }
    }
    fn push(
        &mut self,
        span: Span,
        tuple: &mut LabelTuple,
        value: BasisValue,
    ) -> Result<(), CompileError> {
        let width = value.ty.basis_bits().expect("basis value");
        if tuple.bits + width > MAX_BITS {
            return Err(self.compiler.error(
                self.module,
                span,
                ErrorCode::Limit,
                "basis result exceeds 12 bits",
            ));
        }
        tuple.label |= value.label << tuple.bits;
        tuple.bits += width;
        tuple.types.push(value.ty);
        Ok(())
    }
    fn product(&mut self, tuple: LabelTuple) -> BasisValue {
        BasisValue {
            ty: Ty::tuple(tuple.types),
            label: tuple.label,
        }
    }
    fn require_bit(&mut self, span: Span, value: &BasisValue) -> Result<(), CompileError> {
        if value.ty == Ty::bit() {
            Ok(())
        } else {
            Err(self.compiler.error(
                self.module,
                span,
                ErrorCode::TypeMismatch,
                "not/xor/and require Bit operands",
            ))
        }
    }
    fn boolean(
        &mut self,
        operation: super::super::ordinary::Boolean,
        a: BasisValue,
        b: Option<BasisValue>,
    ) -> BasisValue {
        use super::super::ordinary::Boolean;
        let label = match operation {
            Boolean::Not => a.label ^ 1,
            Boolean::And => a.label & b.expect("binary operand").label,
            Boolean::Xor => a.label ^ b.expect("binary operand").label,
            Boolean::Constant(_) => unreachable!("literal handled directly"),
        };
        BasisValue {
            ty: Ty::bit(),
            label,
        }
    }
    fn call(
        &mut self,
        span: Span,
        callee: &Ident,
        args: &[BasisExpr],
        env: &Self::Environment,
        depth: usize,
    ) -> Result<BasisValue, CompileError> {
        if self
            .compiler
            .locals
            .local_key(callee)
            .is_some_and(|key| env.contains_key(key))
        {
            return Err(self.compiler.error(
                self.module,
                callee.span,
                ErrorCode::TypeMismatch,
                "a basis value is not callable",
            ));
        }
        let Callee::User(key) = self.compiler.resolve(self.module, callee)? else {
            return Err(self.compiler.error(
                self.module,
                callee.span,
                ErrorCode::TypeMismatch,
                "quantum operation in a basis expression",
            ));
        };
        let function = self.compiler.basis.get(&key).ok_or_else(|| {
            self.compiler.error(
                self.module,
                callee.span,
                ErrorCode::TypeMismatch,
                "basis expressions may call only classical functions",
            )
        })?;
        let size = function.signature_size();
        self.compiler.charge(self.module, span, size)?;
        let function = &self.compiler.basis[&key];
        let params = function.params.clone();
        let result = function.result.clone();
        if args.len() != params.len() {
            return Err(self.compiler.error(
                self.module,
                span,
                ErrorCode::Arity,
                "basis argument count does not match",
            ));
        }
        let mut label = 0;
        let mut offset = 0;
        for (arg, ty) in args.iter().zip(&params) {
            let value = self.compiler.eval_basis(self.module, arg, env, depth + 1)?;
            if value.ty != *ty {
                return Err(self.compiler.error(
                    self.module,
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
        Ok(BasisValue {
            ty: result,
            label: self.compiler.basis[&key].table[label],
        })
    }
    fn finish(&mut self, span: Span, value: BasisValue) -> Result<BasisValue, CompileError> {
        self.compiler
            .check_tree(self.module, span, value.ty.tree_size())?;
        Ok(value)
    }
}
