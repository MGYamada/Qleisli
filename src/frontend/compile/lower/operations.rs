//! Static descriptions are compile-time arguments, never runtime owners.
use super::super::operations::{Bindings, Operation};
use super::*;

impl Lowerer<'_, '_> {
    fn operation(
        &mut self,
        module: &str,
        expr: &StaticOp,
        env: &Env,
    ) -> Result<Operation, CompileError> {
        self.compiler.tick(module, expr.span)?;
        // Parser and each constructed description bound recursive depth.
        match &expr.kind {
            StaticOpKind::Name(name) => {
                self.static_name(module, name, env)?;
                if let Some(op) = self.bindings.get(&name.text) {
                    self.compiler.charge(module, name.span, op.copy_size())?;
                    return Ok(op.clone());
                }
                self.compiler.provider(module, name, None)
            }
            StaticOpKind::Bind {
                implementation,
                meaning,
            } => {
                for name in [implementation, meaning] {
                    self.static_name(module, name, env)?;
                    if self.bindings.contains_key(&name.text) {
                        return Err(self.error(
                            module,
                            name.span,
                            ErrorCode::TypeMismatch,
                            "bind_op requires closed declarations",
                        ));
                    }
                }
                self.compiler
                    .provider(module, implementation, Some(meaning))
            }
            StaticOpKind::Inverse(a) | StaticOpKind::Controlled(a) | StaticOpKind::Repeat(_, a) => {
                let a = self.operation(module, a, env)?;
                self.compiler
                    .construct(module, expr.span, &expr.kind, a, None)
            }
            StaticOpKind::Then(a, b)
            | StaticOpKind::Tensor(a, b)
            | StaticOpKind::Conjugate(a, b) => {
                let a = self.operation(module, a, env)?;
                let b = self.operation(module, b, env)?;
                self.compiler
                    .construct(module, expr.span, &expr.kind, a, Some(b))
            }
        }
    }

    pub(super) fn static_name(
        &self,
        module: &str,
        name: &Ident,
        env: &Env,
    ) -> Result<(), CompileError> {
        if env.contains_key(&name.text) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "a local or spent runtime value cannot be a static operation",
            ));
        }
        Ok(())
    }

    pub(super) fn bind_operations(
        &mut self,
        key: &Key,
        args: &[StaticOp],
        env: &Env,
        site: CallSite<'_>,
    ) -> Result<Bindings, CompileError> {
        let decl = self.compiler.declarations[key];
        if decl.static_params.len() != args.len() {
            return Err(self.error(
                site.module,
                site.span,
                ErrorCode::Arity,
                "explicit static argument count does not match",
            ));
        }
        if args.is_empty() {
            return Ok(Bindings::new());
        }
        let expected = self.compiler.abstract_bindings(key)?;
        let mut bindings = Bindings::new();
        let mut identity = Vec::new();
        for (param, arg) in decl.static_params.iter().zip(args) {
            let actual = self.operation(site.module, arg, env)?;
            let required = &expected[&param.name.text];
            if actual.basis != required.basis {
                return Err(self.error(
                    site.module,
                    arg.span,
                    ErrorCode::TypeMismatch,
                    "static argument has a different exact basis tree",
                ));
            }
            if required
                .meaning
                .as_ref()
                .is_some_and(|m| actual.meaning.as_ref() != Some(m))
            {
                return Err(self.error(
                    site.module,
                    arg.span,
                    ErrorCode::Contract,
                    "static argument does not establish the required phase-fixed meaning",
                ));
            }
            for access in [Access::Apply, Access::Adjoint, Access::Controlled] {
                if required.access[super::super::operations::access_index(access)] {
                    // Validate requested derived access even for an unused parameter.
                    actual.steps(site.module, arg.span, access, self.compiler)?;
                }
            }
            self.compiler
                .charge(site.module, arg.span, actual.copy_size().saturating_mul(2))?;
            identity.push(actual.clone());
            bindings.insert(param.name.text.clone(), actual);
        }
        if !identity.is_empty()
            && !self.abstract_check
            && !self
                .compiler
                .instances
                .iter()
                .any(|(k, v)| k == key && *v == identity)
        {
            if self.compiler.instances.len() >= 256 {
                return Err(self.error(
                    site.module,
                    site.span,
                    ErrorCode::Limit,
                    "project exceeds 256 distinct operation specializations",
                ));
            }
            self.compiler.instances.push((key.clone(), identity));
        }
        Ok(bindings)
    }

    pub(super) fn operation_steps(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
        env: &Env,
        access: Access,
    ) -> Result<Option<Vec<CircuitStep>>, CompileError> {
        let Some(op) = self.bindings.get(&name.text) else {
            return Ok(None);
        };
        self.compiler.charge(module, name.span, op.copy_size())?;
        let op = op.clone();
        self.static_name(module, name, env)?;
        if op.basis != *basis {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "operation and input have different exact basis trees",
            ));
        }
        Ok(Some(op.steps(module, name.span, access, self.compiler)?))
    }

    pub(super) fn call_bound(
        &mut self,
        key: &Key,
        args: Vec<Value>,
        site: Option<CallSite<'_>>,
        bindings: Bindings,
    ) -> Result<Value, CompileError> {
        let previous = std::mem::replace(&mut self.bindings, bindings);
        let result = self.call_user(key, args, site);
        self.bindings = previous;
        result
    }
}

/// Check types, linear ownership and declared access with abstract operations.
/// Identity placeholders are discarded here and can never authorize execution.
/// Exact computed obligations are checked afresh for every concrete expansion.
pub(in crate::frontend::compile) fn check_generic(
    compiler: &mut Compiler<'_>,
    key: &Key,
    bindings: Bindings,
) -> Result<(), CompileError> {
    lower_function_inner(compiler, key, bindings, true).map(|_| ())
}
