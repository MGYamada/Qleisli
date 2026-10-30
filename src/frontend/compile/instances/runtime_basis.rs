//! Close runtime-call Basis actuals without granting operation capabilities.
//! Original plans and the common checked nominal trees remain the source of types;
//! the complete emitted root still requires independent typed native checking.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::check::plans::{
    ResolvedStatic, ResolvedStaticKind, ResolvedType, ResolvedTypeKind,
};
use crate::frontend::resolve::{TypeId, locals::BindingKind};

impl Compiler<'_> {
    pub(super) fn runtime_basis(
        &mut self,
        value: &ResolvedStatic,
        environment: &StaticEnvironment,
        module: &str,
    ) -> Result<Option<Ty>, CompileError> {
        self.source_environment(environment, module, value.span)?;
        if value
            .node
            .is_some_and(|node| node.definition() != environment.owner)
        {
            return Err(self.error(
                module,
                value.span,
                ErrorCode::TypeMismatch,
                "runtime Basis has a foreign original occurrence",
            ));
        }
        for reference in &value.type_references {
            self.source_reference(reference, environment, module, value.span)?;
        }
        let mut nodes = 0;
        let mut known_bits = 0;
        let result = match &value.kind {
            ResolvedStaticKind::Basis(basis) => self.runtime_basis_plan(
                basis,
                environment,
                module,
                value.span,
                1,
                &mut nodes,
                &mut known_bits,
            )?,
            ResolvedStaticKind::Name(reference) => {
                self.source_reference(reference, environment, module, value.span)?;
                let key = reference.local.as_ref().ok_or_else(|| {
                    self.error(
                        module,
                        value.span,
                        ErrorCode::TypeMismatch,
                        "runtime Basis name requires its original static binder",
                    )
                })?;
                self.runtime_basis_parameter(key, environment, module, value.span, 1, &mut nodes)?
            }
            _ => {
                return Err(self.error(
                    module,
                    value.span,
                    ErrorCode::TypeMismatch,
                    "runtime static argument is not a Basis",
                ));
            }
        };
        if let Some(basis) = &result {
            let mut work = self.work;
            let checked = types::typed_basis_capacity(basis, value.span, &mut |at, cells| {
                self.charge_at(&mut work, module, at, cells)
                    .map_err(|error| SourceError::new("limit", at, error.to_string()))
            });
            self.work = work;
            checked.map_err(|error| self.originals.error(error.in_module(module)))?;
        }
        Ok(result)
    }

    #[allow(clippy::too_many_arguments)]
    fn runtime_basis_parameter(
        &mut self,
        key: &BinderKey,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<Ty>, CompileError> {
        self.charge(module, span, key.name.len() + environment.bases.len() + 3)?;
        if key.id.definition() != environment.owner
            || !environment.bases.contains_key(key)
            || self.source.lexical[&environment.owner]
                .try_binder(key.id)
                .is_none_or(|binder| binder.key != *key || binder.kind != BindingKind::StaticBasis)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "runtime Basis differs from its original formal",
            ));
        }
        let Some(basis) = self
            .concrete_context
            .current
            .as_ref()
            .and_then(|instance| instance.interface.bases.get(key))
        else {
            return Ok(None);
        };
        let mut work = self.work;
        let result = (|| {
            let mut charge = |at, cells| {
                self.charge_at(&mut work, module, at, cells)
                    .map_err(|error| SourceError::new("limit", at, error.to_string()))
            };
            let size = check::type_size_budgeted(
                basis,
                MAX_TREE_NODES.saturating_sub(*nodes),
                MAX_TREE_DEPTH + 1 - depth,
                true,
                span,
                &mut charge,
            )?;
            // Reserve the full nominal metadata and copied fields before clone.
            types::typed_basis_capacity(basis, span, &mut charge)?;
            Ok::<_, SourceError>((size.nodes, basis.clone()))
        })();
        self.work = work;
        let (count, basis) =
            result.map_err(|error| self.originals.error(error.in_module(module)))?;
        *nodes += count;
        Ok(Some(basis))
    }

    #[allow(clippy::too_many_arguments)]
    fn runtime_nominal(
        &mut self,
        id: TypeId,
        canonical: &check::Ty,
        module: &str,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Ty, CompileError> {
        let mut work = self.work;
        let result = (|| {
            let mut charge = |at, cells| {
                self.charge_at(&mut work, module, at, cells)
                    .map_err(|error| SourceError::new("limit", at, error.to_string()))
            };
            charge(span, self.source.nominals.len() + 1)?;
            let original = self.source.nominals.get(&id).ok_or_else(|| {
                SourceError::new(
                    "source",
                    span,
                    "runtime Basis has no original nominal declaration",
                )
            })?;
            if !canonical.equivalent_by_budgeted(
                original,
                &mut |a, b| Ok(a == b),
                &mut |cells| charge(span, cells),
            )? {
                return Err(SourceError::new(
                    "source",
                    span,
                    "runtime Basis differs from its original nominal tree",
                ));
            }
            let size = check::type_size_budgeted(
                original,
                MAX_TREE_NODES.saturating_sub(*nodes),
                MAX_TREE_DEPTH + 1 - depth,
                true,
                span,
                &mut charge,
            )?;
            // Nominal fields have their declaration's scope; caller formals
            // must never capture their Nat or type names.
            let closed = check::close_type_budgeted(
                original,
                &BTreeMap::new(),
                &BTreeMap::new(),
                span,
                &mut charge,
            )?;
            Ok::<_, SourceError>((size.nodes, closed))
        })();
        self.work = work;
        let (count, closed) =
            result.map_err(|error| self.originals.error(error.in_module(module)))?;
        *nodes += count;
        Ok(closed)
    }

    #[allow(clippy::too_many_arguments)]
    fn runtime_basis_plan(
        &mut self,
        value: &ResolvedType,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        depth: usize,
        nodes: &mut usize,
        known_bits: &mut usize,
    ) -> Result<Option<Ty>, CompileError> {
        self.tick(module, span)?;
        if depth > MAX_TREE_DEPTH || *nodes >= MAX_TREE_NODES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "runtime Basis exceeds finite tree/depth capacity",
            ));
        }
        match &value.kind {
            ResolvedTypeKind::Parameter(parameter) => {
                let key = parameter.key.as_ref().ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "runtime Basis lacks its original binder",
                    )
                })?;
                let closed =
                    self.runtime_basis_parameter(key, environment, module, span, depth, nodes)?;
                if let Some(basis) = &closed {
                    self.runtime_basis_width(basis, module, span, known_bits)?;
                }
                return Ok(closed);
            }
            ResolvedTypeKind::Nominal { id, canonical } => {
                let basis = self.runtime_nominal(*id, canonical, module, span, depth, nodes)?;
                self.runtime_basis_width(&basis, module, span, known_bits)?;
                return Ok(Some(basis));
            }
            _ => {}
        }
        *nodes += 1;
        let result = match &value.kind {
            ResolvedTypeKind::Unit => Some(Ty::unit()),
            ResolvedTypeKind::Bit => Some(Ty::bit()),
            ResolvedTypeKind::Bits(size) => self
                .evaluate_plan_natural_partial(size, environment)?
                .map(Ty::bits),
            ResolvedTypeKind::Tuple(fields) => {
                if !(2..=64).contains(&fields.len()) {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "runtime Basis tuple requires 2 through 64 fields",
                    ));
                }
                self.charge(module, span, fields.len())?;
                let mut closed = Vec::with_capacity(fields.len());
                let mut complete = true;
                for field in fields {
                    match self.runtime_basis_plan(
                        field,
                        environment,
                        module,
                        span,
                        depth + 1,
                        nodes,
                        known_bits,
                    )? {
                        Some(field) => closed.push(field),
                        None => complete = false,
                    }
                }
                complete.then(|| Ty::tuple(closed))
            }
            _ => unreachable!("parameter and nominal handled before node accounting"),
        };
        if !matches!(value.kind, ResolvedTypeKind::Tuple(_)) {
            if let Some(basis) = &result {
                self.runtime_basis_width(basis, module, span, known_bits)?;
            }
        }
        Ok(result)
    }

    fn runtime_basis_width(
        &mut self,
        basis: &Ty,
        module: &str,
        span: Span,
        known_bits: &mut usize,
    ) -> Result<(), CompileError> {
        self.charge(module, span, basis.tree_size().nodes + 1)?;
        let width = basis.basis_width().ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "runtime Basis must have finite ordinary storage",
            )
        })?;
        *known_bits = known_bits.saturating_add(width as usize);
        if *known_bits > MAX_BITS {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "closed runtime Basis portions exceed the initial 12-bit limit",
            ));
        }
        Ok(())
    }
}
