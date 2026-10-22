//! Bounded partial type substitution over the original checked type trees.
use super::*;
use crate::frontend::check::Linear;
use crate::frontend::check::plans::{ResolvedNatural, ResolvedType, ResolvedTypeKind};

#[derive(Default)]
struct Measure {
    cells: usize,
    copy_work: usize,
    complete: bool,
    known_bits: usize,
    fixed_bits: usize,
    conditional_size: bool,
}

fn closed_copy_work(
    ty: &Ty,
    charge: &mut impl FnMut(usize) -> Result<(), CompileError>,
) -> Result<(usize, usize, usize), CompileError> {
    charge(1)?;
    let (mut cells, mut depth, mut work) = (1usize, 1usize, 0usize);
    match &ty.kind {
        Kind::Q(child) => {
            let (n, d, w) = closed_copy_work(child, charge)?;
            cells += n;
            depth += d;
            work += w;
        }
        Kind::Tuple(fields) => {
            charge(fields.len())?;
            for field in fields {
                let (n, d, w) = closed_copy_work(field, charge)?;
                cells += n;
                depth = depth.max(d + 1);
                work += w;
            }
        }
        _ => {}
    }
    Ok((cells, depth, work.saturating_add(cells)))
}

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn close_source_type_partial(
        &mut self,
        value: &check::Ty,
        environment: &StaticEnvironment,
        span: Span,
    ) -> Result<Option<Ty>, CompileError> {
        let module = self.dormant_module(environment.owner, span)?;
        self.close_partial_type(
            value,
            environment,
            &module,
            span,
            false,
            &mut |compiler, size| compiler.close_source_size(size, environment, &module, span),
        )
    }

    pub(super) fn close_resolved_basis(
        &mut self,
        value: &ResolvedType,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
    ) -> Result<Option<Ty>, CompileError> {
        // This finite adapter still has no nominal transport. Borrow original
        // Nat plans while adapting its existing built-in partial closer; never
        // expand a type declaration into invented caller-owned Nat nodes.
        self.preflight_resolved_basis(value, module, span, 1, &mut 0)?;
        let view = self.resolved_basis_view(value, module, span, 1, &mut 0)?;
        self.close_partial_type(
            &view,
            environment,
            module,
            span,
            true,
            &mut |compiler, size| {
                compiler
                    .evaluate_plan_natural_partial(size, environment)
                    .map(|value| (value, false))
            },
        )
    }

    fn preflight_resolved_basis(
        &mut self,
        value: &ResolvedType,
        module: &str,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<(), CompileError> {
        self.tick(module, span)?;
        *nodes = nodes.saturating_add(1);
        if depth > MAX_DEPTH || *nodes > MAX_TREE_NODES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "retained Basis exceeds finite tree/depth capacity",
            ));
        }
        match &value.kind {
            ResolvedTypeKind::Nominal { .. } => Err(self.error(
                module,
                span,
                ErrorCode::Unsupported,
                "nominal source types require typed native transport",
            )),
            ResolvedTypeKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "retained Basis tuple exceeds 64 fields",
                    ));
                }
                self.charge(module, span, fields.len())?;
                for field in fields {
                    self.preflight_resolved_basis(field, module, span, depth + 1, nodes)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn resolved_basis_view<'plan>(
        &mut self,
        value: &'plan ResolvedType,
        module: &str,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<super::super::super::types::Type<&'plan ResolvedNatural>, CompileError> {
        self.tick(module, span)?;
        *nodes = nodes.saturating_add(1);
        if depth > MAX_DEPTH || *nodes > MAX_TREE_NODES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "retained Basis exceeds finite tree/depth capacity",
            ));
        }
        use super::super::super::types::Type;
        Ok(match &value.kind {
            ResolvedTypeKind::Unit => Type::unit(),
            ResolvedTypeKind::Bit => Type::bit(),
            ResolvedTypeKind::Bits(size) => Type::bits(size),
            ResolvedTypeKind::Parameter(parameter) => {
                self.charge(
                    module,
                    span,
                    parameter.name.len()
                        + parameter.key.as_ref().map_or(0, |key| key.name.len())
                        + 1,
                )?;
                Type::parameter(parameter.clone())
            }
            ResolvedTypeKind::Nominal { .. } => {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "nominal source types require typed native transport",
                ));
            }
            ResolvedTypeKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "retained Basis tuple exceeds 64 fields",
                    ));
                }
                self.charge(module, span, fields.len())?;
                let mut result = Vec::with_capacity(fields.len());
                for field in fields {
                    result.push(self.resolved_basis_view(field, module, span, depth + 1, nodes)?);
                }
                Type::tuple(result)
            }
        })
    }

    fn close_source_size(
        &mut self,
        linear: &Linear,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
    ) -> Result<(Option<u32>, bool), CompileError> {
        self.charge(module, span, linear.terms.len() + 1)?;
        let conditional = self.in_inactive_region() && !linear.terms.is_empty();
        let mut result = Some(linear.constant);
        let mut complete = true;
        for (key, coefficient) in &linear.terms {
            self.charge(
                module,
                span,
                key.name
                    .len()
                    .saturating_mul(self.concrete_context.naturals.len() + 1)
                    + 3,
            )?;
            let binder = self
                .source
                .lexical
                .get(&environment.owner)
                .and_then(|table| table.try_binder(key.id));
            if key.id.definition() != environment.owner
                || binder.is_none_or(|binder| {
                    binder.key != *key
                        || !matches!(
                            binder.kind,
                            super::super::super::resolve::locals::BindingKind::StaticNatural
                                | super::super::super::resolve::locals::BindingKind::FoldIndex
                        )
                })
            {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "closed size has a foreign original natural binder",
                ));
            }
            match self.concrete_context.naturals.get(key) {
                Some(value) => {
                    result = result.and_then(|result| {
                        coefficient
                            .checked_mul(i128::from(*value))
                            .and_then(|term| result.checked_add(term))
                    });
                }
                None => complete = false,
            }
        }
        if !complete {
            return Ok((None, conditional));
        }
        let Some(result) = result else {
            if conditional {
                return Ok((None, true));
            }
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "closed size affine arithmetic overflow",
            ));
        };
        match u32::try_from(result) {
            Ok(value) => Ok((Some(value), conditional)),
            Err(_) if conditional => Ok((None, true)),
            Err(_) => Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "closed size must fit a nonnegative u32",
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn close_partial_type<N>(
        &mut self,
        value: &super::super::super::types::Type<N>,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        basis: bool,
        size: &mut impl FnMut(&mut Self, &N) -> Result<(Option<u32>, bool), CompileError>,
    ) -> Result<Option<Ty>, CompileError> {
        self.tick(module, span)?;
        if self.current_instance_owner() != Some(environment.owner)
            || self.source.resolution.module(module) != Some(environment.module)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "type plan differs from its active original source owner",
            ));
        }
        // Reserve the entire expanded tree before any copied type/Vec exists.
        // Deferred trees still visit all closed siblings and size arithmetic.
        let measure =
            self.measure_partial_type(value, environment, module, span, basis, 1, size)?;
        if !measure.complete {
            return Ok(None);
        }
        self.charge(module, span, measure.copy_work)?;
        self.copy_partial_type(value, environment, module, span, size)
            .map(Some)
    }

    #[allow(clippy::too_many_arguments)]
    fn measure_partial_type<N>(
        &mut self,
        value: &super::super::super::types::Type<N>,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        basis: bool,
        depth: usize,
        size: &mut impl FnMut(&mut Self, &N) -> Result<(Option<u32>, bool), CompileError>,
    ) -> Result<Measure, CompileError> {
        self.tick(module, span)?;
        if depth > MAX_DEPTH {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "closed type exceeds depth 64",
            ));
        }
        let mut measure = Measure {
            cells: 1,
            copy_work: 1,
            complete: true,
            known_bits: 0,
            fixed_bits: 0,
            conditional_size: false,
        };
        match &value.kind {
            Kind::Nominal(_) => {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "nominal source types require typed native transport",
                ));
            }
            Kind::Unit => {}
            Kind::Bit => {
                measure.known_bits = 1;
                measure.fixed_bits = 1;
            }
            Kind::Bits(original) => {
                let (width, conditional) = size(self, original)?;
                measure.conditional_size = conditional;
                match width {
                    Some(width) if width <= MAX_BITS as u32 => {
                        measure.known_bits = width as usize;
                        if !conditional {
                            measure.fixed_bits = width as usize;
                        }
                    }
                    Some(_) if conditional => measure.complete = false,
                    Some(_) => {
                        return Err(self.error(
                            module,
                            span,
                            ErrorCode::Limit,
                            "closed register width exceeds 12",
                        ));
                    }
                    None => measure.complete = false,
                }
            }
            Kind::Parameter(parameter) => {
                let key = parameter.key.as_ref().ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "closed Basis lacks its original binder",
                    )
                })?;
                self.charge(
                    module,
                    span,
                    key.name.len().saturating_mul(environment.bases.len() + 1) + 3,
                )?;
                let binder = self
                    .source
                    .lexical
                    .get(&environment.owner)
                    .and_then(|table| table.try_binder(key.id));
                if key.id.definition() != environment.owner
                    || !environment.bases.contains_key(key)
                    || binder.is_none_or(|binder| {
                        binder.key != *key
                            || binder.kind
                                != super::super::super::resolve::locals::BindingKind::StaticBasis
                    })
                {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "closed Basis has a foreign original binder",
                    ));
                }
                let replacement = self
                    .concrete_context
                    .current
                    .as_ref()
                    .and_then(|instance| instance.interface.bases.get(key));
                match replacement {
                    Some(replacement) => {
                        let mut work = self.work;
                        let mut precise = None;
                        let checked =
                            types::closed_basis_capacity(replacement, span, &mut |at, cells| {
                                self.charge_at(&mut work, module, at, cells)
                                    .map_err(|error| {
                                        precise = Some(error);
                                        SourceError::new("limit", at, "closed Basis work limit")
                                    })
                            });
                        self.work = work;
                        if let Some(error) = precise {
                            return Err(error);
                        }
                        checked.map_err(|error| {
                            source_error(self.project, &self.project.root, error.in_module(module))
                        })?;
                        let replacement = &self
                            .concrete_context
                            .current
                            .as_ref()
                            .unwrap()
                            .interface
                            .bases[key];
                        let mut work = self.work;
                        let tree = closed_copy_work(replacement, &mut |cells| {
                            self.charge_at(&mut work, module, span, cells)
                        });
                        self.work = work;
                        let (cells, expanded_depth, copy_work) = tree?;
                        if depth.saturating_sub(1) + expanded_depth > MAX_DEPTH {
                            return Err(self.error(
                                module,
                                span,
                                ErrorCode::Limit,
                                "expanded Basis exceeds depth 64",
                            ));
                        }
                        let replacement = &self
                            .concrete_context
                            .current
                            .as_ref()
                            .unwrap()
                            .interface
                            .bases[key];
                        measure.cells = cells;
                        measure.copy_work = copy_work;
                        measure.known_bits = replacement.basis_bits().expect("closed finite Basis");
                        measure.fixed_bits = measure.known_bits;
                    }
                    None => measure.complete = false,
                }
            }
            Kind::Q(child) => {
                if basis {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "Basis actual contains a quantum owner",
                    ));
                }
                let child = self.measure_partial_type(
                    child,
                    environment,
                    module,
                    span,
                    true,
                    depth + 1,
                    size,
                )?;
                measure.cells += child.cells;
                measure.copy_work = child.copy_work.saturating_add(measure.cells);
                measure.complete = child.complete;
                measure.conditional_size = child.conditional_size;
            }
            Kind::Tuple(fields) => {
                self.charge(module, span, fields.len())?;
                if fields.len() > 64 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "closed tuple exceeds 64 fields",
                    ));
                }
                if fields.len() < 2 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "finite tuple requires at least two fields",
                    ));
                }
                measure.copy_work = 0;
                for field in fields {
                    let child = self.measure_partial_type(
                        field,
                        environment,
                        module,
                        span,
                        basis,
                        depth + 1,
                        size,
                    )?;
                    measure.cells = measure.cells.saturating_add(child.cells);
                    measure.complete &= child.complete;
                    measure.copy_work = measure.copy_work.saturating_add(child.copy_work);
                    measure.known_bits = measure.known_bits.saturating_add(child.known_bits);
                    measure.fixed_bits = measure.fixed_bits.saturating_add(child.fixed_bits);
                    measure.conditional_size |= child.conditional_size;
                }
                measure.copy_work = measure.copy_work.saturating_add(measure.cells);
            }
        }
        if measure.cells > MAX_TREE_NODES || (basis && measure.fixed_bits > MAX_BITS) {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "closed type exceeds finite tree/register capacity",
            ));
        }
        if basis && measure.known_bits > MAX_BITS {
            if measure.conditional_size {
                measure.complete = false;
            } else {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "closed type exceeds finite register capacity",
                ));
            }
        }
        Ok(measure)
    }

    fn copy_partial_type<N>(
        &mut self,
        value: &super::super::super::types::Type<N>,
        environment: &StaticEnvironment,
        module: &str,
        span: Span,
        size: &mut impl FnMut(&mut Self, &N) -> Result<(Option<u32>, bool), CompileError>,
    ) -> Result<Ty, CompileError> {
        self.tick(module, span)?;
        Ok(match &value.kind {
            Kind::Nominal(_) => {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "nominal source types require typed native transport",
                ));
            }
            Kind::Unit => Ty::unit(),
            Kind::Bit => Ty::bit(),
            Kind::Bits(original) => Ty::bits(size(self, original)?.0.ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "size changed during closed type copy",
                )
            })?),
            Kind::Parameter(parameter) => {
                let key = parameter
                    .key
                    .as_ref()
                    .expect("preflight original Basis key");
                self.charge(
                    module,
                    span,
                    key.name.len().saturating_mul(environment.bases.len() + 1) + 1,
                )?;
                self.concrete_context
                    .current
                    .as_ref()
                    .expect("preflight closed instance")
                    .interface
                    .bases[key]
                    .clone()
            }
            Kind::Q(child) => {
                Ty::quantum(self.copy_partial_type(child, environment, module, span, size)?)
            }
            Kind::Tuple(fields) => {
                self.charge(module, span, fields.len())?;
                let mut result = Vec::with_capacity(fields.len());
                for field in fields {
                    result.push(self.copy_partial_type(field, environment, module, span, size)?);
                }
                Ty::tuple(result)
            }
        })
    }
}
