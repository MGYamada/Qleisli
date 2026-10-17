//! Closed portions of original contracts are checked before any deferral.
use super::*;
use crate::frontend::resolve::locals::OriginalNode;

fn available(
    ty: &check::Ty,
    bases: &BTreeMap<BinderKey, Ty>,
    naturals: &BTreeMap<BinderKey, u32>,
    charge: &mut impl FnMut(usize) -> Result<(), CompileError>,
) -> Result<bool, CompileError> {
    charge(1)?;
    Ok(match &ty.kind {
        Kind::Bits(size) => {
            let mut complete = true;
            for key in size.terms.keys() {
                charge(key.name.len().saturating_mul(naturals.len() + 1) + 1)?;
                complete &= naturals.contains_key(key);
            }
            complete
        }
        Kind::Parameter(parameter) => {
            charge(parameter.name.len().saturating_mul(bases.len() + 1) + 1)?;
            parameter
                .key
                .as_ref()
                .is_some_and(|key| bases.contains_key(key))
        }
        Kind::Q(child) => available(child, bases, naturals, charge)?,
        Kind::Tuple(fields) => {
            charge(fields.len())?;
            let mut complete = true;
            for field in fields {
                complete &= available(field, bases, naturals, charge)?;
            }
            complete
        }
        _ => true,
    })
}

impl Compiler<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn validate_partial_instance_contracts(
        &mut self,
        target: Key,
        bases: &BTreeMap<BinderKey, Ty>,
        naturals: &BTreeMap<BinderKey, u32>,
        operations: &operations::Bindings,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        // Signature plans retain the original u32 arithmetic even if an
        // unrelated actual is unbound. This does not reevaluate requires:
        // their adopted normalized conjunction remains the shared closer's.
        let mut work = self.work;
        let result = (|| {
            self.charge_at(&mut work, module, span, 1)?;
            let plans = self.interface_naturals.get(&target).ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "missing original interface natural plans",
                )
            })?;
            if plans.environment.owner != target {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "foreign original interface natural environment",
                ));
            }
            self.charge_at(&mut work, module, span, plans.roots.len())?;
            let shared = std::cell::Cell::new(work);
            let charge = |at, cells| {
                let mut used = shared.get();
                let result = self.charge_at(&mut used, module, at, cells);
                shared.set(used);
                result
            };
            let evaluated = (|| {
                for root in &plans.roots {
                    let lookup = self.locals();
                    let original_type = lookup
                        .original_node_budgeted(root.type_node, &mut |at, cells| {
                            charge(at, cells)
                        })?;
                    let original_natural = lookup
                        .original_node_budgeted(root.natural.node, &mut |at, cells| {
                            charge(at, cells)
                        })?;
                    if root.owner != target
                        || !matches!((original_type, original_natural), (Some(OriginalNode::Type(ty)), Some(OriginalNode::Natural(natural))) if matches!(&ty.kind, TypeKind::Bits(child) if std::ptr::eq(child,natural)))
                    {
                        return Err(self.error(
                            module,
                            root.natural.span,
                            ErrorCode::TypeMismatch,
                            "interface natural differs from its original type child",
                        ));
                    }
                    naturals::evaluate(
                        &root.natural,
                        &plans.environment,
                        naturals,
                        &mut |at, cells| charge(at, cells),
                        &mut |at| charge(at, 1),
                        &|at, code, message| self.error(module, at, code, message),
                    )?;
                }
                Ok(())
            })();
            work = shared.get();
            evaluated
        })();
        self.work = work;
        result?;
        for (key, operation) in operations {
            self.charge(
                module,
                span,
                key.name
                    .len()
                    .saturating_mul(self.source.interfaces[&target].statics.len() + 1)
                    + 1,
            )?;
            let mut work = self.work;
            let closed = (|| {
                let formal = self.source.interfaces[&target]
                    .statics
                    .iter()
                    .find(|formal| formal.key == *key)
                    .ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::TypeMismatch,
                            "foreign original operation binding",
                        )
                    })?;
                let StaticKind::Operation {
                    basis, codomain, ..
                } = &formal.kind
                else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "operation actual has a non-operation formal",
                    ));
                };
                let mut close = |ty: &check::Ty| -> Result<Option<Ty>, CompileError> {
                    if !available(ty, bases, naturals, &mut |cells| {
                        self.charge_at(&mut work, module, span, cells)
                    })? {
                        return Ok(None);
                    }
                    let mut precise = None;
                    let result =
                        check::close_type_budgeted(ty, naturals, bases, span, &mut |at, cells| {
                            self.charge_at(&mut work, module, at, cells)
                                .map_err(|error| {
                                    precise = Some(error);
                                    SourceError::new("limit", at, "partial interface work limit")
                                })
                        });
                    if let Some(error) = precise {
                        return Err(error);
                    }
                    let closed = result.map_err(|error| {
                        source_error(self.project, &self.project.root, error.in_module(module))
                    })?;
                    let mut precise = None;
                    let checked = types::closed_basis_capacity(&closed, span, &mut |at, cells| {
                        self.charge_at(&mut work, module, at, cells)
                            .map_err(|error| {
                                precise = Some(error);
                                SourceError::new("limit", at, "partial operation port work limit")
                            })
                    });
                    if let Some(error) = precise {
                        return Err(error);
                    }
                    checked.map_err(|error| {
                        source_error(self.project, &self.project.root, error.in_module(module))
                    })?;
                    Ok(Some(closed))
                };
                Ok::<_, CompileError>((close(basis)?, close(codomain.as_ref().unwrap_or(basis))?))
            })();
            self.work = work;
            let (input, output) = closed?;
            let mut work = self.work;
            let matches = (|| {
                let mut charge = |cells| self.charge_at(&mut work, module, span, cells);
                let input = input
                    .as_ref()
                    .map(|input| {
                        operations::same_port_budgeted(input, &operation.basis, &mut charge)
                    })
                    .transpose()?
                    .unwrap_or(true);
                let output = output
                    .as_ref()
                    .map(|output| {
                        operations::same_port_budgeted(output, &operation.codomain, &mut charge)
                    })
                    .transpose()?
                    .unwrap_or(true);
                Ok::<_, CompileError>(input && output)
            })();
            self.work = work;
            if !matches? {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "closed static actual differs from the original operation port",
                ));
            }
        }
        Ok(())
    }
}
