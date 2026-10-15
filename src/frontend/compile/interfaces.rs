//! Bind closed normalized interface sizes to their original ordinary Nat plans.
//!
//! This is finite proposal preparation. It neither enables a generic source
//! profile nor supplies Meaning, operation access or native acceptance evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{InterfaceSlot, TypeChild};
use crate::frontend::resolve::locals::OriginalNode;
use std::cell::Cell;

#[cfg(test)]
mod tests;

impl Compiler<'_> {
    pub(super) fn validate_interface_naturals(
        &mut self,
        definition: Key,
        closed: &super::super::closed::ClosedInterface,
        span: Span,
    ) -> Result<(), CompileError> {
        let module = &self.source.resolution.declaration(definition).name.0;
        let work = Cell::new(self.work);
        let charge = |at, cells| {
            let mut used = work.get();
            let result = self.charge_at(&mut used, module, at, cells);
            work.set(used);
            result
        };
        let result = (|| {
            macro_rules! refuse {
                ($at:expr, $message:literal) => {{
                    let at = $at;
                    charge(at, $message.len() + 1)?;
                    return Err(self.error(module, at, ErrorCode::TypeMismatch, $message));
                }};
            }
            charge(span, 1)?;
            let Some(original) = self.interface_naturals.get(&definition) else {
                refuse!(span, "missing original interface natural plans");
            };
            if original.environment.owner != definition {
                refuse!(span, "foreign original interface natural environment");
            }
            let lookup = self.locals();
            charge(span, original.roots.len())?;
            for root in &original.roots {
                let at = root.natural.span;
                if root.owner != definition || root.type_node.definition() != definition {
                    refuse!(at, "foreign original interface natural occurrence");
                }
                // Recheck the retained owner and the exact original Bits child
                // after occurrence transfer, using the same borrowed AST.
                let Some(OriginalNode::Type(source_type)) =
                    lookup.original_node_budgeted(root.type_node, &mut |s, n| charge(s, n))?
                else {
                    refuse!(at, "missing original interface type occurrence");
                };
                let Some(OriginalNode::Natural(source_natural)) =
                    lookup.original_node_budgeted(root.natural.node, &mut |s, n| charge(s, n))?
                else {
                    refuse!(at, "missing original interface size occurrence");
                };
                if !matches!(&source_type.kind, TypeKind::Bits(size) if std::ptr::eq(size, source_natural))
                {
                    refuse!(at, "original interface size is not this type's child");
                }

                let mut ty = match &root.slot {
                    InterfaceSlot::Parameter(ordinal) => {
                        charge(at, 1)?;
                        let Some(ty) = closed.parameters.get(*ordinal) else {
                            refuse!(at, "missing closed interface parameter");
                        };
                        ty
                    }
                    InterfaceSlot::Result => &closed.result,
                    InterfaceSlot::MeaningInput => {
                        // Meaning domains have their own rectangular contract;
                        // a runtime ClosedInterface cannot discharge that slot.
                        refuse!(at, "Meaning domain requires its separate closed contract");
                    }
                    InterfaceSlot::OperationInput { ordinal, formal }
                    | InterfaceSlot::OperationOutput { ordinal, formal } => {
                        charge(at, formal.name.len() + 1)?;
                        let interface = &self.source.interfaces[&definition];
                        let Some(declared) = interface.statics.get(*ordinal) else {
                            refuse!(at, "missing original operation formal");
                        };
                        charge(at, declared.key.name.len() + 1)?;
                        if declared.key != *formal
                            || !matches!(declared.kind, StaticKind::Operation { .. })
                        {
                            refuse!(at, "mismatched original operation formal");
                        }
                        // Bound all key comparisons before the map lookup.
                        charge(at, closed.operations.len())?;
                        for key in closed.operations.keys() {
                            charge(at, key.name.len() + formal.name.len() + 1)?;
                        }
                        let Some(operation) = closed.operations.get(formal) else {
                            refuse!(at, "missing closed operation formal");
                        };
                        let port = if matches!(root.slot, InterfaceSlot::OperationInput { .. }) {
                            &operation.input
                        } else {
                            operation.output()
                        };
                        let Some(basis) = port.quantum_basis() else {
                            refuse!(at, "closed operation port lacks its quantum owner");
                        };
                        basis
                    }
                };
                charge(at, root.path.len())?;
                for child in &root.path {
                    ty = match (child, &ty.kind) {
                        (TypeChild::Quantum, Kind::Q(inner)) => inner,
                        (TypeChild::Tuple(ordinal), Kind::Tuple(fields)) => {
                            let Some(field) = fields.get(*ordinal) else {
                                refuse!(at, "closed interface tuple child is missing");
                            };
                            field
                        }
                        _ => refuse!(at, "closed interface type path differs from its source"),
                    };
                }
                let Kind::Bits(expected) = ty.kind else {
                    refuse!(at, "closed interface size has a different constructor");
                };
                let evaluated = naturals::evaluate(
                    &root.natural,
                    &original.environment,
                    &closed.naturals,
                    &mut |s, n| charge(s, n),
                    &mut |s| charge(s, 1),
                    &|s, code, message| self.error(module, s, code, message),
                )?;
                match evaluated {
                    naturals::NaturalValue::Closed(actual) if actual == expected => {}
                    naturals::NaturalValue::Closed(_) => {
                        refuse!(
                            at,
                            "original interface size differs from normalized closure"
                        );
                    }
                    naturals::NaturalValue::Deferred => {
                        refuse!(at, "original interface size is not concretely discharged");
                    }
                }
            }
            Ok(())
        })();
        self.work = work.get();
        result
    }
}
