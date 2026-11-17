//! Exact coherent source partitions; execution remains behind native transport.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::types::nominal::Body;

#[cfg(test)]
mod tests;

impl Checker<'_, '_> {
    fn qmatch_labels(
        &self,
        selector: &Ty,
        arms: &[QuantumMatchArm],
        scope: &Scope,
        span: Span,
    ) -> Result<()> {
        // Keep the common judgment bounded even for a directly supplied AST.
        if arms.is_empty() || arms.len() > 64 {
            return Err(SourceError::new(
                "type",
                span,
                "qmatch requires 1..64 exact-label arms",
            ));
        }
        self.program.budget.charge(span, arms.len() + 1)?;
        if let Kind::Nominal(nominal) = &selector.kind {
            let Body::Enum(variants) = &nominal.body else {
                return Err(SourceError::new(
                    "type",
                    span,
                    "qmatch exact-label selectors require a fieldless enum or closed built-in basis",
                ));
            };
            self.program.budget.charge(span, variants.len() + 1)?;
            let mut seen = BTreeSet::new();
            for arm in arms {
                let QuantumLabel::Variant(value) = &arm.label else {
                    return Err(SourceError::new(
                        "type",
                        arm.span,
                        "a nominal qmatch selector requires its exact enum variant labels",
                    ));
                };
                let label = self.variant_value(value)?;
                normalize::expect(
                    &label,
                    selector,
                    &scope.context,
                    value.type_name.span,
                    &self.program.budget,
                )?;
                self.program
                    .budget
                    .charge(value.variant.span, value.variant.text.len() + 1)?;
                if !seen.insert(&value.variant.text) {
                    return Err(SourceError::new(
                        "type",
                        value.variant.span,
                        format!("duplicate qmatch label {}", value.variant.text),
                    ));
                }
            }
            if let Some(missing) = variants.iter().find(|label| !seen.contains(label)) {
                return Err(SourceError::new(
                    "type",
                    span,
                    format!("non-exhaustive qmatch: missing variant {missing}"),
                ));
            }
            return Ok(());
        }
        let cardinality = match &selector.kind {
            Kind::Unit => 1,
            Kind::Bit => 2,
            Kind::Bits(width) if width.terms.is_empty() && (0..=6).contains(&width.constant) => {
                1_u32 << (width.constant as u32)
            }
            _ => {
                return Err(SourceError::new(
                    "type",
                    span,
                    "qmatch ordinal selectors require Unit, Bit or closed Bits<n> fitting 64 arms",
                ));
            }
        };
        let mut seen = BTreeSet::new();
        for arm in arms {
            let QuantumLabel::Ordinal(label) = &arm.label else {
                return Err(SourceError::new(
                    "type",
                    arm.span,
                    "a built-in qmatch selector requires exact ordinal labels",
                ));
            };
            if *label >= cardinality {
                return Err(SourceError::new(
                    "type",
                    arm.span,
                    "qmatch ordinal is outside the selector's logical basis",
                ));
            }
            if !seen.insert(*label) {
                return Err(SourceError::new(
                    "type",
                    arm.span,
                    format!("duplicate qmatch ordinal {label}"),
                ));
            }
        }
        if seen.len() != cardinality as usize {
            return Err(SourceError::new(
                "type",
                span,
                "non-exhaustive qmatch ordinal table",
            ));
        }
        Ok(())
    }

    pub(super) fn qmatch(
        &mut self,
        selection: &QuantumMatch,
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        // The same lexical move accounting as qif rejects aliased owners,
        // including reuse of a logical owner whose physical width is zero.
        let selector = self.expr(&selection.selector, scope, None)?;
        let basis = selector.quantum_basis().ok_or_else(|| {
            let mut error = SourceError::new(
                "type",
                span,
                "qmatch selector requires one Q<A> owner for coherent selection on a separate target",
            );
            match &selector.kind {
                Kind::Bit => error
                    .message
                    .push_str(". To branch on an ordinary `Bit`, use ordinary `if`."),
                Kind::Nominal(nominal) if matches!(&nominal.body, Body::Enum(_)) => error
                    .message
                    .push_str(". To distinguish ordinary enum variants, use ordinary `match`."),
                _ => {}
            }
            error.with_control_flow_boundary(ControlFlowBoundary::QmatchSelector)
        })?;
        self.qmatch_labels(basis, &selection.arms, scope, span)?;
        let target = self.expr(&selection.target, scope, None)?;
        let target_basis = target.quantum_basis().ok_or_else(|| {
            SourceError::new("type", span, "qmatch target requires one Q<B> owner")
        })?;
        for arm in &selection.arms {
            self.coherent_arm(&arm.body, &selection.target, target_basis, scope)?;
        }
        self.obligation(span, ObligationKind::TransformedMeaning, scope)?;
        Ok(Ty::pair(selector, target))
    }

    pub(super) fn coherent_arm(
        &mut self,
        arm: &CoherentArm,
        target: &Expr,
        basis: &Ty,
        scope: &Scope,
    ) -> Result<()> {
        let block = match arm {
            CoherentArm::Operation(operation) => {
                let checked = self.qmatch_operation(operation, basis, target.span, scope)?;
                return access(&checked, Access::Controlled, operation.span);
            }
            CoherentArm::Block(block) => block,
        };
        let ExprKind::Name(name) = &target.kind else {
            return Err(SourceError::new(
                "ownership",
                target.span,
                "bind the target owner to a name before using it in an inline coherent arm",
            ));
        };
        let key = self.local(name).ok_or_else(|| {
            SourceError::new(
                "ownership",
                name.span,
                "inline coherent arm requires a target owner",
            )
        })?;
        let mut inner = scope.basis_scope(&self.program.budget, block.span)?;
        let expected = Ty::quantum(self.program.budget.copy_ty(block.span, basis)?);
        let identity = inner.next_binding.get();
        inner.next_binding.set(
            identity.checked_add(1).ok_or_else(|| {
                SourceError::new("limit", block.span, "binding identity overflow")
            })?,
        );
        inner.values.insert(
            self.program.budget.key(name.span, key)?,
            Binding {
                identity,
                ty: self.program.budget.copy_ty(block.span, &expected)?,
            },
        );
        let surrounding = std::mem::replace(&mut self.effects, BodyEffects::new(block.span));
        let checked = self.block(block, &mut inner, Some(&expected));
        let region = std::mem::replace(&mut self.effects, surrounding);
        checked?;
        if self.live_owner(&inner, block.span)?.is_some() {
            return Err(disposal_error(
                block.result.span,
                format!(
                    "inline coherent arm must consume and return target owner `{}`",
                    name.text
                ),
                QuantumOwnershipBoundary::ImplicitDisposal,
            ));
        }
        self.program
            .budget
            .charge(block.span, region.storage_cells() + 1)?;
        self.effects.merge(&region);
        self.program.unitary_regions.push((
            self.definition,
            block.span,
            region,
            "inline coherent arm body must be unitary",
        ));
        Ok(())
    }
}
