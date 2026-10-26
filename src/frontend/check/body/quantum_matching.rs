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
            SourceError::new("type", span, "qmatch selector requires one Q<A> owner")
        })?;
        self.qmatch_labels(basis, &selection.arms, scope, span)?;
        let target = self.expr(&selection.target, scope, None)?;
        let target_basis = target.quantum_basis().ok_or_else(|| {
            SourceError::new("type", span, "qmatch target requires one Q<B> owner")
        })?;
        for arm in &selection.arms {
            // Reuse qif's full type, Unitary provider and actual access path.
            // This also records every original arm's dependency/obligation.
            let operation = self.target_operation(&arm.operation, target_basis, scope)?;
            access(&operation, Access::Controlled, arm.operation.span)?;
        }
        self.obligation(span, ObligationKind::TransformedMeaning, scope)?;
        Ok(Ty::pair(selector, target))
    }
}
