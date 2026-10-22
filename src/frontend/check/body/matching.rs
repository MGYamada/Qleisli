//! Exhaustive ordinary selection over original nominal enum identities.
//! This source judgment does not authorize a runtime representation or handle.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::types::nominal::Body;

#[cfg(test)]
mod tests;

impl Checker<'_, '_> {
    fn match_labels<A>(
        &self,
        scrutinee: &Ty,
        arms: &[MatchArm<A>],
        scope: &Scope,
        span: Span,
    ) -> Result<()> {
        let Kind::Nominal(nominal) = &scrutinee.kind else {
            return Err(SourceError::new(
                "type",
                span,
                "ordinary match requires an ordinary enum; a live Q<T> cannot be inspected or implicitly measured",
            ));
        };
        let Body::Enum(variants) = &nominal.body else {
            return Err(SourceError::new(
                "type",
                span,
                "ordinary match requires an ordinary enum with exact variant labels",
            ));
        };
        self.program
            .budget
            .charge(span, arms.len() + variants.len() + 1)?;
        let mut seen = BTreeSet::new();
        for arm in arms {
            let label = self.variant_value(&arm.label)?;
            normalize::expect(
                &label,
                scrutinee,
                &scope.context,
                arm.label.type_name.span,
                &self.program.budget,
            )?;
            self.program
                .budget
                .charge(arm.label.variant.span, arm.label.variant.text.len() + 1)?;
            if !seen.insert(&arm.label.variant.text) {
                return Err(SourceError::new(
                    "type",
                    arm.label.variant.span,
                    format!("duplicate match arm {}", arm.label.variant.text),
                ));
            }
        }
        if let Some(missing) = variants.iter().find(|label| !seen.contains(label)) {
            return Err(SourceError::new(
                "type",
                span,
                format!("non-exhaustive match: missing variant {missing}"),
            ));
        }
        Ok(())
    }

    /// Inspect every arm even for a known constructor. Effects, dependencies,
    /// result types and the complete outer owner frame must survive selection.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn match_arms<A>(
        &mut self,
        scrutinee: &Ty,
        arms: &[MatchArm<A>],
        scope: &mut Scope,
        expected: Option<&Ty>,
        span: Span,
        evaluate: impl Fn(&mut Self, &A, &mut Scope, Option<&Ty>) -> Result<Ty>,
    ) -> Result<Ty> {
        self.match_labels(scrutinee, arms, scope, span)?;
        let mut joined: Option<(Ty, Scope)> = None;
        for arm in arms {
            let mut branch = scope.copy(&self.program.budget, arm.span)?;
            let actual = evaluate(self, &arm.body, &mut branch, expected)?;
            if let Some(expected) = expected {
                normalize::expect(
                    &actual,
                    expected,
                    &scope.context,
                    arm.span,
                    &self.program.budget,
                )?;
            }
            if let Some((result, previous)) = &joined {
                normalize::expect(
                    &actual,
                    result,
                    &scope.context,
                    arm.span,
                    &self.program.budget,
                )?;
                if !self.same_frame(&previous.values, &branch.values, arm.span)? {
                    return Err(SourceError::new(
                        "ownership",
                        arm.span,
                        "match arms must consume the same owners and preserve outer binding types",
                    ));
                }
            } else {
                joined = Some((actual, branch));
            }
        }
        // Source enums are nonempty; keep this defensive refusal for malformed ASTs.
        let (result, branch) = joined.ok_or_else(|| {
            SourceError::new("type", span, "ordinary match requires a nonempty enum")
        })?;
        self.program.budget.charge(span, branch.moved.len())?;
        scope.values = branch.values;
        scope.moved.extend(branch.moved);
        Ok(result)
    }
}
