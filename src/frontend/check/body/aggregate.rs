//! Ordinary source constructors and projection over original nominal identities.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::types::nominal::{Body, Field, Nominal};

#[cfg(test)]
mod tests;

impl Checker<'_, '_> {
    fn constructor_type(&self, name: &Ident) -> Result<Ty> {
        let ResolvedUse::Global(Target::Type(id)) =
            self.index().table.usage(self.index().usage(name)).target
        else {
            return Err(SourceError::new(
                "type",
                name.span,
                format!(
                    "{} is not a concrete ordinary finite constructor type",
                    name.text
                ),
            ));
        };
        self.program
            .budget
            .copy_ty(name.span, &self.program.nominals[&id])
    }

    pub(super) fn variant_value(&self, value: &VariantValue) -> Result<Ty> {
        let ty = self.constructor_type(&value.type_name)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            unreachable!("nominal registry")
        };
        let Body::Enum(variants) = &nominal.body else {
            return Err(SourceError::new(
                "type",
                value.type_name.span,
                "variant construction requires an enum type",
            ));
        };
        self.program.budget.charge(
            value.variant.span,
            variants.len() + value.variant.text.len(),
        )?;
        if !variants.contains(&value.variant.text) {
            return Err(SourceError::new(
                "type",
                value.variant.span,
                format!(
                    "unknown variant {} of {}",
                    value.variant.text, value.type_name.text
                ),
            ));
        }
        Ok(ty)
    }

    fn field_visible(
        &self,
        nominal: &Nominal<Linear>,
        field: &Field<Linear>,
        span: Span,
    ) -> Result<()> {
        let owner = self.program.resolution.declaration(self.definition).module;
        if !field.public && self.program.resolution.module_name(owner) != nominal.origin.module {
            return Err(SourceError::new(
                "visibility",
                span,
                format!("field {} of {} is private", field.name, nominal.origin.name),
            ));
        }
        Ok(())
    }

    pub(super) fn record_value<E>(
        &mut self,
        record: &RecordValue<E>,
        scope: &mut Scope,
        evaluate: impl Fn(&mut Self, &E, &mut Scope, &Ty) -> Result<Ty>,
    ) -> Result<Ty> {
        let ty = self.constructor_type(&record.type_name)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            unreachable!("nominal registry")
        };
        let Body::Record(fields) = &nominal.body else {
            return Err(SourceError::new(
                "type",
                record.type_name.span,
                "record construction requires a struct type",
            ));
        };
        self.program.budget.charge(
            record.type_name.span,
            fields.len() + record.fields.len() + 1,
        )?;
        let mut seen = BTreeSet::new();
        // Original source order controls evaluation and effect/owner transitions.
        // Declaration order remains in `ty`; never reorder the source expressions.
        for written in &record.fields {
            self.program
                .budget
                .charge(written.name.span, fields.len() + written.name.text.len())?;
            let field = fields
                .iter()
                .find(|field| field.name == written.name.text)
                .ok_or_else(|| {
                    SourceError::new(
                        "type",
                        written.name.span,
                        format!("unknown field {}", written.name.text),
                    )
                })?;
            if !seen.insert(&written.name.text) {
                return Err(SourceError::new(
                    "type",
                    written.name.span,
                    format!("duplicate field {}", written.name.text),
                ));
            }
            self.field_visible(nominal, field, written.name.span)?;
            let actual = evaluate(self, &written.value, scope, &field.ty)?;
            normalize::expect(
                &actual,
                &field.ty,
                &scope.context,
                written.span,
                &self.program.budget,
            )?;
        }
        if let Some(missing) = fields.iter().find(|field| !seen.contains(&field.name)) {
            return Err(SourceError::new(
                "type",
                record.type_name.span,
                format!("missing field {}", missing.name),
            ));
        }
        Ok(ty)
    }

    pub(super) fn field_value(&self, receiver: &Ty, field: &Ident) -> Result<Ty> {
        let Kind::Nominal(nominal) = &receiver.kind else {
            return Err(SourceError::new(
                "type",
                field.span,
                "field projection requires an ordinary record; Q<Record> is one quantum owner and cannot be projected or implicitly observed",
            ));
        };
        let Body::Record(fields) = &nominal.body else {
            return Err(SourceError::new(
                "type",
                field.span,
                "field projection requires an ordinary record",
            ));
        };
        self.program
            .budget
            .charge(field.span, fields.len() + field.text.len())?;
        let selected = fields
            .iter()
            .find(|candidate| candidate.name == field.text)
            .ok_or_else(|| {
                SourceError::new("type", field.span, format!("unknown field {}", field.text))
            })?;
        self.field_visible(nominal, selected, field.span)?;
        self.program.budget.copy_ty(field.span, &selected.ty)
    }
}
