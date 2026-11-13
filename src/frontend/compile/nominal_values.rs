//! Shared checked type and member identities for the original ordinary value.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ast::VariantValue;
use crate::frontend::types::nominal::{Body, Field, Nominal};

impl Compiler<'_> {
    pub(super) fn nominal_value_type(
        &mut self,
        module: &str,
        name: &Ident,
    ) -> Result<Ty, CompileError> {
        self.tick(module, name.span)?;
        let ResolvedUse::Global(Target::Type(id)) = self.locals().usage(name).target else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "nominal constructor requires its original concrete type occurrence",
            ));
        };
        let nominals = Arc::clone(&self.source.nominals);
        let original = nominals.get(&id).ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "nominal constructor lost its original nominal declaration",
            )
        })?;
        let owner = self.current_instance_owner().ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "nominal constructor lacks its active original function",
            )
        })?;
        self.close_body_type(owner, original, name.span)
    }

    pub(super) fn record_index(
        &mut self,
        module: &str,
        nominal: &Nominal<u32>,
        fields: &[Field<u32>],
        name: &Ident,
    ) -> Result<usize, CompileError> {
        self.charge(
            module,
            name.span,
            total_size(fields.iter().map(|field| {
                field
                    .name
                    .len()
                    .saturating_add(name.text.len())
                    .saturating_add(1)
            })),
        )?;
        let index = fields
            .iter()
            .position(|field| field.name == name.text)
            .ok_or_else(|| {
                self.error(
                    module,
                    name.span,
                    ErrorCode::TypeMismatch,
                    "field is absent from its original record declaration",
                )
            })?;
        let owner = self.current_instance_owner().ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "field access lacks its active original function",
            )
        })?;
        let caller = self.source.resolution.declaration(owner).module;
        let cost = self
            .source
            .resolution
            .module_name(caller)
            .len()
            .saturating_add(nominal.origin.module.len())
            .saturating_add(1);
        self.charge(module, name.span, cost)?;
        if !fields[index].public
            && self.source.resolution.module_name(caller) != nominal.origin.module
        {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Capability,
                "field is private to its original declaring module",
            ));
        }
        Ok(index)
    }

    /// Resolve the original constructor/label occurrence through the common
    /// source table. Spelling, width or a caller-supplied type is not authority.
    pub(super) fn enum_label(
        &mut self,
        module: &str,
        value: &VariantValue,
    ) -> Result<(Ty, usize), CompileError> {
        let ty = self.nominal_value_type(module, &value.type_name)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            return Err(self.error(
                module,
                value.type_name.span,
                ErrorCode::TypeMismatch,
                "enum label requires a nominal type",
            ));
        };
        let Body::Enum(labels) = &nominal.body else {
            return Err(self.error(
                module,
                value.type_name.span,
                ErrorCode::Unsupported,
                "enum label requires an original enum declaration",
            ));
        };
        self.charge(
            module,
            value.variant.span,
            total_size(labels.iter().map(|name| {
                name.len()
                    .saturating_add(value.variant.text.len())
                    .saturating_add(1)
            })),
        )?;
        let ordinal = labels
            .iter()
            .position(|label| *label == value.variant.text)
            .ok_or_else(|| {
                self.error(
                    module,
                    value.variant.span,
                    ErrorCode::TypeMismatch,
                    "enum label is absent from its original declaration",
                )
            })?;
        Ok((ty, ordinal))
    }
}
