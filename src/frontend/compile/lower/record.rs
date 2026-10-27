//! Untrusted ordinary record storage behind the unchanged source transport gate.
//! Original occurrences, caller frames and ordered declarations remain authoritative.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ast::RecordValue;
use crate::frontend::types::nominal::{Body, Field, Nominal};

impl Lowerer<'_, '_> {
    fn record_type(&mut self, module: &str, name: &Ident) -> Result<Ty, CompileError> {
        self.compiler.tick(module, name.span)?;
        let ResolvedUse::Global(Target::Type(id)) = self.compiler.locals().usage(name).target
        else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "record constructor requires its original concrete type occurrence",
            ));
        };
        let nominals = Arc::clone(&self.compiler.source.nominals);
        let original = nominals.get(&id).ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "record constructor lost its original nominal declaration",
            )
        })?;
        let owner = self.compiler.current_instance_owner().ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "record constructor lacks its active original function",
            )
        })?;
        self.compiler.close_body_type(owner, original, name.span)
    }

    fn record_index(
        &mut self,
        module: &str,
        nominal: &Nominal<u32>,
        fields: &[Field<u32>],
        name: &Ident,
    ) -> Result<usize, CompileError> {
        self.compiler.charge(
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
        let owner = self.compiler.current_instance_owner().ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "field access lacks its active original function",
            )
        })?;
        let caller = self.compiler.source.resolution.declaration(owner).module;
        let cost = self
            .compiler
            .source
            .resolution
            .module_name(caller)
            .len()
            .saturating_add(nominal.origin.module.len())
            .saturating_add(1);
        self.compiler.charge(module, name.span, cost)?;
        if !fields[index].public
            && self.compiler.source.resolution.module_name(caller) != nominal.origin.module
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

    fn record_child(
        &mut self,
        module: &str,
        span: Span,
        declared: &Ty,
        value: &Value,
    ) -> Result<(), CompileError> {
        self.compiler
            .charge(module, span, value.tree_size().nodes)?;
        if value.owns_quantum() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "ordinary record fields cannot retain quantum ownership",
            ));
        }
        self.validate_record_descendants(module, span, value)?;
        let actual = value.ty();
        if !super::super::operations::same_port_budgeted(declared, &actual, &mut |cells| {
            self.compiler.charge(module, span, cells)
        })? {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record child differs from its complete declared field type",
            ));
        }
        Ok(())
    }

    // The caller reserves the complete child traversal before entering here.
    // Tuple containers must not hide a malformed retained nominal child either.
    fn validate_record_descendants(
        &mut self,
        module: &str,
        span: Span,
        value: &Value,
    ) -> Result<(), CompileError> {
        match value {
            Value::Enumeration(ty, ids) => {
                let enum_shape = matches!(&ty.kind, Kind::Nominal(nominal)
                    if matches!(&nominal.body, Body::Enum(labels) if !labels.is_empty()));
                // This checks only storage coordinates. Symbolic IDs do not
                // establish a runtime ordinal or its logical domain membership.
                if !enum_shape || ty.basis_width() != u32::try_from(ids.len()).ok() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "record enum child requires its original nonempty domain and tag coordinates",
                    ));
                }
            }
            Value::Record(ty, fields) => self.validate_record(module, span, ty, fields)?,
            Value::Pair(a, b) => {
                self.validate_record_descendants(module, span, a)?;
                self.validate_record_descendants(module, span, b)?;
            }
            Value::Tuple(fields) => {
                for field in fields {
                    self.validate_record_descendants(module, span, field)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// A retained type alone must not hide a missing, mistyped or quantum child.
    /// This is an internal producer invariant, not independent native evidence.
    pub(super) fn validate_record(
        &mut self,
        module: &str,
        span: Span,
        ty: &Ty,
        values: &[Value],
    ) -> Result<(), CompileError> {
        let Kind::Nominal(nominal) = &ty.kind else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record storage lost its nominal type",
            ));
        };
        let Body::Record(fields) = &nominal.body else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record storage requires an original struct declaration",
            ));
        };
        self.compiler
            .charge(module, span, fields.len().saturating_add(values.len()))?;
        if fields.len() != values.len() {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record storage must retain every ordered field",
            ));
        }
        for (field, value) in fields.iter().zip(values) {
            self.record_child(module, span, &field.ty, value)?;
        }
        Ok(())
    }

    pub(super) fn record_value<E>(
        &mut self,
        module: &str,
        span: Span,
        record: &RecordValue<E>,
        env: &mut Env,
        evaluate: fn(&mut Self, &str, &E, &mut Env) -> Result<Value, CompileError>,
    ) -> Result<Value, CompileError> {
        let ty = self.record_type(module, &record.type_name)?;
        self.note_nominal(&ty, module, span)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record construction requires a nominal type",
            ));
        };
        let Body::Record(fields) = &nominal.body else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record construction requires an original struct declaration",
            ));
        };
        self.compiler.charge(
            module,
            span,
            fields
                .len()
                .saturating_mul(3)
                .saturating_add(record.fields.len())
                .saturating_add(1),
        )?;
        let mut slots: Vec<Option<Value>> = Vec::with_capacity(fields.len());
        slots.resize_with(fields.len(), || None);
        // Effects and owners follow the original written order. Only completed
        // values are placed in declaration order; no initializer is reordered.
        for written in &record.fields {
            let index = self.record_index(module, nominal, fields, &written.name)?;
            if slots[index].is_some() {
                return Err(self.error(
                    module,
                    written.name.span,
                    ErrorCode::TypeMismatch,
                    "record initializer repeats an original field",
                ));
            }
            let value = evaluate(self, module, &written.value, env)?;
            self.record_child(module, written.span, &fields[index].ty, &value)?;
            slots[index] = Some(value);
        }
        if slots.iter().any(Option::is_none) {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "record initializer must supply every original field",
            ));
        }
        let values = slots
            .into_iter()
            .map(|value| value.expect("complete record fields"))
            .collect();
        Ok(Value::Record(ty, values))
    }

    pub(super) fn record_field(
        &mut self,
        module: &str,
        field: &Ident,
        receiver: Value,
    ) -> Result<Value, CompileError> {
        let Value::Record(ty, values) = receiver else {
            return Err(self.error(
                module,
                field.span,
                ErrorCode::TypeMismatch,
                "field projection requires an ordinary record, never a quantum owner",
            ));
        };
        self.validate_record(module, field.span, &ty, &values)?;
        let Kind::Nominal(nominal) = &ty.kind else {
            unreachable!("validated record type")
        };
        let Body::Record(fields) = &nominal.body else {
            unreachable!("validated record declaration")
        };
        let index = self.record_index(module, nominal, fields, field)?;
        // The receiver has already been evaluated exactly once. All remaining
        // children are ordinary, so projection cannot silently discard an owner.
        Ok(values
            .into_iter()
            .nth(index)
            .expect("validated record index"))
    }
}
