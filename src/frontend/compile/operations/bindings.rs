//! One concrete actual uses the same contract gates in every adapter.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;

impl Compiler<'_> {
    /// Validate this actual even when a sibling is deferred or the formal is
    /// unused. A required contract is source metadata; requested access still
    /// reaches the actual operation's existing steps/raw and native gates.
    pub(in crate::frontend::compile) fn validate_required_operation(
        &mut self,
        required: &RequiredOperation,
        operation: &Operation,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        let mut work = self.work;
        let same_ports = (|| {
            let mut charge = |cells| self.charge_at(&mut work, module, span, cells);
            Ok::<_, CompileError>(
                same_port_budgeted(&operation.basis, &required.basis, &mut charge)?
                    && same_port_budgeted(&operation.codomain, &required.codomain, &mut charge)?,
            )
        })();
        self.work = work;
        if !same_ports? {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                format!("static argument has a different exact basis tree: expected `Op<{}>`, found `Op<{}>`", required.basis, operation.basis),
            ));
        }
        let mut work = self.work;
        let same_meaning = match required.meaning.as_ref() {
            Some(meaning) => {
                same_meaning_budgeted(Some(meaning), operation.meaning.as_ref(), &mut |cells| {
                    self.charge_at(&mut work, module, span, cells)
                })
            }
            None => Ok(true),
        };
        self.work = work;
        if !same_meaning? {
            return Err(self.error(
                module,
                span,
                ErrorCode::Contract,
                "static argument does not establish the required phase-fixed meaning",
            ));
        }
        for access in [Access::Apply, Access::Adjoint, Access::Controlled] {
            if required.access[access_index(access)] {
                if operation.needs_raw() {
                    operation.raw(module, span, access, self)?;
                } else {
                    operation.steps(module, span, access, self)?;
                }
            }
        }
        Ok(())
    }
}
