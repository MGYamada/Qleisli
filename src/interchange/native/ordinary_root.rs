//! The same private native decision binds the actual typed result and graph.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{execution_view::finite::ordinary_root, native_packet::View};

#[cfg(test)]
mod tests;

impl Kernel {
    /// Independently check a closed ordinary-result root. No old-mode fallback,
    /// public success receipt or same-width type erasure authorizes execution.
    pub fn check_ordinary_root(&self, artifact: &[u8], request: &[u8]) -> Result<Checked> {
        let subject = self.subject(artifact, Some(request))?;
        let request = Arc::new(super::super::ordinary_root::Request::decode(
            subject
                .request
                .as_deref()
                .expect("original ordinary request"),
        )?);
        let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
        let decoded = Arc::new(super::super::decode_subject_with_types(
            &subject,
            &mut budget,
            None,
            Some(&request),
        )?);
        let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root])?;
        let prepared = Prepared {
            subject: Arc::clone(&subject),
            decoded,
            derived_effect,
            output_ports,
        };
        let graph = ordinary_root::complete(prepared.graph(), &request)?;
        let native = Self::submit_subject(
            subject,
            "--ordinary-root-check",
            Some(View {
                graph: &graph,
                caller: None,
            }),
        )?;
        let mut checked = prepared.bind(native)?;
        checked.imported.program.ordinary_result = Some(request);
        Ok(checked)
    }
}
