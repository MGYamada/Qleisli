//! One immutable original-source request and compared graph per fresh decision.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{execution_view::finite::qmatch, native_packet::View, qmatch::Request};

#[cfg(test)]
mod tests;

/// Internal named-arm component acceptance. No public constructor, serialized
/// receipt import, raw AcceptedProgram conversion or inverse/control access.
#[derive(Debug)]
pub struct QmatchChecked {
    checked: Checked,
    request: Arc<Request>,
}

impl QmatchChecked {
    pub fn artifact(&self) -> &[u8] {
        self.checked.artifact()
    }
    pub fn request_bytes(&self) -> &[u8] {
        self.checked.request().expect("qmatch requires a request")
    }
    pub fn request(&self) -> &Request {
        &self.request
    }
    pub fn native(&self) -> &NativeChecked {
        &self.checked.imported.program.native
    }
}

fn prepare(subject: Arc<Subject>, request: &Request) -> Result<Prepared> {
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    let decoded = Arc::new(super::super::decode_subject_with_types(
        &subject,
        &mut budget,
        None,
        None,
        Some(request),
    )?);
    let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root])?;
    Ok(Prepared {
        subject,
        decoded,
        derived_effect,
        output_ports,
    })
}

impl Kernel {
    /// Fresh execution-only checking of the internal named-arm source profile.
    /// A missing/incompatible/failed checker refuses without an old-mode retry.
    pub fn check_qmatch_source(&self, artifact: &[u8], request: &[u8]) -> Result<QmatchChecked> {
        let subject = self.subject(artifact, Some(request))?;
        let request = Arc::new(Request::decode(
            subject.request.as_deref().expect("original request"),
        )?);
        let prepared = prepare(Arc::clone(&subject), &request)?;
        let graph = qmatch::complete(prepared.graph(), &request)?;
        let native = Self::submit_subject(
            subject,
            "--qmatch-source-check",
            Some(View {
                graph: &graph,
                caller: None,
            }),
        )?;
        let checked = prepared.bind(native)?;
        Ok(QmatchChecked { checked, request })
    }
}
