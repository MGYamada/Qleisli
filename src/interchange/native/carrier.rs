//! A private typed handle retains the exact compared graph and request objects.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::carrier::Request;
use crate::interchange::{execution_view::finite::carrier, native_packet::View};

#[cfg(test)]
mod tests;

/// Fresh pure carrier/body acceptance, separate from ordinary source execution.
/// No public constructor, receipt import, inverse/control or raw-handle escape.
#[derive(Debug)]
pub struct CarrierChecked {
    checked: Checked,
    request: Arc<Request>,
}

impl CarrierChecked {
    pub fn artifact(&self) -> &[u8] {
        self.checked.artifact()
    }
    pub fn request_bytes(&self) -> &[u8] {
        self.checked
            .request()
            .expect("carrier requires an original request")
    }
    pub fn request(&self) -> &Request {
        &self.request
    }
    pub fn native(&self) -> &NativeChecked {
        &self.checked.imported.program.native
    }
    /// The exact retained native-compared root, for the source-step adapter.
    /// This grants no public Raw execution handle or inverse/control access.
    pub(crate) fn raw(&self) -> &RawProgram {
        self.checked.imported.program.raw()
    }
}

impl Kernel {
    /// Check an internal typed pure request against the actual QIRF graph.
    /// Unsupported original type syntax rejects; there is no erasing fallback.
    pub fn check_carrier(&self, artifact: &[u8], request: &[u8]) -> Result<CarrierChecked> {
        let subject = self.subject(artifact, Some(request))?;
        let request = Arc::new(Request::decode(
            subject.request.as_deref().expect("original request"),
        )?);
        let prepared = Prepared::with_carrier(Arc::clone(&subject), Some(&request))?;
        let graph = carrier::complete(prepared.graph(), &request)?;
        let native = Self::submit_subject(
            subject,
            "--carrier-pure-check",
            Some(View {
                graph: &graph,
                caller: None,
            }),
        )?;
        let checked = prepared.bind(native)?;
        Ok(CarrierChecked { checked, request })
    }
}
