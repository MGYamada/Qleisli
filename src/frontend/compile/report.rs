//! Read-only observations of whole-project checks, with no acceptance authority.

use crate::interchange::native::NativeDecisionSummary;

/// Diagnostic metadata for a checked source collection. Concrete IR counts
/// exclude symbolic declarations and count each ordinary root once; generic
/// expansions are checked inside their enclosing roots. Native request counts
/// include individual contracts and do not assert whole-source preservation.
#[derive(Clone, Debug)]
pub struct ProjectCheckReport {
    native_decisions: NativeDecisionSummary,
    entry_request_checked: Option<bool>,
    concrete_local_roots: usize,
    concrete_bundled_roots: usize,
}

impl ProjectCheckReport {
    pub(super) fn new(
        result: super::ProjectResult,
        native_decisions: NativeDecisionSummary,
    ) -> Self {
        Self {
            entry_request_checked: result.entry.as_ref().map(|entry| entry.request().is_some()),
            concrete_local_roots: result.concrete_local_roots,
            concrete_bundled_roots: result.concrete_bundled_roots,
            native_decisions,
        }
    }

    /// Actual successful decisions, including temporary contract checks and
    /// all loaded bundled concrete functions. Paths are observed per invocation,
    /// not recanonicalized after checking and not binary identity attestations.
    pub fn native_decisions(&self) -> &NativeDecisionSummary {
        &self.native_decisions
    }

    /// Whether the entry's complete IR had an independent request. `None`
    /// denotes a library without an entry. Partial contracts do not set this.
    pub fn entry_request_checked(&self) -> Option<bool> {
        self.entry_request_checked
    }

    pub fn concrete_local_roots(&self) -> usize {
        self.concrete_local_roots
    }

    pub fn concrete_bundled_roots(&self) -> usize {
        self.concrete_bundled_roots
    }
}
