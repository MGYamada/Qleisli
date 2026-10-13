//! Host transport capacities, separate from native acceptance/exact-work budgets.
//! These fixed response ceilings preserve the existing wire compatibility limits;
//! they are neither producer allowances nor program resource certificates.
use std::time::Duration;

/// Finite and hierarchical adapters select named transport profiles. An
/// arithmetic/acceptance work count cannot be passed as bytes to this API.
#[derive(Clone, Copy)]
pub(crate) struct TransportLimits {
    timeout: Duration,
    response_bytes: usize,
}

impl TransportLimits {
    pub(crate) const FINITE: Self = Self {
        timeout: Duration::from_secs(60),
        response_bytes: 256,
    };
    pub(crate) const HIERARCHY_INSPECTION: Self = Self {
        timeout: Duration::from_secs(60),
        response_bytes: 1_100_000,
    };
    pub(crate) const HIERARCHY_REQUEST: Self = Self {
        timeout: Duration::from_secs(60),
        response_bytes: 2_200_000,
    };

    pub(crate) fn invoke<T>(
        self,
        executable: &std::path::Path,
        packet: Vec<u8>,
        mode: &str,
        decode: impl FnOnce(&[u8]) -> super::Result<T>,
    ) -> super::Result<T> {
        super::invoke(
            executable,
            packet,
            mode,
            self.timeout,
            self.response_bytes,
            decode,
        )
    }

    // Test deadlines may be shorter without changing any production profile.
    #[cfg(test)]
    pub(crate) fn with_timeout(self, timeout: Duration) -> Self {
        Self { timeout, ..self }
    }
}
