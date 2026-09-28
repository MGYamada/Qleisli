//! Bounded, untrusted OpenQASM 3 / QIR adapters for closed terminal circuits.
//!
//! See `docs/interop-m1.1.md` for the accepted subset, QIS and limits. Imported
//! ownership is independently verified; translation correctness is not proved
//! by that check. Export never transfers Qleisli evidence to an external tool.

mod openqasm;
mod profile;
mod qir;

use crate::VerifiedProgram;
use crate::frontend::ast::Span;
use std::fmt;

pub use openqasm::import_openqasm3;

/// Maximum UTF-8 source size accepted by the initial OpenQASM adapter.
pub const MAX_OPENQASM_BYTES: usize = 1 << 20;
pub(crate) const MAX_QUBITS: usize = 12;
pub(crate) const MAX_GATES: usize = 4096;
pub(crate) const MAX_TOKENS: usize = 65_536;
pub(crate) const MAX_OPERATIONS: usize = 65_536;

/// Stable categories for the initial adapter; no partial artifact is returned.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InteropErrorKind {
    Parse,
    Unsupported,
    Limit,
    InvalidIr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InteropError {
    pub kind: InteropErrorKind,
    pub message: String,
    /// Original UTF-8 byte range, when an import token identifies the failure.
    pub span: Option<Span>,
    /// Zero-based top-level raw operation index, when an export op fails.
    pub operation: Option<usize>,
}

impl InteropError {
    fn new(kind: InteropErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            span: None,
            operation: None,
        }
    }
    fn unsupported(message: impl Into<String>) -> Self {
        Self::new(InteropErrorKind::Unsupported, message)
    }
    fn limit(message: impl Into<String>) -> Self {
        Self::new(InteropErrorKind::Limit, message)
    }
    fn at(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }
}

impl fmt::Display for InteropError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.message)?;
        if let Some(span) = self.span {
            write!(f, " at bytes {}..{}", span.start, span.end)?;
        }
        if let Some(index) = self.operation {
            write!(f, " at raw operation {index}")?;
        }
        Ok(())
    }
}
impl std::error::Error for InteropError {}

/// Export a closed, verified terminal-profile program as OpenQASM 3.0.
pub fn export_openqasm3(program: &VerifiedProgram) -> Result<String, InteropError> {
    Ok(openqasm::write(&profile::extract(program)?))
}

/// Export QIR 2.0 Base Profile text with the explicit QIS in the connection spec.
/// Standard LLVM assembly/verification and target support remain external gates.
pub fn export_qir_base(program: &VerifiedProgram) -> Result<String, InteropError> {
    Ok(qir::write(&profile::extract(program)?))
}
