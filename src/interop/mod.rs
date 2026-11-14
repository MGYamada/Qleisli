//! Bounded, untrusted OpenQASM 3 / QIR adapters for closed terminal circuits.
//!
//! See the fixed interoperability contract for the accepted subset, QIS and limits. Imported
//! ownership is independently verified; translation correctness is not proved
//! by that check. Export never transfers Qleisli evidence to an external tool.

mod export;
mod openqasm;
mod placement;
mod profile;
mod qir;

use crate::AcceptedProgram;
use crate::frontend::ast::Span;
use std::fmt;

pub use openqasm::{import_openqasm3, import_openqasm3_with_kernel};

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

/// Resources checked by Lean for the exact OpenQASM text returned with them.
#[derive(Debug, PartialEq, Eq)]
pub struct OpenQasmResources {
    pub exact_work: usize,
    pub qubits: usize,
    pub resets: usize,
    pub gates: usize,
    pub swaps: usize,
    pub t_gates: usize,
    pub measurements: usize,
}

/// Export a closed typed workspace program and check the placement of the
/// emitted gates against its original source before returning resource counts.
/// The checked terminal subset includes workspace intervals in named calls.
pub fn export_openqasm3_with_resources(
    program: &AcceptedProgram,
) -> Result<(String, OpenQasmResources), InteropError> {
    profile::check_openqasm_result(program)?;
    let context = program.source_context().ok_or_else(|| {
        InteropError::unsupported("checked OpenQASM resources require original workspace source")
    })?;
    let intervals = placement::workspace_intervals(context, program.raw().operations.len())?;
    if intervals.is_empty() {
        return Err(InteropError::unsupported(
            "checked OpenQASM resources require at least one source workspace",
        ));
    }
    let (circuit, alignment) = profile::extract_with_alignment(program, &intervals)?;
    let text = openqasm::write(&circuit);
    let resources = program
        .check_openqasm_placement(text.as_bytes(), &alignment.encode())
        .map_err(|error| {
            let kind = match error.code {
                "limit" => InteropErrorKind::Limit,
                "unsupported" => InteropErrorKind::Unsupported,
                _ => InteropErrorKind::InvalidIr,
            };
            InteropError::new(kind, error.to_string())
        })?;
    Ok((text, resources))
}

/// Export a closed, verified terminal-profile program as OpenQASM 3.0.
/// Typed classical results use the checked measurement-bit order. Unit emits
/// no bits, and the target contains no nominal types or tuple metadata.
pub fn export_openqasm3(program: &AcceptedProgram) -> Result<String, InteropError> {
    profile::check_openqasm_result(program)?;
    Ok(openqasm::write(&profile::extract(program)?))
}

/// Export QIR 2.0 Base Profile text with the explicit QIS in the connection spec.
/// Standard LLVM assembly/verification and target support remain external gates.
pub fn export_qir_base(program: &AcceptedProgram) -> Result<String, InteropError> {
    program
        .portable_artifact()
        .map_err(|error| InteropError::unsupported(error.to_string()))?;
    Ok(qir::write(&profile::extract(program)?))
}
