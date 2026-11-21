//! Structured source diagnostics for machine-facing frontend clients.
//!
//! Locations refer to the original source bytes. This module reports checks;
//! its records do not carry semantic evidence or authorize execution.

use std::path::{Path, PathBuf};

use super::ast::Span;
use super::compile::CompileError;
use super::types::{Stage, Type};

pub(crate) const CONTROL_ACCESS_EXPLANATION: &str = "ctrl requires computational-basis sector preservation, not read-only access; phase kickback is permitted; use excl for arbitrary coherent access";

pub(crate) const UNSUPPORTED_REFERENCE_EXPLANATION: &str = "Rust-style references are not supported; for quantum access, excl grants arbitrary coherent access, while ctrl requires computational-basis sector preservation, not an unchanged quantum state. Phase kickback and entanglement are permitted; do not mechanically replace & with ctrl";

pub(super) fn static_operand_mismatch<N: std::fmt::Display + PartialEq>(
    expected: &Type<N>,
    actual: &Type<N>,
    basis: bool,
) -> String {
    let shown = |ty: &Type<N>| {
        if basis {
            format!("Q<{}>", ty.display(Stage::Basis))
        } else {
            ty.display(Stage::Runtime).to_string()
        }
    };
    let mut message = format!(
        "static operation argument type mismatch: expected `{}`, found `{}`",
        shown(expected),
        shown(actual)
    );
    let bases = if basis {
        Some((expected, actual))
    } else {
        expected.quantum_basis().zip(actual.quantum_basis())
    };
    if let Some((expected, actual)) = bases {
        let (expected_leaves, expected_binary) = product_leaves(expected);
        let (actual_leaves, actual_binary) = product_leaves(actual);
        if expected_leaves.len() > 1 && expected_leaves == actual_leaves {
            message.push_str(". Tuple nesting is significant.");
            if expected_binary && actual_binary {
                message.push_str(" Regroup the register with `split` and `join`.");
            } else {
                message.push_str(
                    " Reshape with a supported explicit basis map that preserves leaf order, or use a matching declared interface.",
                );
            }
        }
    }
    message
}

fn product_leaves<N>(basis: &Type<N>) -> (Vec<&Type<N>>, bool) {
    let mut pending = vec![basis];
    let mut leaves = Vec::new();
    let mut binary = true;
    while let Some(node) = pending.pop() {
        if let Some(fields) = node.tuple_fields() {
            binary &= fields.len() == 2;
            pending.extend(fields.iter().rev());
        } else {
            leaves.push(node);
        }
    }
    (leaves, binary)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceLocation {
    /// Original source identity, before a CLI makes it project-relative.
    pub path: PathBuf,
    pub span: Span,
    /// One-based Unicode scalar coordinates, with CRLF counted as one newline.
    pub line: usize,
    pub column: usize,
}

impl SourceLocation {
    /// Locate a UTF-8 byte span in the original source, counting CRLF as one newline.
    /// Returns `None` for inverted, out-of-bounds or non-character-boundary spans.
    pub fn from_span(path: &Path, source: &str, span: Span) -> Option<Self> {
        source.get(span.start..span.end)?;
        let (line, column) = coordinates(source, span);
        Some(Self {
            path: path.into(),
            span,
            line,
            column,
        })
    }
}

/// Why a diagnostic teaches the boundary between affine and linear ownership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuantumOwnershipBoundary {
    /// An unresolved Rust disposal spelling. No argument type was inferred.
    UnresolvedDisposal,
    ImplicitDisposal,
    CleanWorkspaceReturn,
    DirtyWorkspaceReturn,
    ComputedWorkspaceReturn,
}

impl QuantumOwnershipBoundary {
    pub fn reason(self) -> &'static str {
        match self {
            Self::UnresolvedDisposal => "unresolved_disposal",
            Self::ImplicitDisposal => "implicit_quantum_disposal",
            Self::CleanWorkspaceReturn => "clean_workspace_return",
            Self::DirtyWorkspaceReturn => "dirty_workspace_return",
            Self::ComputedWorkspaceReturn => "computed_workspace_return",
        }
    }
}

/// The construct where a classical or coherent quantum control contract failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlFlowBoundary {
    IfCondition,
    QifControl,
    MatchSelector,
    QmatchSelector,
    ForCarry,
    QforCarry,
}

impl ControlFlowBoundary {
    pub fn reason(self) -> &'static str {
        match self {
            Self::IfCondition => "if_condition",
            Self::QifControl => "qif_control",
            Self::MatchSelector => "match_selector",
            Self::QmatchSelector => "qmatch_selector",
            Self::ForCarry => "for_carry",
            Self::QforCarry => "qfor_carry",
        }
    }
}

/// A typed explanation attached to an existing source rejection.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticBoundary {
    QuantumOwnership(QuantumOwnershipBoundary),
    ControlFlow(ControlFlowBoundary),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    /// A snake_case category from version 1 of `qleisli.result`.
    pub code: &'static str,
    pub message: String,
    /// None for failures without a source span, including missing entry points.
    pub primary: Option<SourceLocation>,
    /// Exact equation detail, when bounded reconstruction found a mismatch.
    pub counterexample: Option<Box<crate::contract::EquationCounterexample>>,
    /// The source rule explained by this diagnostic, when one was identified.
    pub boundary: Option<DiagnosticBoundary>,
}

impl Diagnostic {
    pub(crate) fn from_compile(error: CompileError) -> Self {
        let code = error.code.as_str();
        let primary = (error.span != Span::default()).then_some(SourceLocation {
            path: error.path,
            span: error.span,
            line: error.line,
            column: error.column,
        });
        Self {
            code,
            message: without_repeated_category(code, error.message),
            primary,
            counterexample: error.counterexample,
            boundary: error.boundary,
        }
    }
}

pub(super) fn without_repeated_category(code: &str, message: String) -> String {
    // Interchange Display includes its category and optional JSON pointer.
    // Preserve a distinct nested category, but do not repeat our own category
    // in structured text/JSON. This does not alter native error classification.
    if let Some(detail) = message.strip_prefix(&format!("{code}: ")) {
        detail.to_owned()
    } else if let Some(detail) = message.strip_prefix(&format!("{code} at ")) {
        format!("at {detail}")
    } else {
        message
    }
}

pub(crate) fn coordinates(source: &str, span: Span) -> (usize, usize) {
    let mut line = 1;
    let mut column = 1;
    let mut previous_cr = false;
    for ch in source.get(..span.start).unwrap_or("").chars() {
        match ch {
            '\r' => {
                line += 1;
                column = 1;
            }
            '\n' => {
                if !previous_cr {
                    line += 1;
                }
                column = 1;
            }
            _ => column += 1,
        }
        previous_cr = ch == '\r';
    }
    (line, column)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ErrorCode;

    #[test]
    fn source_location_validates_byte_spans_and_counts_unicode_columns() {
        let text = "a\r\nβx";
        let path = Path::new("program.qasm");
        let location = SourceLocation::from_span(path, text, Span { start: 5, end: 6 }).unwrap();
        assert_eq!((location.line, location.column), (2, 2));
        for (start, end) in [(4, 5), (3, 4), (6, 5), (5, 7)] {
            assert!(SourceLocation::from_span(path, text, Span { start, end }).is_none());
        }
    }

    #[test]
    fn native_diagnostic_conversion_preserves_pointers_and_distinct_causes() {
        for (native_code, pointer, expected) in [
            ("invalid_ir", "", "rejected"),
            (
                "invalid_ir",
                "/programs/0/ops/1",
                "at /programs/0/ops/1: rejected",
            ),
            ("contract", "/request", "contract at /request: rejected"),
        ] {
            let native = crate::interchange::Error {
                counterexample: None,
                code: native_code,
                message: "rejected".into(),
                json_pointer: pointer.into(),
            };
            let source = CompileError {
                counterexample: None,
                boundary: None,
                code: ErrorCode::InvalidIr,
                path: "module.qli".into(),
                span: Span::new(8, 12),
                line: 2,
                column: 3,
                message: native.to_string(),
            };
            let diagnostic = Diagnostic::from_compile(source);
            assert_eq!(diagnostic.code, "invalid_ir");
            assert_eq!(diagnostic.message, expected);
            assert_eq!(
                diagnostic.primary,
                Some(SourceLocation {
                    path: "module.qli".into(),
                    span: Span::new(8, 12),
                    line: 2,
                    column: 3,
                })
            );
        }
    }
}
