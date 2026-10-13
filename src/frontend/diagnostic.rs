//! Structured source diagnostics for machine-facing frontend clients.
//!
//! Locations refer to the original source bytes. This module reports checks;
//! its records do not carry semantic evidence or authorize execution.

use std::path::PathBuf;

use super::ast::Span;
use super::compile::CompileError;

pub(crate) const CONTROL_ACCESS_EXPLANATION: &str = "ctrl requires computational-basis sector preservation, not read-only access; phase kickback is permitted; use excl for arbitrary coherent access";

pub(crate) const UNSUPPORTED_REFERENCE_EXPLANATION: &str = "Rust-style references are not supported; for quantum access, excl grants arbitrary coherent access, while ctrl requires computational-basis sector preservation, not an unchanged quantum state. Phase kickback and entanglement are permitted; do not mechanically replace & with ctrl";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceLocation {
    /// Original source identity, before a CLI makes it project-relative.
    pub path: PathBuf,
    pub span: Span,
    /// One-based Unicode scalar coordinates, with CRLF counted as one newline.
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    /// A snake_case category from version 1 of `qleisli.result`.
    pub code: &'static str,
    pub message: String,
    /// None for failures without a source span, including missing entry points.
    pub primary: Option<SourceLocation>,
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
                code: native_code,
                message: "rejected".into(),
                json_pointer: pointer.into(),
            };
            let source = CompileError {
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
