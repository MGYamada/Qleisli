//! Structured source diagnostics for machine-facing frontend clients.
//!
//! Locations refer to the original source bytes. This module reports checks;
//! its records do not carry semantic evidence or authorize execution.

use std::path::PathBuf;

use super::ast::Span;
use super::compile::{CompileError, ErrorCode};

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
        let code = match error.code {
            ErrorCode::Project => "project",
            ErrorCode::UnknownName => "unknown_name",
            ErrorCode::RecursiveCall => "recursive_call",
            ErrorCode::TypeMismatch => "type_mismatch",
            ErrorCode::Arity => "arity",
            ErrorCode::Ownership => "ownership",
            ErrorCode::Effect => "effect",
            ErrorCode::InvalidEntry => "invalid_entry",
            ErrorCode::Unsupported => "unsupported",
            ErrorCode::Limit => "limit",
            ErrorCode::InvalidIr => "invalid_ir",
            ErrorCode::Capability => "capability",
            ErrorCode::Contract => "contract",
        };
        let primary = (error.span != Span::default()).then_some(SourceLocation {
            path: error.path,
            span: error.span,
            line: error.line,
            column: error.column,
        });
        Self {
            code,
            message: error.message,
            primary,
        }
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
