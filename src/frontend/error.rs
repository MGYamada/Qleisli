//! Shared preparation diagnostics; profile-specific conversions stay in adapters.
use super::ast::Span;
use std::fmt;

pub(super) type Result<T> = std::result::Result<T, Error>;

/// A preparation failure, with a half-open byte span in the retained module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub(super) code: &'static str,
    pub(super) module: Option<String>,
    pub(super) span: Span,
    pub(super) message: String,
}
impl Error {
    pub(in crate::frontend) fn new(
        code: &'static str,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code,
            module: None,
            span,
            message: message.into(),
        }
    }
    pub(super) fn in_module(mut self, module: &str) -> Self {
        if self.module.is_none() {
            self.module = Some(module.into());
        }
        self
    }
    pub fn code(&self) -> &str {
        self.code
    }
    pub fn module(&self) -> Option<&str> {
        self.module.as_deref()
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn message(&self) -> &str {
        &self.message
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}..{}: {}: {}",
            self.module.as_deref().unwrap_or("<source>"),
            self.span.start,
            self.span.end,
            self.code,
            self.message
        )
    }
}
impl std::error::Error for Error {}
