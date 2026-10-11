//! Shared physical scanner for the migrating source frontend.
//!
//! Words and numeral spellings have no semantic category here. Punctuation is
//! atomic; temporary parser adapters join adjacent marks into their historical
//! tokens. No backend, keyword table, numeric value or grammar is selected here.

use super::ast::Span;
use super::documentation::{DocComment, DocStyle};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Word,
    Numeral,
    Punctuation(char),
    Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Token {
    pub kind: Kind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ErrorKind {
    Forbidden(&'static str),
    Unexpected(char),
    UnterminatedComment,
    CommentDepth(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ScanError {
    pub kind: ErrorKind,
    pub span: Span,
}

pub(super) struct Scanner<'a> {
    source: &'a str,
    pos: usize,
    max_comment_depth: Option<usize>,
    retain_docs: bool,
    docs: Vec<DocComment>,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str, max_comment_depth: Option<usize>, retain_docs: bool) -> Self {
        Self {
            source,
            pos: 0,
            max_comment_depth,
            retain_docs,
            docs: Vec::new(),
        }
    }

    pub fn into_docs(self) -> Vec<DocComment> {
        self.docs
    }

    pub fn next(&mut self) -> Result<Token, ScanError> {
        loop {
            let Some(ch) = self.peek() else {
                return Ok(Token {
                    kind: Kind::Eof,
                    span: Span::new(self.pos, self.pos),
                });
            };
            if ch == '\r' && !self.source[self.pos..].starts_with("\r\n") {
                return Err(ScanError {
                    kind: ErrorKind::Forbidden("bare carriage return is forbidden; use LF or CRLF"),
                    span: Span::new(self.pos, self.pos + 1),
                });
            }
            if matches!(ch, ' ' | '\t' | '\n' | '\r') {
                self.bump();
            } else if self.source[self.pos..].starts_with("//")
                || self.source[self.pos..].starts_with("/*")
            {
                if let Some(comment) = self.comment(self.retain_docs)? {
                    self.docs.push(comment);
                }
            } else {
                break;
            }
        }
        let start = self.pos;
        let ch = self.peek().expect("nonempty after trivia");
        if let Some(message) = forbidden_character(ch) {
            return Err(ScanError {
                kind: ErrorKind::Forbidden(message),
                span: Span::new(start, start + ch.len_utf8()),
            });
        }
        self.bump();
        let kind = if ch.is_ascii_alphabetic() || ch == '_' {
            while self
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.bump();
            }
            Kind::Word
        } else if ch.is_ascii_digit() {
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
            }
            Kind::Numeral
        } else if "[]{}(),;:<>+-*=^|!.".contains(ch) {
            Kind::Punctuation(ch)
        } else {
            return Err(ScanError {
                kind: ErrorKind::Unexpected(ch),
                span: Span::new(start, self.pos),
            });
        };
        Ok(Token {
            kind,
            span: Span::new(start, self.pos),
        })
    }

    /// Join only an immediately adjacent ASCII punctuation mark. Trivia is not
    /// scanned here: `: /* text */ :` must never become `::`.
    pub fn join(&mut self, token: &mut Token, suffix: char) -> bool {
        debug_assert!(matches!(token.kind, Kind::Punctuation(_)));
        debug_assert!(suffix.is_ascii() && "[]{}(),;:<>+-*=^|!.".contains(suffix));
        debug_assert_eq!(token.span.end, self.pos);
        if self.peek() == Some(suffix) {
            self.bump();
            token.span.end = self.pos;
            true
        } else {
            false
        }
    }

    fn comment(&mut self, retain_docs: bool) -> Result<Option<DocComment>, ScanError> {
        let start = self.pos;
        let rest = &self.source[start..];
        let line = rest.starts_with("//");
        let style = if rest.starts_with("//!") || rest.starts_with("/*!") {
            Some(DocStyle::Inner)
        } else if (rest.starts_with("///") && !rest.starts_with("////"))
            || (rest.starts_with("/**") && !rest.starts_with("/***") && !rest.starts_with("/**/"))
        {
            Some(DocStyle::Outer)
        } else {
            None
        };
        self.pos += 2;
        let content_end;
        let span_end;
        if line {
            while let Some(ch) = self.peek() {
                if ch == '\n' {
                    break;
                }
                self.comment_character(ch, style.is_some())?;
                self.bump();
            }
            // CRLF is one line ending, but all source offsets stay original.
            content_end =
                if self.source[start..self.pos].ends_with('\r') && self.peek() == Some('\n') {
                    self.pos - 1
                } else {
                    self.pos
                };
            span_end = content_end;
        } else {
            let mut depth = 1usize;
            while depth != 0 {
                if self.source[self.pos..].starts_with("/*") {
                    depth += 1;
                    self.pos += 2;
                    if self.max_comment_depth.is_some_and(|limit| depth > limit) {
                        return Err(ScanError {
                            kind: ErrorKind::CommentDepth(self.max_comment_depth.unwrap()),
                            span: Span::new(start, self.pos),
                        });
                    }
                } else if self.source[self.pos..].starts_with("*/") {
                    depth -= 1;
                    self.pos += 2;
                } else if let Some(ch) = self.peek() {
                    self.comment_character(ch, style.is_some())?;
                    self.bump();
                } else {
                    return Err(ScanError {
                        kind: ErrorKind::UnterminatedComment,
                        span: Span::new(start, self.pos),
                    });
                }
            }
            content_end = self.pos - 2;
            span_end = self.pos;
        }
        Ok(if retain_docs {
            style.map(|style| DocComment {
                style,
                text: self.source[start + 3..content_end].replace("\r\n", "\n"),
                span: Span::new(start, span_end),
            })
        } else {
            None
        })
    }

    fn comment_character(&self, ch: char, _doc: bool) -> Result<(), ScanError> {
        let message = if ch == '\r' && !self.source[self.pos..].starts_with("\r\n") {
            Some("bare carriage return is forbidden; use LF or CRLF")
        } else if matches!(ch, ' ' | '\t' | '\n' | '\r') {
            None
        } else {
            forbidden_character(ch)
        };
        if let Some(message) = message {
            Err(ScanError {
                kind: ErrorKind::Forbidden(message),
                span: Span::new(self.pos, self.pos + ch.len_utf8()),
            })
        } else {
            Ok(())
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    fn bump(&mut self) {
        if let Some(ch) = self.peek() {
            self.pos += ch.len_utf8();
        }
    }
}

fn forbidden_character(ch: char) -> Option<&'static str> {
    if matches!(
        ch,
        '\u{061c}' | '\u{200e}' | '\u{200f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}'
    ) {
        Some("bidirectional control character is forbidden")
    } else if matches!(
        ch,
        '\u{000b}' | '\u{000c}' | '\u{0085}' | '\u{2028}' | '\u{2029}'
    ) {
        Some("unsupported line separator is forbidden")
    } else if ch.is_whitespace() {
        Some("unsupported whitespace; use ASCII space, tab, LF, or CRLF")
    } else if ch.is_control() {
        Some("control character is forbidden")
    } else {
        None
    }
}
