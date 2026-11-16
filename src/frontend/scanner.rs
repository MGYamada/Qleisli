//! Shared physical scanner for the migrating source frontend.
//!
//! Words and numeral spellings have no semantic category here. Punctuation is
//! atomic; the common lexer joins adjacent marks into source tokens.
//! No backend, keyword table, numeric value or grammar is selected here.

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
    ForbiddenScalar(&'static str, char),
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
        if let Some(kind) = forbidden_character(ch) {
            return Err(ScanError {
                kind,
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
        } else if "[]{}(),;:<>+-*=^|!.#".contains(ch) {
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
        debug_assert!(suffix.is_ascii() && "[]{}(),;:<>+-*=^|!.#".contains(suffix));
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
                self.comment_character(ch)?;
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
                    self.comment_character(ch)?;
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

    fn comment_character(&self, ch: char) -> Result<(), ScanError> {
        let kind = if ch == '\r' && !self.source[self.pos..].starts_with("\r\n") {
            Some(ErrorKind::Forbidden(
                "bare carriage return is forbidden; use LF or CRLF",
            ))
        } else if matches!(ch, ' ' | '\t' | '\n' | '\r') {
            None
        } else {
            forbidden_character(ch)
        };
        if let Some(kind) = kind {
            Err(ScanError {
                kind,
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

fn forbidden_character(ch: char) -> Option<ErrorKind> {
    if matches!(
        ch,
        '\u{061c}' | '\u{200e}' | '\u{200f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}'
    ) {
        Some(ErrorKind::ForbiddenScalar(
            "bidirectional control character is forbidden",
            ch,
        ))
    } else if is_default_ignorable_or_format(ch) {
        Some(ErrorKind::ForbiddenScalar(
            "default-ignorable or format character is forbidden",
            ch,
        ))
    } else if matches!(
        ch,
        '\u{000b}' | '\u{000c}' | '\u{0085}' | '\u{2028}' | '\u{2029}'
    ) {
        Some(ErrorKind::Forbidden(
            "unsupported line separator is forbidden",
        ))
    } else if ch.is_whitespace() {
        Some(ErrorKind::Forbidden(
            "unsupported whitespace; use ASCII space, tab, LF, or CRLF",
        ))
    } else if ch.is_control() {
        Some(ErrorKind::Forbidden("control character is forbidden"))
    } else {
        None
    }
}

// Unicode 17.0.0: union of Default_Ignorable_Code_Point in DerivedCoreProperties.txt
// and General_Category=Cf in extracted/DerivedGeneralCategory.txt. See NOTICE.
// The fixed table keeps behavior independent of the Rust toolchain's Unicode version.
fn is_default_ignorable_or_format(ch: char) -> bool {
    matches!(
        ch,
        '\u{00ad}'
            | '\u{034f}'
            | '\u{0600}'..='\u{0605}'
            | '\u{061c}'
            | '\u{06dd}'
            | '\u{070f}'
            | '\u{0890}'..='\u{0891}'
            | '\u{08e2}'
            | '\u{115f}'..='\u{1160}'
            | '\u{17b4}'..='\u{17b5}'
            | '\u{180b}'..='\u{180f}'
            | '\u{200b}'..='\u{200f}'
            | '\u{202a}'..='\u{202e}'
            | '\u{2060}'..='\u{206f}'
            | '\u{3164}'
            | '\u{fe00}'..='\u{fe0f}'
            | '\u{feff}'
            | '\u{ffa0}'
            | '\u{fff0}'..='\u{fffb}'
            | '\u{110bd}'
            | '\u{110cd}'
            | '\u{13430}'..='\u{1343f}'
            | '\u{1bca0}'..='\u{1bca3}'
            | '\u{1d173}'..='\u{1d17a}'
            | '\u{e0000}'..='\u{e0fff}'
    )
}
