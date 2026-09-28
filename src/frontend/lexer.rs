//! ASCII-keyword lexer with UTF-8 byte positions.

use super::ast::Span;
use super::documentation::{DocComment, DocStyle};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Use,
    Pub,
    Basis,
    Iso,
    Unitary,
    Observe,
    Fn,
    Let,
    If,
    Else,
    Do,
    Pure,
    WithComputed,
    ApplyContract,
    Adjoint,
    RepeatStatic,
    Qif,
    True,
    False,
    Natural(String),
    FatArrow,
    Not,
    Xor,
    And,
    Unit,
    Bit,
    CBit,
    Q,
    Zero,
    One,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LAngle,
    RAngle,
    Comma,
    Colon,
    DoubleColon,
    Semicolon,
    Equals,
    Arrow,
    LeftArrow,
    Pipe,
    Eof,
}

/// Shared by the lexer and module-path validation so a reserved word cannot
/// become a local module name that source code cannot import.
pub(crate) fn keyword_kind(name: &str) -> Option<TokenKind> {
    Some(match name {
        "use" => TokenKind::Use,
        "pub" => TokenKind::Pub,
        "basis" => TokenKind::Basis,
        "iso" => TokenKind::Iso,
        "unitary" => TokenKind::Unitary,
        "observe" => TokenKind::Observe,
        "fn" => TokenKind::Fn,
        "let" => TokenKind::Let,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "do" => TokenKind::Do,
        "pure" => TokenKind::Pure,
        "with_computed" => TokenKind::WithComputed,
        "apply_contract" => TokenKind::ApplyContract,
        "adjoint" => TokenKind::Adjoint,
        "repeat_static" => TokenKind::RepeatStatic,
        "qif" => TokenKind::Qif,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "not" => TokenKind::Not,
        "xor" => TokenKind::Xor,
        "and" => TokenKind::And,
        "Unit" => TokenKind::Unit,
        "Bit" => TokenKind::Bit,
        "CBit" => TokenKind::CBit,
        "Q" => TokenKind::Q,
        _ => return None,
    })
}

impl TokenKind {
    pub fn description(&self) -> &'static str {
        match self {
            Self::Ident(_) => "identifier",
            Self::Use => "`use`",
            Self::Pub => "`pub`",
            Self::Basis => "`basis`",
            Self::Iso => "`iso`",
            Self::Unitary => "`unitary`",
            Self::Observe => "`observe`",
            Self::Fn => "`fn`",
            Self::Let => "`let`",
            Self::If => "`if`",
            Self::Else => "`else`",
            Self::Do => "`do`",
            Self::Pure => "`pure`",
            Self::WithComputed => "`with_computed`",
            Self::ApplyContract => "`apply_contract`",
            Self::Adjoint => "`adjoint`",
            Self::RepeatStatic => "`repeat_static`",
            Self::Qif => "`qif`",
            Self::True => "`true`",
            Self::False => "`false`",
            Self::Natural(_) => "natural number (only in repeat_static)",
            Self::FatArrow => "`=>`",
            Self::Not => "`not`",
            Self::Xor => "`xor`",
            Self::And => "`and`",
            Self::Unit => "`Unit`",
            Self::Bit => "`Bit`",
            Self::CBit => "`CBit`",
            Self::Q => "`Q`",
            Self::Zero => "`0`",
            Self::One => "`1`",
            Self::LParen => "`(`",
            Self::RParen => "`)`",
            Self::LBrace => "`{`",
            Self::RBrace => "`}`",
            Self::LAngle => "`<`",
            Self::RAngle => "`>`",
            Self::Comma => "`,`",
            Self::Colon => "`:`",
            Self::DoubleColon => "`::`",
            Self::Semicolon => "`;`",
            Self::Equals => "`=`",
            Self::Arrow => "`->`",
            Self::LeftArrow => "`<-`",
            Self::Pipe => "`|`",
            Self::Eof => "end of file",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at byte {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for LexError {}

pub fn lex(source: &str) -> Result<Vec<Token>, LexError> {
    scan(source, false).map(|(tokens, _)| tokens)
}

pub(crate) fn lex_documented(source: &str) -> Result<(Vec<Token>, Vec<DocComment>), LexError> {
    scan(source, true)
}

fn scan(source: &str, retain_docs: bool) -> Result<(Vec<Token>, Vec<DocComment>), LexError> {
    let mut lexer = Lexer { source, pos: 0 };
    let mut tokens = Vec::new();
    let mut docs = Vec::new();
    while let Some(ch) = lexer.peek() {
        if matches!(ch, ' ' | '\t' | '\n' | '\r') {
            lexer.bump();
            continue;
        }
        if source[lexer.pos..].starts_with("//") || source[lexer.pos..].starts_with("/*") {
            if let Some(comment) = lexer.comment(retain_docs)? {
                docs.push(comment);
            }
            continue;
        }

        let start = lexer.pos;
        if let Some(message) = forbidden_character(ch) {
            return Err(LexError {
                message: message.to_owned(),
                span: Span::new(start, start + ch.len_utf8()),
            });
        }
        let kind = if ch.is_ascii_alphabetic() || ch == '_' {
            lexer.bump();
            while lexer
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                lexer.bump();
            }
            let name = &source[start..lexer.pos];
            keyword_kind(name).unwrap_or_else(|| TokenKind::Ident(name.to_owned()))
        } else if ch.is_ascii_digit() {
            lexer.bump();
            while lexer.peek().is_some_and(|c| c.is_ascii_digit()) {
                lexer.bump();
            }
            match &source[start..lexer.pos] {
                "0" => TokenKind::Zero,
                "1" => TokenKind::One,
                digits => TokenKind::Natural(digits.to_owned()),
            }
        } else {
            lexer.bump();
            match ch {
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                '{' => TokenKind::LBrace,
                '}' => TokenKind::RBrace,
                '>' => TokenKind::RAngle,
                ',' => TokenKind::Comma,
                ';' => TokenKind::Semicolon,
                '=' if lexer.peek() == Some('>') => {
                    lexer.bump();
                    TokenKind::FatArrow
                }
                '=' => TokenKind::Equals,
                '|' => TokenKind::Pipe,
                ':' if lexer.peek() == Some(':') => {
                    lexer.bump();
                    TokenKind::DoubleColon
                }
                ':' => TokenKind::Colon,
                '-' if lexer.peek() == Some('>') => {
                    lexer.bump();
                    TokenKind::Arrow
                }
                '<' if lexer.peek() == Some('-') => {
                    lexer.bump();
                    TokenKind::LeftArrow
                }
                '<' => TokenKind::LAngle,
                _ => {
                    return Err(LexError {
                        message: format!("unexpected character `{ch}`"),
                        span: Span::new(start, lexer.pos),
                    });
                }
            }
        };
        tokens.push(Token {
            kind,
            span: Span::new(start, lexer.pos),
        });
    }
    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span::new(source.len(), source.len()),
    });
    Ok((tokens, docs))
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
        Some("unsupported whitespace; use ASCII space, tab, LF, or CR")
    } else if ch.is_control() {
        Some("control character is forbidden")
    } else {
        None
    }
}

struct Lexer<'a> {
    source: &'a str,
    pos: usize,
}

impl Lexer<'_> {
    fn comment(&mut self, retain_docs: bool) -> Result<Option<DocComment>, LexError> {
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
                } else if self.source[self.pos..].starts_with("*/") {
                    depth -= 1;
                    self.pos += 2;
                } else if let Some(ch) = self.peek() {
                    self.comment_character(ch, style.is_some())?;
                    self.bump();
                } else {
                    return Err(LexError {
                        message: "unterminated block comment".into(),
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

    fn comment_character(&self, ch: char, doc: bool) -> Result<(), LexError> {
        let message = if doc && ch == '\r' && !self.source[self.pos..].starts_with("\r\n") {
            Some("bare carriage return is forbidden in documentation")
        } else if matches!(ch, ' ' | '\t' | '\n' | '\r') {
            None
        } else {
            forbidden_character(ch)
        };
        if let Some(message) = message {
            Err(LexError {
                message: message.into(),
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
