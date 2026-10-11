#![allow(dead_code)]
mod frontend {
pub mod ast {
#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct Span {pub start:usize,pub end:usize}
impl Span {pub fn new(start:usize,end:usize)->Self{Self{start,end}}}
}
pub mod documentation {
use super::ast::Span;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum DocStyle { Inner, Outer }
#[derive(Clone,Debug,PartialEq,Eq)] pub struct DocComment {pub style:DocStyle,pub text:String,pub span:Span}
}
pub mod scanner {

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
}
pub mod old {

use super::ast::Span;
use super::documentation::{DocComment, DocStyle};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Use,
    Meaning,
    Static,
    Op,
    Requires,
    ApplyAccess,
    AdjointAccess,
    ControlledAccess,
    PermutationBy,
    PhaseBy,
    BindOp,
    InverseOp,
    ThenOp,
    TensorOp,
    ControlledOp,
    RepeatOp,
    ConjugateOp,
    LBracket,
    RBracket,
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
        "meaning" => TokenKind::Meaning,
        "static" => TokenKind::Static,
        "Op" => TokenKind::Op,
        "requires" => TokenKind::Requires,
        "Apply" => TokenKind::ApplyAccess,
        "Adjoint" => TokenKind::AdjointAccess,
        "Controlled" => TokenKind::ControlledAccess,
        "permutation_by" => TokenKind::PermutationBy,
        "phase_by" => TokenKind::PhaseBy,
        "bind_op" => TokenKind::BindOp,
        "inverse_op" => TokenKind::InverseOp,
        "then_op" => TokenKind::ThenOp,
        "tensor_op" => TokenKind::TensorOp,
        "controlled_op" => TokenKind::ControlledOp,
        "repeat_op" => TokenKind::RepeatOp,
        "conjugate_op" => TokenKind::ConjugateOp,

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
            Self::Meaning => "`meaning`",
            Self::Static => "`static`",
            Self::Op => "`Op`",
            Self::Requires => "`requires`",
            Self::ApplyAccess => "`Apply`",
            Self::AdjointAccess => "`Adjoint`",
            Self::ControlledAccess => "`Controlled`",
            Self::PermutationBy => "`permutation_by`",
            Self::PhaseBy => "`phase_by`",
            Self::BindOp => "`bind_op`",
            Self::InverseOp => "`inverse_op`",
            Self::ThenOp => "`then_op`",
            Self::TensorOp => "`tensor_op`",
            Self::ControlledOp => "`controlled_op`",
            Self::RepeatOp => "`repeat_op`",
            Self::ConjugateOp => "`conjugate_op`",
            Self::LBracket => "`[`",
            Self::RBracket => "`]`",
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
        if ch == '\r' && !source[lexer.pos..].starts_with("\r\n") {
            return Err(LexError {
                message: "bare carriage return is forbidden; use LF or CRLF".into(),
                span: Span::new(lexer.pos, lexer.pos + 1),
            });
        }
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
                '[' => TokenKind::LBracket,
                ']' => TokenKind::RBracket,
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
        Some("unsupported whitespace; use ASCII space, tab, LF, or CRLF")
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

    fn comment_character(&self, ch: char, _doc: bool) -> Result<(), LexError> {
        let message = if ch == '\r' && !self.source[self.pos..].starts_with("\r\n") {
            Some("bare carriage return is forbidden; use LF or CRLF")
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
}
pub mod new {

use super::ast::Span;
use super::documentation::DocComment;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Use,
    Meaning,
    Static,
    Op,
    Requires,
    ApplyAccess,
    AdjointAccess,
    ControlledAccess,
    PermutationBy,
    PhaseBy,
    BindOp,
    InverseOp,
    ThenOp,
    TensorOp,
    ControlledOp,
    RepeatOp,
    ConjugateOp,
    LBracket,
    RBracket,
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
        "meaning" => TokenKind::Meaning,
        "static" => TokenKind::Static,
        "Op" => TokenKind::Op,
        "requires" => TokenKind::Requires,
        "Apply" => TokenKind::ApplyAccess,
        "Adjoint" => TokenKind::AdjointAccess,
        "Controlled" => TokenKind::ControlledAccess,
        "permutation_by" => TokenKind::PermutationBy,
        "phase_by" => TokenKind::PhaseBy,
        "bind_op" => TokenKind::BindOp,
        "inverse_op" => TokenKind::InverseOp,
        "then_op" => TokenKind::ThenOp,
        "tensor_op" => TokenKind::TensorOp,
        "controlled_op" => TokenKind::ControlledOp,
        "repeat_op" => TokenKind::RepeatOp,
        "conjugate_op" => TokenKind::ConjugateOp,

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
            Self::Meaning => "`meaning`",
            Self::Static => "`static`",
            Self::Op => "`Op`",
            Self::Requires => "`requires`",
            Self::ApplyAccess => "`Apply`",
            Self::AdjointAccess => "`Adjoint`",
            Self::ControlledAccess => "`Controlled`",
            Self::PermutationBy => "`permutation_by`",
            Self::PhaseBy => "`phase_by`",
            Self::BindOp => "`bind_op`",
            Self::InverseOp => "`inverse_op`",
            Self::ThenOp => "`then_op`",
            Self::TensorOp => "`tensor_op`",
            Self::ControlledOp => "`controlled_op`",
            Self::RepeatOp => "`repeat_op`",
            Self::ConjugateOp => "`conjugate_op`",
            Self::LBracket => "`[`",
            Self::RBracket => "`]`",
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
    use super::scanner::{ErrorKind, Kind, Scanner};
    let mut scanner = Scanner::new(source, None, retain_docs);
    let mut tokens = Vec::new();
    loop {
        let mut token = scanner.next().map_err(|error| LexError {
            message: match error.kind {
                ErrorKind::Forbidden(message) => message.into(),
                ErrorKind::Unexpected(ch) => format!("unexpected character `{ch}`"),
                ErrorKind::UnterminatedComment => "unterminated block comment".into(),
                ErrorKind::CommentDepth(limit) => format!("comment nesting exceeds {limit}"),
            },
            span: error.span,
        })?;
        let text = &source[token.span.start..token.span.end];
        let kind = match token.kind {
            Kind::Word => keyword_kind(text).unwrap_or_else(|| TokenKind::Ident(text.into())),
            Kind::Numeral => match text {
                "0" => TokenKind::Zero,
                "1" => TokenKind::One,
                digits => TokenKind::Natural(digits.into()),
            },
            Kind::Eof => TokenKind::Eof,
            Kind::Punctuation(ch) => match ch {
                '(' => TokenKind::LParen,
                '[' => TokenKind::LBracket,
                ']' => TokenKind::RBracket,
                ')' => TokenKind::RParen,
                '{' => TokenKind::LBrace,
                '}' => TokenKind::RBrace,
                '>' => TokenKind::RAngle,
                ',' => TokenKind::Comma,
                ';' => TokenKind::Semicolon,
                '=' if scanner.join(&mut token, '>') => TokenKind::FatArrow,
                '=' => TokenKind::Equals,
                '|' => TokenKind::Pipe,
                ':' if scanner.join(&mut token, ':') => TokenKind::DoubleColon,
                ':' => TokenKind::Colon,
                '-' if scanner.join(&mut token, '>') => TokenKind::Arrow,
                '<' if scanner.join(&mut token, '-') => TokenKind::LeftArrow,
                '<' => TokenKind::LAngle,
                _ => {
                    return Err(LexError {
                        message: format!("unexpected character `{ch}`"),
                        span: token.span,
                    });
                }
            },
        };
        let eof = kind == TokenKind::Eof;
        tokens.push(Token {
            kind,
            span: token.span,
        });
        if eof {
            return Ok((tokens, scanner.into_docs()));
        }
    }
}
}
pub mod sized_old {
use super::ast::Span;
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Token {text:String,span:Span}
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Error {code:&'static str,span:Span,message:String}
impl Error {fn new(code:&'static str,span:Span,message:impl Into<String>)->Self {Self{code,span,message:message.into()}}}
type Result<T>=std::result::Result<T,Error>;
fn error(span:Span,message:impl Into<String>)->Error {Error::new("parse",span,message)}

pub fn tokens(source: &str) -> Result<Vec<Token>> {
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut result = Vec::new();
    while i < bytes.len() {
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if bytes[i..].starts_with(b"/*") {
            let start = i;
            i += 2;
            let mut depth = 1;
            while i < bytes.len() && depth > 0 {
                if bytes[i..].starts_with(b"/*") {
                    depth += 1;
                    i += 2;
                } else if bytes[i..].starts_with(b"*/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
                if depth > 64 {
                    return Err(error(Span::new(start, i), "comment nesting exceeds 64"));
                }
            }
            if depth != 0 {
                return Err(error(Span::new(start, i), "unterminated comment"));
            }
            continue;
        }
        let start = i;
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
        } else if bytes[i].is_ascii_digit() {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i - start > 1 && bytes[start] == b'0' {
                return Err(error(
                    Span::new(start, i),
                    "natural literal has a leading zero",
                ));
            }
        } else if [b"::", b"->", b"..", b"==", b"!=", b"<=", b">="]
            .iter()
            .any(|symbol| bytes[i..].starts_with(*symbol))
        {
            i += 2;
        } else if b"[]{}(),;:<>+-*=^".contains(&bytes[i]) {
            i += 1;
        } else {
            return Err(error(
                Span::new(i, i + source[i..].chars().next().unwrap().len_utf8()),
                "unsupported sized-source character",
            ));
        }
        result.push(Token {
            text: source[start..i].into(),
            span: Span::new(start, i),
        });
        if result.len() > 10_000 {
            return Err(Error::new(
                "limit",
                Span::new(start, i),
                "source exceeds 10000 tokens",
            ));
        }
    }
    result.push(Token {
        text: String::new(),
        span: Span::new(i, i),
    });
    Ok(result)
}

}
pub mod sized_new {
use super::ast::Span;
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Token {text:String,span:Span}
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Error {code:&'static str,span:Span,message:String}
impl Error {fn new(code:&'static str,span:Span,message:impl Into<String>)->Self {Self{code,span,message:message.into()}}}
type Result<T>=std::result::Result<T,Error>;
fn error(span:Span,message:impl Into<String>)->Error {Error::new("parse",span,message)}

pub fn tokens(source: &str) -> Result<Vec<Token>> {
    tokens_with_limits(source, 10_000, 64)
}

fn tokens_with_limits(
    source: &str,
    max_tokens: usize,
    max_comment_depth: usize,
) -> Result<Vec<Token>> {
    use crate::frontend::scanner::{ErrorKind, Kind, Scanner};
    let mut scanner = Scanner::new(source, Some(max_comment_depth), false);
    let mut result = Vec::new();
    loop {
        let mut token = scanner.next().map_err(|e| {
            error(
                e.span,
                match e.kind {
                    ErrorKind::Forbidden(message) => message.to_owned(),
                    ErrorKind::Unexpected(_) => "unsupported sized-source character".into(),
                    ErrorKind::UnterminatedComment => "unterminated comment".into(),
                    ErrorKind::CommentDepth(limit) => format!("comment nesting exceeds {limit}"),
                },
            )
        })?;
        match token.kind {
            Kind::Word | Kind::Eof => {}
            Kind::Numeral => {
                if token.span.end - token.span.start > 1
                    && source.as_bytes()[token.span.start] == b'0'
                {
                    return Err(error(token.span, "natural literal has a leading zero"));
                }
            }
            Kind::Punctuation(ch) => {
                let suffix = match ch {
                    ':' => Some(':'),
                    '-' => Some('>'),
                    '.' => Some('.'),
                    '=' | '!' | '<' | '>' => Some('='),
                    _ => None,
                };
                let joined = suffix.is_some_and(|next| scanner.join(&mut token, next));
                if !joined && !"[]{}(),;:<>+-*=^".contains(ch) {
                    return Err(error(token.span, "unsupported sized-source character"));
                }
            }
        }
        let eof = token.kind == Kind::Eof;
        // Count projected tokens, not physical punctuation atoms; EOF and
        // comments do not consume the historical 10,000-token allowance.
        if !eof && result.len() >= max_tokens {
            return Err(Error::new(
                "limit",
                token.span,
                format!("source exceeds {max_tokens} tokens"),
            ));
        }
        result.push(Token {
            text: source[token.span.start..token.span.end].into(),
            span: token.span,
        });
        if eof {
            return Ok(result);
        }
    }
}

}
}

fn check(s:&str,check_sized:bool){
 let a=format!("{:?}",frontend::old::lex_documented(s));
 let b=format!("{:?}",frontend::new::lex_documented(s));
 assert_eq!(a,b,"finite source {s:?}");
 if check_sized {
 let a=format!("{:?}",frontend::sized_old::tokens(s));
 let b=format!("{:?}",frontend::sized_new::tokens(s));
 assert_eq!(a,b,"sized source {s:?}");
 }
}
fn main(){
 let alphabet=["a","_","0","1",":","-",">","<","=",".","!","/","*","|"," ","\n"];
 let mut checked=0usize;
 for a in alphabet {for b in alphabet {for c in alphabet {for d in alphabet {
  check(&format!("{a}{b}{c}{d}"),true);checked+=1;
 }}}}
 let fragments=["pub","fn","Q","Bit","Bits","000","01","2","_a","::","->","==>","<->","!=","..","[]","{}",",",";",":","^","+","*","|"," ","\t","\r\n","// λ\r\n","/*日本語*/","/**x*/","/*!x*/","///x\n","//!x\n","/**/","/***/","/* /*λ*/ */","/*","*/","λ","\u{200b}","\u{feff}"];
 let mut seed=0x0123456789abcdefu64;
 for _ in 0..100_000 {
   let mut s=String::new();
   for _ in 0..12 {seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;s.push_str(fragments[seed as usize%fragments.len()]);}
   check(&s,true); checked+=1;
 }
 for bad in ['\r','\u{b}','\u{c}','\0','\u{202e}','\u{2028}','\u{0085}','\u{00a0}'] {
  for (a,b) in [("",""),("//","\n"),("/*","*/"),("/*!","*/"),("/** ","*/")] {
    check(&format!("//日本語\r\n{a}{bad}x{b} fn"),false);checked+=1;
  }
 }
 println!("PASS: {checked} finite old/new comparisons; 165536 sized old/new comparisons on inputs without the intentionally tightened character policy");
}
