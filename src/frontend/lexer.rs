//! ASCII-keyword lexer with UTF-8 byte positions.

use super::ast::Span;

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
    let mut lexer = Lexer { source, pos: 0 };
    let mut tokens = Vec::new();
    while let Some(ch) = lexer.peek() {
        if ch.is_whitespace() {
            lexer.bump();
            continue;
        }
        if source[lexer.pos..].starts_with("//") {
            while let Some(c) = lexer.peek() {
                if c == '\n' || c == '\r' {
                    break;
                }
                lexer.bump();
            }
            continue;
        }

        let start = lexer.pos;
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
        } else {
            lexer.bump();
            match ch {
                '0' => TokenKind::Zero,
                '1' => TokenKind::One,
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                '{' => TokenKind::LBrace,
                '}' => TokenKind::RBrace,
                '>' => TokenKind::RAngle,
                ',' => TokenKind::Comma,
                ';' => TokenKind::Semicolon,
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
    Ok(tokens)
}

struct Lexer<'a> {
    source: &'a str,
    pos: usize,
}

impl Lexer<'_> {
    fn peek(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    fn bump(&mut self) {
        if let Some(ch) = self.peek() {
            self.pos += ch.len_utf8();
        }
    }
}
