//! ASCII-keyword lexer with UTF-8 byte positions.

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
    Classical,
    Basis,
    Isometry,
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
    Qfor,
    True,
    False,
    Natural(String),
    FatArrow,
    Plus,
    Minus,
    Star,
    Caret,
    DotDot,
    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,
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
        "checked_op" | "bind_op" => TokenKind::BindOp,
        "inverse_op" => TokenKind::InverseOp,
        "then_op" => TokenKind::ThenOp,
        "tensor_op" => TokenKind::TensorOp,
        "controlled_op" => TokenKind::ControlledOp,
        "repeat_op" => TokenKind::RepeatOp,
        "conjugate_op" => TokenKind::ConjugateOp,

        "pub" => TokenKind::Pub,
        "classical" => TokenKind::Classical,
        "basis" => TokenKind::Basis,
        // Keep the old word reserved for the located migration error below.
        // The canonical token does not rename versioned IR effect tags.
        "isometry" | "iso" => TokenKind::Isometry,
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
        "qfor" => TokenKind::Qfor,
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
            Self::BindOp => "`checked_op`",
            Self::InverseOp => "`inverse_op`",
            Self::ThenOp => "`then_op`",
            Self::TensorOp => "`tensor_op`",
            Self::ControlledOp => "`controlled_op`",
            Self::RepeatOp => "`repeat_op`",
            Self::ConjugateOp => "`conjugate_op`",
            Self::LBracket => "`[`",
            Self::RBracket => "`]`",
            Self::Pub => "`pub`",
            Self::Classical => "`classical`",
            Self::Basis => "`basis`",
            Self::Isometry => "`isometry`",
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
            Self::Qfor => "`qfor`",
            Self::True => "`true`",
            Self::False => "`false`",
            Self::Natural(_) => "natural number",
            Self::Plus => "`+`",
            Self::Minus => "`-`",
            Self::Star => "`*`",
            Self::Caret => "`^`",
            Self::DotDot => "`..`",
            Self::EqualEqual => "`==`",
            Self::NotEqual => "`!=`",
            Self::LessEqual => "`<=`",
            Self::GreaterEqual => "`>=`",
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
    scan(source, false, None, None).map(|(tokens, _)| tokens)
}

pub(crate) fn lex_documented(source: &str) -> Result<(Vec<Token>, Vec<DocComment>), LexError> {
    scan(source, true, None, None)
}

pub(crate) fn lex_documented_bounded(
    source: &str,
    max_tokens: usize,
    max_comment_depth: usize,
) -> Result<(Vec<Token>, Vec<DocComment>), LexError> {
    scan(source, true, Some(max_tokens), Some(max_comment_depth))
}

fn scan(
    source: &str,
    retain_docs: bool,
    max_tokens: Option<usize>,
    max_comment_depth: Option<usize>,
) -> Result<(Vec<Token>, Vec<DocComment>), LexError> {
    use super::scanner::{ErrorKind, Kind, Scanner};
    let mut scanner = Scanner::new(source, max_comment_depth, retain_docs);
    let mut tokens: Vec<Token> = Vec::new();
    loop {
        let mut token = scanner.next().map_err(|error| LexError {
            message: match error.kind {
                ErrorKind::Forbidden(message) => message.into(),
                ErrorKind::Unexpected('?') => "`?` residual propagation is unsupported in the verified quantum core; use a final expression and explicit branches that preserve every quantum owner".into(),
                ErrorKind::Unexpected('&') => format!(
                    "unexpected character `&`; {}",
                    super::diagnostic::UNSUPPORTED_REFERENCE_EXPLANATION
                ),
                ErrorKind::Unexpected(ch) => format!("unexpected character `{ch}`"),
                ErrorKind::UnterminatedComment => "unterminated block comment".into(),
                ErrorKind::CommentDepth(limit) => format!("comment nesting exceeds {limit}"),
            },
            span: error.span,
        })?;
        let text = &source[token.span.start..token.span.end];
        let mut kind = match token.kind {
            Kind::Word => keyword_kind(text).unwrap_or_else(|| TokenKind::Ident(String::new())),
            Kind::Numeral => match text {
                "0" => TokenKind::Zero,
                "1" => TokenKind::One,
                _ => TokenKind::Natural(String::new()),
            },
            Kind::Eof => TokenKind::Eof,
            Kind::Punctuation(ch) => match ch {
                '(' => TokenKind::LParen,
                '[' => TokenKind::LBracket,
                ']' => TokenKind::RBracket,
                ')' => TokenKind::RParen,
                '{' => TokenKind::LBrace,
                '}' => TokenKind::RBrace,
                '>' if scanner.join(&mut token, '=') => TokenKind::GreaterEqual,
                '>' => TokenKind::RAngle,
                ',' => TokenKind::Comma,
                ';' => TokenKind::Semicolon,
                '=' if scanner.join(&mut token, '>') => TokenKind::FatArrow,
                '=' if scanner.join(&mut token, '=') => TokenKind::EqualEqual,
                '=' => TokenKind::Equals,
                '!' if scanner.join(&mut token, '=') => TokenKind::NotEqual,
                '.' if scanner.join(&mut token, '.') => TokenKind::DotDot,
                '+' => TokenKind::Plus,
                '*' => TokenKind::Star,
                '^' => TokenKind::Caret,
                '|' => TokenKind::Pipe,
                ':' if scanner.join(&mut token, ':') => TokenKind::DoubleColon,
                ':' => TokenKind::Colon,
                '-' if scanner.join(&mut token, '>') => TokenKind::Arrow,
                '-' => TokenKind::Minus,
                '<' if scanner.join(&mut token, '=') => TokenKind::LessEqual,
                '<' if scanner.join(&mut token, '-') => TokenKind::LeftArrow,
                '<' => TokenKind::LAngle,
                _ => {
                    let message = if ch == '.' {
                        "unexpected character `.`; field and method receiver syntax is unsupported; use an ordinary function call. For quantum access, write explicit `excl ...` or `ctrl ...` arguments: receiver adjustment cannot infer or forward quantum access".into()
                    } else if ch == '!' {
                        match tokens.last().map(|token| &token.kind) {
                            Some(TokenKind::Ident(name))
                                if matches!(
                                    name.as_str(),
                                    "panic"
                                        | "assert"
                                        | "assert_eq"
                                        | "assert_ne"
                                        | "debug_assert"
                                        | "debug_assert_eq"
                                        | "debug_assert_ne"
                                        | "unreachable"
                                        | "todo"
                                        | "unimplemented"
                                ) =>
                            {
                                format!(
                                    "`{name}!` runtime exits are unsupported in the verified quantum core; use a final expression and explicit branches that preserve every quantum owner"
                                )
                            }
                            _ => format!("unexpected character `{ch}`"),
                        }
                    } else {
                        format!("unexpected character `{ch}`")
                    };
                    return Err(LexError {
                        message,
                        span: token.span,
                    });
                }
            },
        };
        // Charge before allocating an owned word/numeral token. Trivia and EOF
        // do not consume the entry point's token allowance.
        if token.kind != Kind::Eof && max_tokens.is_some_and(|limit| tokens.len() >= limit) {
            return Err(LexError {
                message: format!("source exceeds {} tokens", max_tokens.unwrap()),
                span: token.span,
            });
        }
        // Reserve the retired spelling for a located migration error only.
        // Capacity rejection retains precedence over spelling diagnostics.
        if token.kind == Kind::Word && text == "bind_op" {
            return Err(LexError {
                message: "`bind_op` was renamed to `checked_op` in Qleisli 0.3.0; use `checked_op(implementation, Meaning)` to request exact meaning checking.".into(),
                span: token.span,
            });
        }
        if token.kind == Kind::Word && text == "iso" {
            return Err(LexError {
                message: "`iso` was renamed to `isometry` in Qleisli 0.3.0; use `isometry fn` for an isometry effect assertion.".into(),
                span: token.span,
            });
        }
        if let TokenKind::Ident(value) | TokenKind::Natural(value) = &mut kind {
            *value = text.to_owned();
        }
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

#[cfg(test)]
mod common_token_tests {
    use super::*;

    #[test]
    fn capacity_precedes_retired_word_diagnostics_with_a_small_allowance() {
        for (old, new) in [("bind_op", "checked_op"), ("iso", "isometry")] {
            let source = format!("/* λ */ x {old}");
            let start = source.find(old).unwrap();
            let span = Span::new(start, start + old.len());
            let capacity = lex_documented_bounded(&source, 1, 2).unwrap_err();
            assert_eq!(capacity.span, span);
            assert_eq!(capacity.message, "source exceeds 1 tokens");
            let retirement = lex_documented_bounded(&source, 2, 2).unwrap_err();
            assert_eq!(retirement.span, span);
            assert!(
                retirement
                    .message
                    .contains(&format!("was renamed to `{new}`"))
            );
        }
    }

    #[test]
    fn bounded_common_tokens_count_pairs_before_owning_spellings() {
        let source = "/* λ */ <= == identifier // tail\r\n";
        let (tokens, _) = lex_documented_bounded(source, 3, 2).unwrap();
        assert_eq!(tokens.len(), 4);
        assert_eq!(
            tokens.last().unwrap().span,
            Span::new(source.len(), source.len())
        );
        let error = lex_documented_bounded(source, 2, 2).unwrap_err();
        assert_eq!(&source[error.span.start..error.span.end], "identifier");
        let error = lex_documented_bounded("x <=", 1, 2).unwrap_err();
        assert_eq!(error.span, Span::new(2, 4));
        assert_eq!(error.message, "source exceeds 1 tokens");
        assert_eq!(
            lex_documented_bounded("/* only */", 0, 2).unwrap().0.len(),
            1
        );
    }

    #[test]
    fn comment_bound_and_doc_recognition_are_independent_of_tokens() {
        let source = "/** /* λ */ */ x";
        let (tokens, docs) = lex_documented_bounded(source, 1, 2).unwrap();
        assert_eq!(tokens.len(), 2);
        assert_eq!(docs.len(), 1);
        let error = lex_documented_bounded(source, 1, 1).unwrap_err();
        assert_eq!(error.span, Span::new(0, 6));
        assert_eq!(error.message, "comment nesting exceeds 1");
    }
}
