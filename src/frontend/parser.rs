//! One source parser for the provisional finite and sized constructs.
//!
//! Parsing does not resolve names or establish typing, effects, linear use, or
//! quantum validity. Those checks must happen before producing trusted IR.

use std::fmt;
use std::mem::discriminant;

use super::ast::*;
use super::documentation::{DocumentedModule, attach};
use super::lexer::{LexError, Token, TokenKind, lex_documented};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at byte {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

impl From<LexError> for ParseError {
    fn from(value: LexError) -> Self {
        Self {
            message: value.message,
            span: value.span,
        }
    }
}

pub fn parse_module(source: &str) -> Result<Module, ParseError> {
    parse_documented_module(source).map(|documented| documented.syntax)
}

/// Parse the same source grammar, retaining descriptive comments separately
/// from the existing AST. Documentation never establishes quantum validity.
pub fn parse_documented_module(source: &str) -> Result<DocumentedModule, ParseError> {
    parse_documented(source, None)
}

pub(crate) fn parse_bounded_module(source: &str) -> Result<Module, ParseError> {
    parse_documented(source, Some((10_000, 64))).map(|documented| documented.syntax)
}

/// Parse a complete host-supplied ordinary type description with the source
/// grammar and the same token/depth limits. Trailing syntax is never ignored.
pub(crate) fn parse_closed_basis(source: &str) -> Result<Type, ParseError> {
    if source.len() > 65_536 {
        return Err(ParseError {
            message: "source exceeds 64 KiB limit".into(),
            span: Span::new(0, source.len()),
        });
    }
    let (tokens, _) = super::lexer::lex_documented_bounded(source, 10_000, 64)?;
    let mut parser = Parser {
        tokens,
        pos: 0,
        nesting: 0,
        remaining_import_prefix_identifiers: MAX_IMPORT_PREFIX_IDENTIFIERS,
        remaining_import_prefix_bytes: MAX_IMPORT_PREFIX_BYTES,
    };
    let ty = parser.basis_type()?;
    parser.expect(&TokenKind::Eof)?;
    Ok(ty)
}

fn parse_documented(
    source: &str,
    limits: Option<(usize, usize)>,
) -> Result<DocumentedModule, ParseError> {
    let (tokens, comments) = if let Some((tokens, comments)) = limits {
        super::lexer::lex_documented_bounded(source, tokens, comments)?
    } else {
        lex_documented(source)?
    };
    let mut parser = Parser {
        tokens,
        pos: 0,
        nesting: 0,
        remaining_import_prefix_identifiers: MAX_IMPORT_PREFIX_IDENTIFIERS,
        remaining_import_prefix_bytes: MAX_IMPORT_PREFIX_BYTES,
    };
    let syntax = parser.module(source.len())?;
    attach(syntax, &parser.tokens, comments)
}

/// An implementation limit on recursive syntax and left-associated expression ASTs.
const MAX_NESTING: usize = 64;
const MAX_TUPLE_FIELDS: usize = 64;
// Only group-induced prefix copies spend these module-wide budgets. Original
// path tokens remain linear in the input, including long ungrouped imports.
const MAX_IMPORT_PREFIX_IDENTIFIERS: usize = 65_536;
const MAX_IMPORT_PREFIX_BYTES: usize = 1_048_576;

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    nesting: usize,
    remaining_import_prefix_identifiers: usize,
    remaining_import_prefix_bytes: usize,
}

impl Parser {
    fn nested<T>(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        if self.nesting >= MAX_NESTING {
            return Err(self.error("syntax nesting exceeds the initial 64-level limit"));
        }
        self.nesting += 1;
        let result = parse(self);
        self.nesting -= 1;
        result
    }

    fn module(&mut self, source_len: usize) -> Result<Module, ParseError> {
        let mut uses = Vec::new();
        let mut decls = Vec::new();
        while !self.at(&TokenKind::Eof) {
            if self.at(&TokenKind::Use) {
                uses.extend(self.use_decl()?);
            } else if self.at(&TokenKind::Pub)
                || self.at(&TokenKind::Basis)
                || self.at(&TokenKind::Iso)
                || self.at(&TokenKind::Unitary)
                || self.at(&TokenKind::Observe)
                || self.at(&TokenKind::Fn)
                || self.at(&TokenKind::Meaning)
            {
                decls.push(self.decl()?);
            } else {
                return Err(self.error("expected `use` or a function declaration"));
            }
        }
        Ok(Module {
            uses,
            decls,
            span: Span::new(0, source_len),
        })
    }

    fn use_decl(&mut self) -> Result<Vec<UseDecl>, ParseError> {
        let start = self.expect(&TokenKind::Use)?.span.start;
        let paths = self.use_tree(&[])?;
        let end = self.expect(&TokenKind::Semicolon)?.span.end;
        Ok(paths
            .into_iter()
            .map(|path| UseDecl {
                path,
                span: Span::new(start, end),
            })
            .collect())
    }

    // Grouping expands to the existing leaf AST, without changing resolution.
    fn use_tree(&mut self, prefix: &[Ident]) -> Result<Vec<Vec<Ident>>, ParseError> {
        if self.at(&TokenKind::LBrace) {
            return self.nested(|parser| {
                parser.bump();
                if parser.at(&TokenKind::RBrace) {
                    return Err(parser.error("import groups must contain at least one name"));
                }
                let mut paths = Vec::new();
                loop {
                    paths.extend(parser.use_tree(prefix)?);
                    if parser.consume(&TokenKind::Comma).is_none() || parser.at(&TokenKind::RBrace)
                    {
                        break;
                    }
                }
                parser.expect(&TokenKind::RBrace)?;
                Ok(paths)
            });
        }
        let mut path = self.clone_import_prefix(prefix)?;
        loop {
            // Declaration keywords are admitted only in the std module position.
            let name = if path.len() == 1
                && path[0].text == "std"
                && matches!(self.current().kind, TokenKind::Basis | TokenKind::Observe)
            {
                let token = self.bump();
                Ident {
                    text: if token.kind == TokenKind::Basis {
                        "basis"
                    } else {
                        "observe"
                    }
                    .into(),
                    span: token.span,
                }
            } else {
                self.ident()?
            };
            path.push(name);
            if self.consume(&TokenKind::DoubleColon).is_none() {
                return if path.len() < 2 {
                    Err(self.error("imports require a module path and a name"))
                } else {
                    Ok(vec![path])
                };
            }
            if self.at(&TokenKind::LBrace) {
                return self.use_tree(&path);
            }
        }
    }

    fn clone_import_prefix(&mut self, prefix: &[Ident]) -> Result<Vec<Ident>, ParseError> {
        let identifiers = self
            .remaining_import_prefix_identifiers
            .checked_sub(prefix.len())
            .ok_or_else(|| {
                self.error("grouped import expansion exceeds the 65536 copied identifiers limit")
            })?;
        let bytes = prefix
            .iter()
            .try_fold(self.remaining_import_prefix_bytes, |remaining, name| {
                remaining.checked_sub(name.text.len())
            })
            .ok_or_else(|| {
                self.error("grouped import expansion exceeds the 1048576 copied name bytes limit")
            })?;
        self.remaining_import_prefix_identifiers = identifiers;
        self.remaining_import_prefix_bytes = bytes;
        Ok(prefix.to_vec())
    }

    fn decl(&mut self) -> Result<Decl, ParseError> {
        let pub_token = self.consume(&TokenKind::Pub);
        let public = pub_token.is_some();
        let start = pub_token.map_or_else(|| self.current().span.start, |token| token.span.start);
        if self.consume(&TokenKind::Meaning).is_some() {
            let name = self.ident()?;
            self.expect(&TokenKind::Colon)?;
            let return_type = self.basis_type()?;
            self.expect(&TokenKind::Equals)?;
            let permutation = if self.consume(&TokenKind::PermutationBy).is_some() {
                true
            } else {
                self.expect(&TokenKind::PhaseBy)?;
                false
            };
            self.expect(&TokenKind::LParen)?;
            let function = self.ident()?;
            self.expect(&TokenKind::RParen)?;
            let end = self.expect(&TokenKind::Semicolon)?.span.end;
            return Ok(Decl {
                public,
                kind: FnKind::Meaning,
                name,
                static_params: vec![],
                requires: vec![],
                params: vec![],
                return_type,
                body: FnBody::Meaning {
                    permutation,
                    function,
                },
                span: Span::new(start, end),
            });
        }
        let kind = if self.consume(&TokenKind::Basis).is_some() {
            FnKind::Basis
        } else if self.consume(&TokenKind::Iso).is_some() {
            FnKind::Iso
        } else if self.consume(&TokenKind::Unitary).is_some() {
            FnKind::Unitary
        } else if self.consume(&TokenKind::Observe).is_some() {
            FnKind::Observe
        } else if self.at(&TokenKind::Fn) {
            FnKind::Inferred
        } else {
            return Err(self.error(
                "expected `fn`, `basis`, `iso`, `unitary`, `observe`, or `meaning` after `pub`",
            ));
        };
        self.expect(&TokenKind::Fn)?;
        let name = self.ident()?;
        let mut static_params = Vec::new();
        if self.consume(&TokenKind::LBracket).is_some() {
            if kind == FnKind::Basis {
                return Err(self.error("basis functions cannot have static operation parameters"));
            }
            loop {
                self.expect(&TokenKind::Static)?;
                // The sized profile historically permits type words as Nat
                // names. Keep this contextual: operation/runtime identifiers
                // still use the ordinary reserved-word rules.
                let natural = self.tokens.get(self.pos + 2).is_some_and(
                    |token| matches!(&token.kind, TokenKind::Ident(name) if name == "Nat"),
                );
                let name = if natural {
                    self.natural_ident()?
                } else {
                    self.ident()?
                };
                self.expect(&TokenKind::Colon)?;
                let kind = if self.word("Nat") {
                    self.bump();
                    StaticParamKind::Natural
                } else if self.word("Basis") {
                    self.bump();
                    StaticParamKind::Basis
                } else {
                    self.expect(&TokenKind::Op)?;
                    self.expect(&TokenKind::LAngle)?;
                    let basis = self.basis_type()?;
                    let meaning = if self.consume(&TokenKind::Comma).is_some() {
                        Some(self.ident()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::RAngle)?;
                    StaticParamKind::Operation { basis, meaning }
                };
                static_params.push(StaticParam { name, kind });
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(&TokenKind::RBracket)?;
        }
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        if !self.at(&TokenKind::RParen) {
            loop {
                let pattern = self.pattern()?;
                self.expect(&TokenKind::Colon)?;
                let ty = if kind == FnKind::Basis {
                    self.basis_type()?
                } else {
                    self.ty()?
                };
                let span = Span::new(pattern.span.start, ty.span.end);
                params.push(Param { pattern, ty, span });
                if self.consume(&TokenKind::Comma).is_none() || self.at(&TokenKind::RParen) {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let return_type = if kind == FnKind::Basis {
            self.basis_type()?
        } else {
            self.ty()?
        };
        let mut requires = Vec::new();
        if let Some(requires_token) = self.consume(&TokenKind::Requires) {
            if kind == FnKind::Basis {
                return Err(ParseError {
                    message: "basis functions cannot have requires clauses".into(),
                    span: requires_token.span,
                });
            }
            loop {
                if matches!(
                    self.current().kind,
                    TokenKind::ApplyAccess | TokenKind::AdjointAccess | TokenKind::ControlledAccess
                ) {
                    let access_span = self.current().span;
                    let access = match self.bump().kind {
                        TokenKind::ApplyAccess => Access::Apply,
                        TokenKind::AdjointAccess => Access::Adjoint,
                        _ => Access::Controlled,
                    };
                    self.expect(&TokenKind::LParen)?;
                    let name = self.ident()?;
                    self.expect(&TokenKind::RParen)?;
                    requires.push(Requirement::Access(AccessConstraint {
                        access,
                        name,
                        span: access_span,
                    }));
                } else {
                    requires.push(Requirement::Predicate(self.predicate()?));
                }
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        let (body, end) = if kind == FnKind::Basis {
            let (basis, block_span) = self.basis_block()?;
            (FnBody::Basis(basis), block_span.end)
        } else {
            let block = self.block()?;
            let end = block.span.end;
            (FnBody::Quantum(block), end)
        };
        Ok(Decl {
            public,
            kind,
            name,
            static_params,
            requires,
            params,
            return_type,
            body,
            span: Span::new(start, end),
        })
    }

    fn ty(&mut self) -> Result<Type, ParseError> {
        let ty = self.nested(Self::ty_inner)?;
        Self::type_depth(&ty)?;
        Ok(ty)
    }

    fn static_op(&mut self) -> Result<StaticOp, ParseError> {
        self.nested(Self::static_op_inner)
    }

    fn static_op_inner(&mut self) -> Result<StaticOp, ParseError> {
        let start = self.current().span;
        // Type descriptions are contextual static arguments. An ordinary call
        // named `type` remains an ordinary call; no expression becomes a type.
        if self.word("type")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::LParen)
        {
            self.bump();
            self.expect(&TokenKind::LParen)?;
            let ty = self.basis_type()?;
            let end = self.expect(&TokenKind::RParen)?.span;
            return Ok(StaticOp {
                kind: StaticOpKind::Type(ty),
                span: start.cover(end),
            });
        }
        if Self::natural_name(&self.current().kind).is_some()
            || matches!(
                self.current().kind,
                TokenKind::Zero | TokenKind::One | TokenKind::Natural(_) | TokenKind::LParen
            )
        {
            let natural = self.natural()?;
            let kind = if self.consume(&TokenKind::LBracket).is_some() {
                let NatKind::Name(text) = natural.kind else {
                    return Err(self.error("only a function can have static arguments"));
                };
                let name = Ident {
                    text,
                    span: natural.span,
                };
                StaticOpKind::Specialize {
                    name,
                    arguments: self.static_arguments()?,
                }
            } else if let NatKind::Name(text) = natural.kind {
                StaticOpKind::Name(Ident {
                    text,
                    span: natural.span,
                })
            } else {
                StaticOpKind::Natural(natural)
            };
            return Ok(StaticOp {
                span: start.cover(self.tokens[self.pos - 1].span),
                kind,
            });
        }
        if !matches!(
            self.current().kind,
            TokenKind::BindOp
                | TokenKind::RepeatOp
                | TokenKind::InverseOp
                | TokenKind::ControlledOp
                | TokenKind::ThenOp
                | TokenKind::TensorOp
                | TokenKind::ConjugateOp
        ) {
            return Err(self.error("expected a static operation description"));
        }
        let constructor = self.bump();
        self.expect(&TokenKind::LParen)?;
        let kind = match constructor.kind {
            TokenKind::BindOp => {
                let implementation = self.ident()?;
                self.expect(&TokenKind::Comma)?;
                StaticOpKind::Bind {
                    implementation,
                    meaning: self.ident()?,
                }
            }
            TokenKind::RepeatOp => {
                let natural = self.natural()?;
                let count = if self.consume(&TokenKind::Caret).is_some() {
                    if !matches!(natural.kind, NatKind::Number(2)) {
                        return Err(ParseError {
                            message: "only 2^e repetition counts are supported".into(),
                            span: natural.span,
                        });
                    }
                    Count::Power(self.natural_atom()?)
                } else {
                    Count::Natural(natural)
                };
                self.expect(&TokenKind::Comma)?;
                StaticOpKind::Repeat(count, Box::new(self.static_op()?))
            }
            TokenKind::InverseOp => StaticOpKind::Inverse(Box::new(self.static_op()?)),
            TokenKind::ControlledOp => StaticOpKind::Controlled(Box::new(self.static_op()?)),
            TokenKind::ThenOp | TokenKind::TensorOp | TokenKind::ConjugateOp => {
                let a = Box::new(self.static_op()?);
                self.expect(&TokenKind::Comma)?;
                let b = Box::new(self.static_op()?);
                match constructor.kind {
                    TokenKind::ThenOp => StaticOpKind::Then(a, b),
                    TokenKind::TensorOp => StaticOpKind::Tensor(a, b),
                    _ => StaticOpKind::Conjugate(a, b),
                }
            }
            _ => return Err(self.error("expected a static operation description")),
        };
        let end = self.expect(&TokenKind::RParen)?.span;
        Ok(StaticOp {
            kind,
            span: start.cover(end),
        })
    }

    fn word(&self, word: &str) -> bool {
        matches!(&self.current().kind, TokenKind::Ident(name) if name == word)
    }

    fn expect_word(&mut self, word: &str) -> Result<Ident, ParseError> {
        if self.word(word) {
            self.ident()
        } else {
            Err(self.error(&format!("expected `{word}`")))
        }
    }

    fn static_arguments(&mut self) -> Result<Vec<StaticOp>, ParseError> {
        let mut arguments = Vec::new();
        if self.at(&TokenKind::RBracket) {
            self.bump();
            return Ok(arguments);
        }
        loop {
            arguments.push(self.static_op()?);
            if self.consume(&TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(arguments)
    }

    fn natural_node(kind: NatKind, span: Span) -> Result<Natural, ParseError> {
        let depth = match &kind {
            NatKind::Number(_) | NatKind::Name(_) => 1,
            NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => {
                1 + a.depth.max(b.depth)
            }
        };
        if depth > 128 {
            return Err(ParseError {
                message: "natural expression depth exceeds 128 limit".into(),
                span,
            });
        }
        Ok(Natural { kind, span, depth })
    }

    fn natural(&mut self) -> Result<Natural, ParseError> {
        let mut left = self.natural_factor()?;
        while self.at(&TokenKind::Plus) || self.at(&TokenKind::Minus) {
            let sub = self.bump().kind == TokenKind::Minus;
            let right = self.natural_factor()?;
            let span = left.span.cover(right.span);
            left = Self::natural_node(
                if sub {
                    NatKind::Sub(Box::new(left), Box::new(right))
                } else {
                    NatKind::Add(Box::new(left), Box::new(right))
                },
                span,
            )?;
        }
        Ok(left)
    }

    fn natural_factor(&mut self) -> Result<Natural, ParseError> {
        let mut left = self.natural_atom()?;
        while self.consume(&TokenKind::Star).is_some() {
            let right = self.natural_atom()?;
            let span = left.span.cover(right.span);
            left = Self::natural_node(NatKind::Mul(Box::new(left), Box::new(right)), span)?;
        }
        Ok(left)
    }

    fn natural_atom(&mut self) -> Result<Natural, ParseError> {
        self.nested(|parser| {
            let token = parser.current().clone();
            if parser.consume(&TokenKind::LParen).is_some() {
                let mut natural = parser.natural()?;
                let close = parser.expect(&TokenKind::RParen)?;
                natural.span = token.span.cover(close.span);
                Ok(natural)
            } else {
                let kind = match &token.kind {
                    TokenKind::Zero => NatKind::Number(0),
                    TokenKind::One => NatKind::Number(1),
                    TokenKind::Natural(digits) => {
                        if digits.starts_with('0') {
                            return Err(parser.error("natural literal has a leading zero"));
                        }
                        NatKind::Number(
                            digits
                                .parse()
                                .map_err(|_| parser.error("natural literal exceeds i128 limit"))?,
                        )
                    }
                    kind => match Self::natural_name(kind) {
                        Some(name) => NatKind::Name(name.to_owned()),
                        None => return Err(parser.error("expected a static natural expression")),
                    },
                };
                parser.bump();
                Self::natural_node(kind, token.span)
            }
        })
    }

    fn predicate(&mut self) -> Result<Predicate, ParseError> {
        let left = self.natural()?;
        let comparison = match self.current().kind {
            TokenKind::EqualEqual => Compare::Eq,
            TokenKind::NotEqual => Compare::Ne,
            TokenKind::LAngle => Compare::Lt,
            TokenKind::LessEqual => Compare::Le,
            TokenKind::RAngle => Compare::Gt,
            TokenKind::GreaterEqual => Compare::Ge,
            _ => return Err(self.error("expected static comparison")),
        };
        self.bump();
        Ok(Predicate {
            left,
            comparison,
            right: self.natural()?,
        })
    }

    // Only the existing two-stage application spelling is special. A normal
    // `controlled(q)` remains a call to the ordinary identifier `controlled`.
    fn controlled_application(&self) -> bool {
        if !self.word("controlled")
            || self
                .tokens
                .get(self.pos + 1)
                .is_none_or(|t| t.kind != TokenKind::LParen)
        {
            return false;
        }
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().skip(self.pos + 1) {
            match token.kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return self
                            .tokens
                            .get(index + 1)
                            .is_some_and(|t| t.kind == TokenKind::LParen);
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
        }
        false
    }

    fn ty_inner(&mut self) -> Result<Type, ParseError> {
        if self.word("CBits") || self.current().kind == TokenKind::CBit {
            return Err(self.error("CBit/CBits types were removed; use Bit/Bits<n>"));
        }
        if self.word("Bits") {
            let token = self.bump();
            self.expect(&TokenKind::LAngle)?;
            let size = self.natural()?;
            let end = self.expect(&TokenKind::RAngle)?;
            return Ok(Type {
                kind: TypeKind::Bits(size),
                span: token.span.cover(end.span),
            });
        }

        if let Some(token) = self.consume(&TokenKind::Unit) {
            return Ok(Type {
                kind: TypeKind::Unit,
                span: token.span,
            });
        }
        if let Some(token) = self.consume(&TokenKind::Bit) {
            return Ok(Type {
                kind: TypeKind::Bit,
                span: token.span,
            });
        }
        if let Some(open) = self.consume(&TokenKind::Q) {
            self.expect(&TokenKind::LAngle)?;
            let inner = self.basis_type()?;
            let close = self.expect(&TokenKind::RAngle)?;
            return Ok(Type {
                kind: TypeKind::Q(Box::new(inner)),
                span: open.span.cover(close.span),
            });
        }
        if matches!(self.current().kind, TokenKind::Ident(_)) {
            let name = self.ident()?;
            return Ok(Type {
                span: name.span,
                kind: TypeKind::Named(name),
            });
        }
        self.tuple_type(false)
    }

    fn basis_type(&mut self) -> Result<Type, ParseError> {
        let ty = self.nested(Self::basis_type_inner)?;
        Self::type_depth(&ty)?;
        Ok(ty)
    }

    fn basis_type_inner(&mut self) -> Result<Type, ParseError> {
        if self.word("CBits") || self.current().kind == TokenKind::CBit {
            return Err(self.error("CBit/CBits types were removed; use Bit/Bits<n>"));
        }
        if self.word("Bits") {
            let token = self.bump();
            self.expect(&TokenKind::LAngle)?;
            let size = self.natural()?;
            let end = self.expect(&TokenKind::RAngle)?;
            return Ok(Type {
                kind: TypeKind::Bits(size),
                span: token.span.cover(end.span),
            });
        }

        if let Some(token) = self.consume(&TokenKind::Unit) {
            return Ok(Type {
                kind: TypeKind::Unit,
                span: token.span,
            });
        }
        if let Some(token) = self.consume(&TokenKind::Bit) {
            return Ok(Type {
                kind: TypeKind::Bit,
                span: token.span,
            });
        }
        if matches!(self.current().kind, TokenKind::Ident(_)) {
            let name = self.ident()?;
            return Ok(Type {
                span: name.span,
                kind: TypeKind::Named(name),
            });
        }
        self.tuple_type(true)
    }

    fn tuple_type(&mut self, basis_only: bool) -> Result<Type, ParseError> {
        let open = self.expect(&TokenKind::LParen)?;
        if let Some(close) = self.consume(&TokenKind::RParen) {
            return Err(ParseError {
                span: open.span.cover(close.span),
                message: "empty tuple type spelling was removed; use Unit (the value remains ())"
                    .into(),
            });
        }
        let mut fields = vec![if basis_only {
            self.basis_type()?
        } else {
            self.ty()?
        }];
        self.expect(&TokenKind::Comma)?;
        loop {
            fields.push(if basis_only {
                self.basis_type()?
            } else {
                self.ty()?
            });
            self.tuple_arity(fields.len())?;
            if self.consume(&TokenKind::Comma).is_none() {
                break;
            }
        }
        let close = self.expect(&TokenKind::RParen)?;
        let ty = Type {
            kind: TypeKind::Tuple(fields),
            span: open.span.cover(close.span),
        };
        Self::type_depth(&ty)?;
        Ok(ty)
    }

    fn tuple_arity(&self, fields: usize) -> Result<(), ParseError> {
        if fields > MAX_TUPLE_FIELDS {
            return Err(self.error("tuple exceeds the initial 64-field limit"));
        }
        Ok(())
    }

    fn type_depth(ty: &Type) -> Result<(), ParseError> {
        let mut pending = vec![(ty, 1)];
        while let Some((node, depth)) = pending.pop() {
            if depth > MAX_NESTING {
                return Err(ParseError {
                    message: "type AST exceeds the initial 64-level limit".into(),
                    span: node.span,
                });
            }
            match &node.kind {
                TypeKind::Tuple(fields) => {
                    pending.extend(fields.iter().map(|field| (field, depth + 1)))
                }
                TypeKind::Q(inner) => pending.push((inner, depth + 1)),
                _ => {}
            }
        }
        Ok(())
    }

    fn basis_block(&mut self) -> Result<(BasisExpr, Span), ParseError> {
        let open = self.expect(&TokenKind::LBrace)?;
        let expr = self.basis_expr()?;
        let close = self.expect(&TokenKind::RBrace)?;
        Ok((expr, open.span.cover(close.span)))
    }

    fn block(&mut self) -> Result<Block, ParseError> {
        self.block_mode(false)
    }

    fn block_mode(&mut self, fold: bool) -> Result<Block, ParseError> {
        let open = self.expect(&TokenKind::LBrace)?;
        self.nested(|parser| parser.block_contents_inner(open.span.start, fold))
    }

    fn block_contents(&mut self, start: usize) -> Result<Block, ParseError> {
        self.nested(|parser| parser.block_contents_inner(start, false))
    }

    fn block_contents_inner(&mut self, start: usize, fold: bool) -> Result<Block, ParseError> {
        let mut statements = Vec::new();
        loop {
            if self.at(&TokenKind::RBrace) {
                if fold {
                    return Err(self.error("static fold requires yield"));
                }
                let close = self.bump();
                return Ok(Block {
                    implicit_result: true,
                    statements,
                    result: Box::new(Expr {
                        kind: ExprKind::Unit,
                        span: close.span,
                    }),
                    span: Span::new(start, close.span.end),
                });
            }
            if let Some(let_token) = self.consume(&TokenKind::Let) {
                let pattern = self.pattern()?;
                self.expect(&TokenKind::Equals)?;
                let value = self.expr()?;
                let end = self.expect(&TokenKind::Semicolon)?.span.end;
                statements.push(Stmt {
                    kind: StmtKind::Let { pattern, value },
                    span: Span::new(let_token.span.start, end),
                });
                continue;
            }
            let yielded = fold && self.word("yield");
            if yielded {
                self.bump();
            }
            let empty_yield = yielded && self.at(&TokenKind::RBrace);
            let expr = if empty_yield {
                Expr {
                    kind: ExprKind::Unit,
                    span: self.current().span,
                }
            } else {
                self.expr()?
            };
            if yielded {
                self.consume(&TokenKind::Semicolon);
                let close = self.expect(&TokenKind::RBrace)?;
                return Ok(Block {
                    implicit_result: empty_yield,
                    statements,
                    result: Box::new(expr),
                    span: Span::new(start, close.span.end),
                });
            }
            if let Some(semicolon) = self.consume(&TokenKind::Semicolon) {
                statements.push(Stmt {
                    span: expr.span.cover(semicolon.span),
                    kind: StmtKind::Expr(expr),
                });
                continue;
            }
            if fold {
                return Err(ParseError {
                    message: "static fold requires yield".into(),
                    span: expr.span,
                });
            }
            let close = self.expect(&TokenKind::RBrace)?;
            return Ok(Block {
                implicit_result: false,
                statements,
                result: Box::new(expr),
                span: Span::new(start, close.span.end),
            });
        }
    }

    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        let pattern = self.nested(Self::pattern_inner)?;
        Self::pattern_depth(&pattern)?;
        Ok(pattern)
    }

    fn pattern_inner(&mut self) -> Result<Pattern, ParseError> {
        if let TokenKind::Ident(name) = self.current().kind.clone() {
            let token = self.bump();
            if name == "_" {
                return Ok(Pattern {
                    kind: PatternKind::Wildcard,
                    span: token.span,
                });
            }
            return Ok(Pattern {
                kind: PatternKind::Name(Ident {
                    text: name,
                    span: token.span,
                }),
                span: token.span,
            });
        }
        let open = self.expect(&TokenKind::LParen)?;
        if let Some(close) = self.consume(&TokenKind::RParen) {
            return Ok(Pattern {
                kind: PatternKind::Tuple(vec![]),
                span: open.span.cover(close.span),
            });
        }
        let mut fields = vec![self.pattern()?];
        self.expect(&TokenKind::Comma)?;
        loop {
            fields.push(self.pattern()?);
            self.tuple_arity(fields.len())?;
            if self.consume(&TokenKind::Comma).is_none() {
                break;
            }
        }
        let close = self.expect(&TokenKind::RParen)?;
        Ok(Pattern {
            kind: PatternKind::Tuple(fields),
            span: open.span.cover(close.span),
        })
    }

    fn pattern_depth(pattern: &Pattern) -> Result<(), ParseError> {
        let mut pending = vec![(pattern, 1)];
        while let Some((node, depth)) = pending.pop() {
            if depth > MAX_NESTING {
                return Err(ParseError {
                    message: "pattern AST exceeds the initial 64-level limit".into(),
                    span: node.span,
                });
            }
            if let PatternKind::Tuple(fields) = &node.kind {
                pending.extend(fields.iter().map(|field| (field, depth + 1)));
            }
        }
        Ok(())
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.nested(Self::expr_inner)
    }

    fn expr_inner(&mut self) -> Result<Expr, ParseError> {
        // Use an iterative precedence stack so parenthesized expressions do
        // not add three recursive parser frames per nesting level. Operators
        // are left-associative, with `and` above `xor`.
        let mut values = Vec::new();
        let mut operators = Vec::new();
        loop {
            let mut negations = Vec::new();
            while let Some(token) = self.consume(&TokenKind::Not) {
                negations.push(token.span);
                if self.nesting + negations.len() > MAX_NESTING {
                    return Err(self.error("expression exceeds the initial 64-level limit"));
                }
            }
            self.nesting += negations.len();
            let parsed = self.expr_primary();
            self.nesting -= negations.len();
            let mut value = parsed?;
            let depth = Self::expr_depth(&value)? + negations.len();
            if depth > MAX_NESTING {
                return Err(self.error("expression AST exceeds the initial 64-level limit"));
            }
            for span in negations.into_iter().rev() {
                value = Expr {
                    span: span.cover(value.span),
                    kind: ExprKind::Not(Box::new(value)),
                };
            }
            values.push((value, depth));
            let priority = match self.current().kind {
                TokenKind::And => 2,
                TokenKind::Xor => 1,
                _ => break,
            };
            while operators
                .last()
                .is_some_and(|(previous, _)| *previous >= priority)
            {
                Self::reduce_boolean(&mut values, operators.pop().unwrap().1)?;
            }
            operators.push((priority, self.bump()));
        }
        while let Some((_, operator)) = operators.pop() {
            Self::reduce_boolean(&mut values, operator)?;
        }
        Ok(values.pop().unwrap().0)
    }

    fn reduce_boolean(values: &mut Vec<(Expr, usize)>, operator: Token) -> Result<(), ParseError> {
        let (right, right_depth) = values.pop().unwrap();
        let (left, left_depth) = values.pop().unwrap();
        let depth = 1 + left_depth.max(right_depth);
        if depth > MAX_NESTING {
            return Err(ParseError {
                message: "expression AST exceeds the initial 64-level limit".to_owned(),
                span: operator.span,
            });
        }
        let span = left.span.cover(right.span);
        let kind = match operator.kind {
            TokenKind::And => ExprKind::And(Box::new(left), Box::new(right)),
            TokenKind::Xor => ExprKind::Xor(Box::new(left), Box::new(right)),
            _ => unreachable!("Boolean operator stack"),
        };
        values.push((Expr { kind, span }, depth));
        Ok(())
    }

    fn expr_depth(expr: &Expr) -> Result<usize, ParseError> {
        // Keep this iterative walk outside the recursive parsing frames.
        // Binary chains can deepen the AST without deepening the parse stack.
        let mut maximum = 1;
        let mut pending = vec![(expr, 1)];
        while let Some((node, depth)) = pending.pop() {
            if depth > MAX_NESTING {
                return Err(ParseError {
                    message: "expression AST exceeds the initial 64-level limit".to_owned(),
                    span: node.span,
                });
            }
            maximum = maximum.max(depth);
            match &node.kind {
                ExprKind::Not(inner)
                | ExprKind::ApplyContract { input: inner, .. }
                | ExprKind::Adjoint { input: inner, .. }
                | ExprKind::RepeatStatic { input: inner, .. }
                | ExprKind::CoherentLift { input: inner, .. } => {
                    pending.push((inner, depth + 1));
                }
                ExprKind::Tuple(fields) => {
                    pending.extend(fields.iter().map(|field| (field, depth + 1)))
                }
                ExprKind::Xor(a, b)
                | ExprKind::And(a, b)
                | ExprKind::QuantumIf {
                    control: a,
                    target: b,
                    ..
                } => pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)]),
                ExprKind::Call { args, .. } | ExprKind::Controlled { args, .. } => {
                    pending.extend(args.iter().map(|arg| (arg, depth + 1)));
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push((condition, depth + 1));
                    for block in [then_branch, else_branch] {
                        pending.push((&block.result, depth + 1));
                        pending.extend(block.statements.iter().map(|statement| {
                            let value = match &statement.kind {
                                StmtKind::Let { value, .. } | StmtKind::Expr(value) => value,
                            };
                            (value, depth + 1)
                        }));
                    }
                }
                ExprKind::StaticIf {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    for block in [then_branch, else_branch] {
                        pending.push((&block.result, depth + 1));
                        pending.extend(block.statements.iter().map(|s| {
                            (
                                match &s.kind {
                                    StmtKind::Let { value, .. } | StmtKind::Expr(value) => value,
                                },
                                depth + 1,
                            )
                        }));
                    }
                }
                ExprKind::StaticFold {
                    initial: source,
                    body,
                    ..
                }
                | ExprKind::WithComputed { source, body, .. }
                | ExprKind::CertifiedComputed { source, body, .. } => {
                    pending.push((source, depth + 1));
                    pending.push((&body.result, depth + 1));
                    pending.extend(body.statements.iter().map(|statement| {
                        let value = match &statement.kind {
                            StmtKind::Let { value, .. } | StmtKind::Expr(value) => value,
                        };
                        (value, depth + 1)
                    }));
                }
                ExprKind::Name(_) | ExprKind::Bit(_) | ExprKind::Unit => {}
            }
        }
        Ok(maximum)
    }

    fn expr_primary(&mut self) -> Result<Expr, ParseError> {
        if self.word("for")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| t.kind == TokenKind::Static)
        {
            let open = self.bump();
            self.bump();
            let index = self.natural_ident()?;
            self.expect_word("in")?;
            let start = self.natural()?;
            self.expect(&TokenKind::DotDot)?;
            let end = self.natural()?;
            self.expect_word("carry")?;
            let carry = self.pattern()?;
            self.expect(&TokenKind::Equals)?;
            let initial = Box::new(self.expr()?);
            let body = self.block_mode(true)?;
            return Ok(Expr {
                span: open.span.cover(body.span),
                kind: ExprKind::StaticFold {
                    index,
                    start,
                    end,
                    carry,
                    initial,
                    body,
                },
            });
        }
        if self.controlled_application() {
            let start = self.bump();
            self.expect(&TokenKind::LParen)?;
            let operation = self.static_op()?;
            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::LParen)?;
            let args = self.expr_args()?;
            let end = self.expect(&TokenKind::RParen)?;
            return Ok(Expr {
                kind: ExprKind::Controlled { operation, args },
                span: start.span.cover(end.span),
            });
        }

        if let Some(start) = self.consume(&TokenKind::ApplyContract) {
            return self.apply_contract(start.span);
        }
        if self.at(&TokenKind::Adjoint) || self.at(&TokenKind::RepeatStatic) {
            let start = self.bump();
            self.expect(&TokenKind::LParen)?;
            let count = if start.kind == TokenKind::RepeatStatic {
                let count = match &self.current().kind {
                    TokenKind::Zero => 0,
                    TokenKind::One => 1,
                    TokenKind::Natural(digits) if !digits.starts_with('0') => digits
                        .parse::<u16>()
                        .ok()
                        .filter(|n| *n <= 4096)
                        .ok_or_else(|| {
                            self.error("static repetition exceeds the 4096-count limit")
                        })?,
                    _ => return Err(self.error("expected canonical static natural number")),
                };
                self.bump();
                self.expect(&TokenKind::Comma)?;
                Some(count)
            } else {
                None
            };
            let operation = self.static_op()?;
            self.expect(&TokenKind::Comma)?;
            let input = Box::new(self.expr()?);
            let end = self.expect(&TokenKind::RParen)?;
            let kind = if let Some(count) = count {
                ExprKind::RepeatStatic {
                    count,
                    function: match operation.kind {
                        StaticOpKind::Name(name) => name,
                        _ => return Err(self.error("repeat_static requires a function name")),
                    },
                    input,
                }
            } else {
                ExprKind::Adjoint { operation, input }
            };
            return Ok(Expr {
                kind,
                span: start.span.cover(end.span),
            });
        }
        if let Some(start) = self.consume(&TokenKind::Qif) {
            return self.quantum_if(start);
        }
        if let Some(if_token) = self.consume(&TokenKind::If) {
            return self.classical_if(if_token);
        }
        if let Some(do_token) = self.consume(&TokenKind::Do) {
            return self.coherent_lift(do_token);
        }
        if let Some(with_token) = self.consume(&TokenKind::WithComputed) {
            return self.with_computed(with_token);
        }
        self.expr_atom()
    }

    fn quantum_if(&mut self, start: Token) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let control = Box::new(self.expr()?);
        self.expect(&TokenKind::Comma)?;
        let target = Box::new(self.expr()?);
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::LBrace)?;
        self.expect(&TokenKind::Zero)?;
        self.expect(&TokenKind::FatArrow)?;
        let zero = self.ident()?;
        self.expect(&TokenKind::Comma)?;
        self.expect(&TokenKind::One)?;
        self.expect(&TokenKind::FatArrow)?;
        let one = self.ident()?;
        let end = self.expect(&TokenKind::RBrace)?;
        Ok(Expr {
            kind: ExprKind::QuantumIf {
                control,
                target,
                zero,
                one,
            },
            span: start.span.cover(end.span),
        })
    }

    fn classical_if(&mut self, if_token: Token) -> Result<Expr, ParseError> {
        if self.consume(&TokenKind::Static).is_some() {
            let predicate = self.predicate()?;
            let then_branch = self.block()?;
            self.expect(&TokenKind::Else)?;
            let else_branch = self.block()?;
            return Ok(Expr {
                span: Span::new(if_token.span.start, else_branch.span.end),
                kind: ExprKind::StaticIf {
                    predicate,
                    then_branch,
                    else_branch,
                },
            });
        }
        let condition = self.expr()?;
        let then_branch = self.block()?;
        self.expect(&TokenKind::Else)?;
        let else_branch = self.block()?;
        let span = Span::new(if_token.span.start, else_branch.span.end);
        Ok(Expr {
            kind: ExprKind::If {
                condition: Box::new(condition),
                then_branch,
                else_branch,
            },
            span,
        })
    }

    fn coherent_lift(&mut self, do_token: Token) -> Result<Expr, ParseError> {
        let binder = self.pattern()?;
        self.expect(&TokenKind::LeftArrow)?;
        let input = self.expr()?;
        self.expect(&TokenKind::Semicolon)?;
        self.expect(&TokenKind::Pure)?;
        let basis = self.basis_expr()?;
        let span = Span::new(do_token.span.start, basis.span.end);
        Ok(Expr {
            kind: ExprKind::CoherentLift {
                binder,
                input: Box::new(input),
                basis,
            },
            span,
        })
    }

    fn with_computed(&mut self, with_token: Token) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let source = self.expr()?;
        self.expect(&TokenKind::Comma)?;
        let function = self.ident()?;
        let logical = if self.consume(&TokenKind::Comma).is_some() {
            Some(self.ident()?)
        } else {
            None
        };
        self.expect(&TokenKind::RParen)?;
        let open = self.expect(&TokenKind::LBrace)?;
        self.expect(&TokenKind::Pipe)?;
        let binder = self.ident()?;
        let ancilla_binder = if logical.is_some() {
            self.expect(&TokenKind::Comma)?;
            Some(self.ident()?)
        } else {
            None
        };
        self.expect(&TokenKind::Pipe)?;
        let body = self.block_contents(open.span.start)?;
        let span = Span::new(with_token.span.start, body.span.end);
        let kind = if let Some(logical) = logical {
            ExprKind::CertifiedComputed {
                source: Box::new(source),
                function,
                logical: Box::new(logical),
                data_binder: Box::new(binder),
                ancilla_binder: Box::new(ancilla_binder.expect("certified binder")),
                body,
            }
        } else {
            ExprKind::WithComputed {
                source: Box::new(source),
                function,
                binder,
                body,
            }
        };
        Ok(Expr { kind, span })
    }

    fn apply_contract(&mut self, start: Span) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let implementation = self.ident()?;
        self.expect(&TokenKind::Comma)?;
        let specification = self.ident()?;
        self.expect(&TokenKind::Comma)?;
        let input = Box::new(self.expr()?);
        let end = self.expect(&TokenKind::RParen)?;
        Ok(Expr {
            kind: ExprKind::ApplyContract {
                implementation,
                specification,
                input,
            },
            span: start.cover(end.span),
        })
    }

    /// One literal classification for ordinary and basis Bit expressions.
    /// Explicit natural positions use their own bounded Nat parser.
    fn bit_literal(&mut self) -> Result<Option<(bool, Span)>, ParseError> {
        let value = match self.current().kind {
            TokenKind::Zero => false,
            TokenKind::One => true,
            TokenKind::True | TokenKind::False => {
                return Err(self.error("true/false literals were removed; use 1/0 for Bit"));
            }
            TokenKind::Natural(_) => return Err(self.error("Bit literals must be 0 or 1")),
            _ => return Ok(None),
        };
        Ok(Some((value, self.bump().span)))
    }

    fn expr_atom(&mut self) -> Result<Expr, ParseError> {
        if let Some((value, span)) = self.bit_literal()? {
            return Ok(Expr {
                kind: ExprKind::Bit(value),
                span,
            });
        }
        if let TokenKind::Ident(_) = self.current().kind {
            return self.named_expr();
        }
        let open = self.expect(&TokenKind::LParen)?;
        if let Some(close) = self.consume(&TokenKind::RParen) {
            return Ok(Expr {
                kind: ExprKind::Unit,
                span: open.span.cover(close.span),
            });
        }
        let mut left = self.expr()?;
        if self.consume(&TokenKind::Comma).is_some() {
            let mut fields = vec![left];
            loop {
                fields.push(self.expr()?);
                self.tuple_arity(fields.len())?;
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
            let close = self.expect(&TokenKind::RParen)?;
            let result = Expr {
                kind: ExprKind::Tuple(fields),
                span: open.span.cover(close.span),
            };
            Self::expr_depth(&result)?;
            return Ok(result);
        }
        let close = self.expect(&TokenKind::RParen)?;
        left.span = open.span.cover(close.span);
        Ok(left)
    }

    fn named_expr(&mut self) -> Result<Expr, ParseError> {
        let ident = self.ident()?;
        let mut static_args = Vec::new();
        let mut end = ident.span;
        if self.consume(&TokenKind::LBracket).is_some() {
            static_args = self.static_arguments()?;
            end = self.tokens[self.pos - 1].span;
            if !static_args.is_empty() && !self.at(&TokenKind::LParen) {
                return Err(self.error("static arguments require a call"));
            }
        }
        if self.consume(&TokenKind::LParen).is_some() {
            let args = self.expr_args()?;
            let close = self.expect(&TokenKind::RParen)?;
            let span = ident.span.cover(close.span);
            return Ok(Expr {
                kind: ExprKind::Call {
                    callee: ident,
                    static_args,
                    args,
                },
                span,
            });
        }
        Ok(Expr {
            span: ident.span.cover(end),
            kind: ExprKind::Name(ident),
        })
    }

    fn expr_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        if !self.at(&TokenKind::RParen) {
            loop {
                args.push(self.expr()?);
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        Ok(args)
    }

    fn basis_expr(&mut self) -> Result<BasisExpr, ParseError> {
        let expr = self.basis_xor()?;
        Self::basis_depth(&expr)?;
        Ok(expr)
    }

    fn basis_depth(expr: &BasisExpr) -> Result<(), ParseError> {
        // A left-associated chain can grow the AST without growing the parse
        // stack. Nested chains must also share the AST depth budget.
        let mut pending = vec![(expr, 1)];
        while let Some((node, depth)) = pending.pop() {
            if depth > MAX_NESTING {
                return Err(ParseError {
                    message: "basis AST exceeds the initial 64-level limit".to_owned(),
                    span: node.span,
                });
            }
            match &node.kind {
                BasisExprKind::Not(inner) => pending.push((inner, depth + 1)),
                BasisExprKind::Tuple(fields) => {
                    pending.extend(fields.iter().map(|field| (field, depth + 1)))
                }
                BasisExprKind::Xor(a, b) | BasisExprKind::And(a, b) => {
                    pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
                }
                BasisExprKind::Call { args, .. } => {
                    pending.extend(args.iter().map(|arg| (arg, depth + 1)))
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn basis_xor(&mut self) -> Result<BasisExpr, ParseError> {
        let mut left = self.basis_and()?;
        let mut chain = 0;
        while self.consume(&TokenKind::Xor).is_some() {
            chain += 1;
            if self.nesting + chain > MAX_NESTING {
                return Err(self.error("basis expression exceeds the initial 64-level limit"));
            }
            let right = self.basis_and()?;
            let span = left.span.cover(right.span);
            left = BasisExpr {
                kind: BasisExprKind::Xor(Box::new(left), Box::new(right)),
                span,
            };
        }
        Ok(left)
    }

    fn basis_and(&mut self) -> Result<BasisExpr, ParseError> {
        let mut left = self.basis_unary()?;
        let mut chain = 0;
        while self.consume(&TokenKind::And).is_some() {
            chain += 1;
            if self.nesting + chain > MAX_NESTING {
                return Err(self.error("basis expression exceeds the initial 64-level limit"));
            }
            let right = self.basis_unary()?;
            let span = left.span.cover(right.span);
            left = BasisExpr {
                kind: BasisExprKind::And(Box::new(left), Box::new(right)),
                span,
            };
        }
        Ok(left)
    }

    fn basis_unary(&mut self) -> Result<BasisExpr, ParseError> {
        self.nested(Self::basis_unary_inner)
    }

    fn basis_unary_inner(&mut self) -> Result<BasisExpr, ParseError> {
        if let Some(not) = self.consume(&TokenKind::Not) {
            let inner = self.basis_unary()?;
            let span = not.span.cover(inner.span);
            return Ok(BasisExpr {
                kind: BasisExprKind::Not(Box::new(inner)),
                span,
            });
        }
        self.basis_atom()
    }

    fn basis_atom(&mut self) -> Result<BasisExpr, ParseError> {
        self.nested(Self::basis_atom_inner)
    }

    fn basis_atom_inner(&mut self) -> Result<BasisExpr, ParseError> {
        if matches!(self.current().kind, TokenKind::Natural(_)) {
            return Err(self.error("Bit literal must be 0 or 1"));
        }
        if let TokenKind::Ident(_) = self.current().kind {
            let ident = self.ident()?;
            if self.consume(&TokenKind::LParen).is_some() {
                let mut args = Vec::new();
                if !self.at(&TokenKind::RParen) {
                    loop {
                        args.push(self.basis_expr()?);
                        if self.consume(&TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                }
                let close = self.expect(&TokenKind::RParen)?;
                return Ok(BasisExpr {
                    span: ident.span.cover(close.span),
                    kind: BasisExprKind::Call {
                        callee: ident,
                        args,
                    },
                });
            }
            return Ok(BasisExpr {
                span: ident.span,
                kind: BasisExprKind::Name(ident),
            });
        }
        if let Some((value, span)) = self.bit_literal()? {
            return Ok(BasisExpr {
                kind: BasisExprKind::Bit(value),
                span,
            });
        }
        let open = self.expect(&TokenKind::LParen)?;
        if let Some(close) = self.consume(&TokenKind::RParen) {
            return Ok(BasisExpr {
                kind: BasisExprKind::Unit,
                span: open.span.cover(close.span),
            });
        }
        let mut left = self.basis_expr()?;
        if self.consume(&TokenKind::Comma).is_some() {
            let mut fields = vec![left];
            loop {
                fields.push(self.basis_expr()?);
                self.tuple_arity(fields.len())?;
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
            let close = self.expect(&TokenKind::RParen)?;
            let result = BasisExpr {
                kind: BasisExprKind::Tuple(fields),
                span: open.span.cover(close.span),
            };
            Self::basis_depth(&result)?;
            return Ok(result);
        }
        let close = self.expect(&TokenKind::RParen)?;
        left.span = open.span.cover(close.span);
        Ok(left)
    }

    // Type words retain their lexer classification and meaning in type/runtime
    // syntax. Only a static-natural grammar position treats them as names.
    fn natural_name(kind: &TokenKind) -> Option<&str> {
        match kind {
            TokenKind::Ident(name) => Some(name),
            TokenKind::Q => Some("Q"),
            TokenKind::Op => Some("Op"),
            TokenKind::Unit => Some("Unit"),
            TokenKind::Bit => Some("Bit"),
            TokenKind::CBit => Some("CBit"),
            _ => None,
        }
    }

    fn natural_ident(&mut self) -> Result<Ident, ParseError> {
        match Self::natural_name(&self.current().kind) {
            Some(name) if name != "_" => {
                let text = name.to_owned();
                let span = self.bump().span;
                Ok(Ident { text, span })
            }
            _ => Err(self.error("expected an identifier")),
        }
    }

    fn ident(&mut self) -> Result<Ident, ParseError> {
        match &self.current().kind {
            TokenKind::Ident(name) if name != "_" => {
                let text = name.clone();
                let span = self.bump().span;
                Ok(Ident { text, span })
            }
            _ => Err(self.error("expected an identifier")),
        }
    }

    fn at(&self, expected: &TokenKind) -> bool {
        discriminant(&self.current().kind) == discriminant(expected)
    }

    fn consume(&mut self, expected: &TokenKind) -> Option<Token> {
        self.at(expected).then(|| self.bump())
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<Token, ParseError> {
        self.consume(expected).ok_or_else(|| {
            self.error(&format!(
                "expected {}, found {}",
                expected.description(),
                self.current().kind.description()
            ))
        })
    }

    fn bump(&mut self) -> Token {
        let token = self.current().clone();
        // Keep the EOF sentinel available for diagnostics after truncated input.
        if token.kind != TokenKind::Eof {
            self.pos += 1;
        }
        token
    }

    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn error(&self, message: &str) -> ParseError {
        ParseError {
            message: message.to_owned(),
            span: self.current().span,
        }
    }
}

#[cfg(test)]
mod tests;
