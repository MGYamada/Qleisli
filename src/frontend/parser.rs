//! Parser for the provisional finite `.qli` grammar in `docs/syntax-v0.md`.
//!
//! Parsing does not resolve names or establish typing, effects, linear use, or
//! quantum validity. Those checks must happen before producing trusted IR.

use std::fmt;
use std::mem::discriminant;

use super::ast::{
    BasisExpr, BasisExprKind, Block, Decl, Expr, ExprKind, FnBody, FnKind, Ident, Module, Param,
    Pattern, PatternKind, Span, Stmt, StmtKind, Type, TypeKind, UseDecl,
};
use super::lexer::{LexError, Token, TokenKind, lex};

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
    let tokens = lex(source)?;
    Parser {
        tokens,
        pos: 0,
        nesting: 0,
    }
    .module(source.len())
}

/// An implementation limit on recursive syntax and left-associated basis ASTs.
const MAX_NESTING: usize = 64;

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    nesting: usize,
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
                uses.push(self.use_decl()?);
            } else if self.at(&TokenKind::Pub)
                || self.at(&TokenKind::Basis)
                || self.at(&TokenKind::Iso)
                || self.at(&TokenKind::Unitary)
                || self.at(&TokenKind::Observe)
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

    fn use_decl(&mut self) -> Result<UseDecl, ParseError> {
        let start = self.expect(&TokenKind::Use)?.span.start;
        let first = self.ident()?;
        let is_std = first.text == "std";
        let mut path = vec![first];
        self.expect(&TokenKind::DoubleColon)?;
        // `basis` and `observe` are declaration keywords, but also the names
        // of compiler-owned std modules. Only that path position admits them.
        if is_std && matches!(self.current().kind, TokenKind::Basis | TokenKind::Observe) {
            let token = self.bump();
            let text = match token.kind {
                TokenKind::Basis => "basis",
                TokenKind::Observe => "observe",
                _ => unreachable!("checked std module keyword"),
            };
            path.push(Ident {
                text: text.to_owned(),
                span: token.span,
            });
            self.expect(&TokenKind::DoubleColon)?;
            path.push(self.ident()?);
        } else {
            path.push(self.ident()?);
        }
        while self.consume(&TokenKind::DoubleColon).is_some() {
            path.push(self.ident()?);
        }
        let end = self.expect(&TokenKind::Semicolon)?.span.end;
        Ok(UseDecl {
            path,
            span: Span::new(start, end),
        })
    }

    fn decl(&mut self) -> Result<Decl, ParseError> {
        let pub_token = self.consume(&TokenKind::Pub);
        let public = pub_token.is_some();
        let start = pub_token.map_or_else(|| self.current().span.start, |token| token.span.start);
        let kind = if self.consume(&TokenKind::Basis).is_some() {
            FnKind::Basis
        } else if self.consume(&TokenKind::Iso).is_some() {
            FnKind::Iso
        } else if self.consume(&TokenKind::Unitary).is_some() {
            FnKind::Unitary
        } else if self.consume(&TokenKind::Observe).is_some() {
            FnKind::Observe
        } else {
            return Err(self.error("expected `basis`, `iso`, `unitary`, or `observe` after `pub`"));
        };
        self.expect(&TokenKind::Fn)?;
        let name = self.ident()?;
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        if !self.at(&TokenKind::RParen) {
            loop {
                let param_name = self.ident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = if kind == FnKind::Basis {
                    self.basis_type()?
                } else {
                    self.ty()?
                };
                let span = Span::new(param_name.span.start, ty.span.end);
                params.push(Param {
                    name: param_name,
                    ty,
                    span,
                });
                if self.consume(&TokenKind::Comma).is_none() {
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
            params,
            return_type,
            body,
            span: Span::new(start, end),
        })
    }

    fn ty(&mut self) -> Result<Type, ParseError> {
        self.nested(Self::ty_inner)
    }

    fn ty_inner(&mut self) -> Result<Type, ParseError> {
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
        if let Some(token) = self.consume(&TokenKind::CBit) {
            return Ok(Type {
                kind: TypeKind::CBit,
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
        self.tuple_type(false)
    }

    fn basis_type(&mut self) -> Result<Type, ParseError> {
        self.nested(Self::basis_type_inner)
    }

    fn basis_type_inner(&mut self) -> Result<Type, ParseError> {
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
        self.tuple_type(true)
    }

    fn tuple_type(&mut self, basis_only: bool) -> Result<Type, ParseError> {
        let open = self.expect(&TokenKind::LParen)?;
        let left = if basis_only {
            self.basis_type()?
        } else {
            self.ty()?
        };
        self.expect(&TokenKind::Comma)?;
        let right = if basis_only {
            self.basis_type()?
        } else {
            self.ty()?
        };
        let close = self.expect(&TokenKind::RParen)?;
        Ok(Type {
            kind: TypeKind::Tuple(Box::new(left), Box::new(right)),
            span: open.span.cover(close.span),
        })
    }

    fn basis_block(&mut self) -> Result<(BasisExpr, Span), ParseError> {
        let open = self.expect(&TokenKind::LBrace)?;
        let expr = self.basis_expr()?;
        let close = self.expect(&TokenKind::RBrace)?;
        Ok((expr, open.span.cover(close.span)))
    }

    fn block(&mut self) -> Result<Block, ParseError> {
        let open = self.expect(&TokenKind::LBrace)?;
        self.block_contents(open.span.start)
    }

    fn block_contents(&mut self, start: usize) -> Result<Block, ParseError> {
        self.nested(|parser| parser.block_contents_inner(start))
    }

    fn block_contents_inner(&mut self, start: usize) -> Result<Block, ParseError> {
        let mut statements = Vec::new();
        loop {
            if self.at(&TokenKind::RBrace) {
                return Err(self.error("expected a final expression before `}`"));
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
            let expr = self.expr()?;
            if let Some(semicolon) = self.consume(&TokenKind::Semicolon) {
                statements.push(Stmt {
                    span: expr.span.cover(semicolon.span),
                    kind: StmtKind::Expr(expr),
                });
                continue;
            }
            let close = self.expect(&TokenKind::RBrace)?;
            return Ok(Block {
                statements,
                result: Box::new(expr),
                span: Span::new(start, close.span.end),
            });
        }
    }

    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        self.nested(Self::pattern_inner)
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
        let left = self.pattern()?;
        self.expect(&TokenKind::Comma)?;
        let right = self.pattern()?;
        let close = self.expect(&TokenKind::RParen)?;
        Ok(Pattern {
            kind: PatternKind::Tuple(Box::new(left), Box::new(right)),
            span: open.span.cover(close.span),
        })
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.nested(Self::expr_inner)
    }

    fn expr_inner(&mut self) -> Result<Expr, ParseError> {
        if let Some(if_token) = self.consume(&TokenKind::If) {
            let condition = self.expr()?;
            let then_branch = self.block()?;
            self.expect(&TokenKind::Else)?;
            let else_branch = self.block()?;
            let span = Span::new(if_token.span.start, else_branch.span.end);
            return Ok(Expr {
                kind: ExprKind::If {
                    condition: Box::new(condition),
                    then_branch,
                    else_branch,
                },
                span,
            });
        }
        if let Some(do_token) = self.consume(&TokenKind::Do) {
            let binder = self.ident()?;
            self.expect(&TokenKind::LeftArrow)?;
            let input = self.expr()?;
            self.expect(&TokenKind::Semicolon)?;
            self.expect(&TokenKind::Pure)?;
            let basis = self.basis_expr()?;
            let span = Span::new(do_token.span.start, basis.span.end);
            return Ok(Expr {
                kind: ExprKind::CoherentLift {
                    binder,
                    input: Box::new(input),
                    basis,
                },
                span,
            });
        }
        if let Some(with_token) = self.consume(&TokenKind::WithComputed) {
            self.expect(&TokenKind::LParen)?;
            let source = self.expr()?;
            self.expect(&TokenKind::Comma)?;
            let function = self.ident()?;
            self.expect(&TokenKind::RParen)?;
            let open = self.expect(&TokenKind::LBrace)?;
            self.expect(&TokenKind::Pipe)?;
            let binder = self.ident()?;
            self.expect(&TokenKind::Pipe)?;
            let body = self.block_contents(open.span.start)?;
            let span = Span::new(with_token.span.start, body.span.end);
            return Ok(Expr {
                kind: ExprKind::WithComputed {
                    source: Box::new(source),
                    function,
                    binder,
                    body,
                },
                span,
            });
        }
        self.expr_atom()
    }

    fn expr_atom(&mut self) -> Result<Expr, ParseError> {
        if let TokenKind::Ident(_) = self.current().kind {
            let ident = self.ident()?;
            if self.consume(&TokenKind::LParen).is_some() {
                let args = self.expr_args()?;
                let close = self.expect(&TokenKind::RParen)?;
                let span = ident.span.cover(close.span);
                return Ok(Expr {
                    kind: ExprKind::Call {
                        callee: ident,
                        args,
                    },
                    span,
                });
            }
            return Ok(Expr {
                span: ident.span,
                kind: ExprKind::Name(ident),
            });
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
            let right = self.expr()?;
            let close = self.expect(&TokenKind::RParen)?;
            return Ok(Expr {
                kind: ExprKind::Tuple(Box::new(left), Box::new(right)),
                span: open.span.cover(close.span),
            });
        }
        let close = self.expect(&TokenKind::RParen)?;
        left.span = open.span.cover(close.span);
        Ok(left)
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
        // A left-associated chain can grow the AST without growing the parse
        // stack. Nested chains must also share the AST depth budget.
        let mut pending = vec![(&expr, 1)];
        while let Some((node, depth)) = pending.pop() {
            if depth > MAX_NESTING {
                return Err(ParseError {
                    message: "basis AST exceeds the initial 64-level limit".to_owned(),
                    span: node.span,
                });
            }
            match &node.kind {
                BasisExprKind::Not(inner) => pending.push((inner, depth + 1)),
                BasisExprKind::Tuple(a, b)
                | BasisExprKind::Xor(a, b)
                | BasisExprKind::And(a, b) => {
                    pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
                }
                BasisExprKind::Call { args, .. } => {
                    pending.extend(args.iter().map(|arg| (arg, depth + 1)))
                }
                _ => {}
            }
        }
        Ok(expr)
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
        if let Some(token) = self.consume(&TokenKind::Zero) {
            return Ok(BasisExpr {
                kind: BasisExprKind::Bit(false),
                span: token.span,
            });
        }
        if let Some(token) = self.consume(&TokenKind::One) {
            return Ok(BasisExpr {
                kind: BasisExprKind::Bit(true),
                span: token.span,
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
            let right = self.basis_expr()?;
            let close = self.expect(&TokenKind::RParen)?;
            return Ok(BasisExpr {
                kind: BasisExprKind::Tuple(Box::new(left), Box::new(right)),
                span: open.span.cover(close.span),
            });
        }
        let close = self.expect(&TokenKind::RParen)?;
        left.span = open.span.cover(close.span);
        Ok(left)
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
        self.pos += 1;
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
