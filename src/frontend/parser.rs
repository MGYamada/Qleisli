//! Parser for the provisional finite `.qli` grammar in `docs/syntax-v0.md`.
//!
//! Parsing does not resolve names or establish typing, effects, linear use, or
//! quantum validity. Those checks must happen before producing trusted IR.

use std::fmt;
use std::mem::discriminant;

use super::ast::{
    Access, AccessConstraint, BasisExpr, BasisExprKind, Block, Decl, Expr, ExprKind, FnBody,
    FnKind, Ident, Module, Param, Pattern, PatternKind, Span, StaticOp, StaticOpKind, StaticParam,
    Stmt, StmtKind, Type, TypeKind, UseDecl,
};
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
    let (tokens, comments) = lex_documented(source)?;
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
        } else {
            return Err(self.error("expected `basis`, `iso`, `unitary`, or `observe` after `pub`"));
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
                let name = self.ident()?;
                self.expect(&TokenKind::Colon)?;
                self.expect(&TokenKind::Op)?;
                self.expect(&TokenKind::LAngle)?;
                let basis = self.basis_type()?;
                let meaning = if self.consume(&TokenKind::Comma).is_some() {
                    Some(self.ident()?)
                } else {
                    None
                };
                self.expect(&TokenKind::RAngle)?;
                static_params.push(StaticParam {
                    name,
                    basis,
                    meaning,
                });
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
                let pattern = if kind == FnKind::Basis {
                    self.pattern()?
                } else {
                    let name = self.ident()?;
                    Pattern {
                        span: name.span,
                        kind: PatternKind::Name(name),
                    }
                };
                self.expect(&TokenKind::Colon)?;
                let ty = if kind == FnKind::Basis {
                    self.basis_type()?
                } else {
                    self.ty()?
                };
                let span = Span::new(pattern.span.start, ty.span.end);
                params.push(Param { pattern, ty, span });
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
        let mut requires = Vec::new();
        if self.consume(&TokenKind::Requires).is_some() {
            if static_params.is_empty() {
                return Err(self.error("requires needs static parameters"));
            }
            loop {
                let access = if self.consume(&TokenKind::ApplyAccess).is_some() {
                    Access::Apply
                } else if self.consume(&TokenKind::AdjointAccess).is_some() {
                    Access::Adjoint
                } else {
                    self.expect(&TokenKind::ControlledAccess)?;
                    Access::Controlled
                };
                self.expect(&TokenKind::LParen)?;
                let name = self.ident()?;
                self.expect(&TokenKind::RParen)?;
                requires.push(AccessConstraint { access, name });
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
        if matches!(self.current().kind, TokenKind::Ident(_)) {
            let name = self.ident()?;
            return Ok(StaticOp {
                span: name.span,
                kind: StaticOpKind::Name(name),
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
                let count = match &self.current().kind {
                    TokenKind::Zero => 0,
                    TokenKind::One => 1,
                    TokenKind::Natural(n) if !n.starts_with('0') => n
                        .parse::<u16>()
                        .ok()
                        .filter(|n| *n <= 4096)
                        .ok_or_else(|| self.error("static repetition exceeds 4096"))?,
                    _ => return Err(self.error("expected canonical static natural number")),
                };
                self.bump();
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
        let ty = self.nested(Self::basis_type_inner)?;
        Self::type_depth(&ty)?;
        Ok(ty)
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
                ExprKind::Call { args, .. } => {
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
                ExprKind::WithComputed { source, body, .. }
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
                ExprKind::Name(_) | ExprKind::CBit(_) | ExprKind::Unit => {}
            }
        }
        Ok(maximum)
    }

    fn expr_primary(&mut self) -> Result<Expr, ParseError> {
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
            let function = self.ident()?;
            self.expect(&TokenKind::Comma)?;
            let input = Box::new(self.expr()?);
            let end = self.expect(&TokenKind::RParen)?;
            let kind = if let Some(count) = count {
                ExprKind::RepeatStatic {
                    count,
                    function,
                    input,
                }
            } else {
                ExprKind::Adjoint { function, input }
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

    fn expr_atom(&mut self) -> Result<Expr, ParseError> {
        if let Some(token) = self.consume(&TokenKind::True) {
            return Ok(Expr {
                kind: ExprKind::CBit(true),
                span: token.span,
            });
        }
        if let Some(token) = self.consume(&TokenKind::False) {
            return Ok(Expr {
                kind: ExprKind::CBit(false),
                span: token.span,
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
        if self.consume(&TokenKind::LBracket).is_some() {
            loop {
                static_args.push(self.static_op()?);
                if self.consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(&TokenKind::RBracket)?;
            if !self.at(&TokenKind::LParen) {
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
            span: ident.span,
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
