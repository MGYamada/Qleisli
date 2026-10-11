//! A bounded contextual lexer/parser; the finite public token enum is unchanged.
use super::ast::*;
use super::{Error, Result, Span};

#[derive(Clone)]
struct Token {
    text: String,
    span: Span,
}
fn error(span: Span, message: impl Into<String>) -> Error {
    Error::new("parse", span, message)
}
fn natural_node(kind: NatKind, span: Span) -> Result<Natural> {
    let depth = match &kind {
        NatKind::Number(_) | NatKind::Name(_) => 1,
        NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => 1 + a.depth.max(b.depth),
    };
    if depth > 128 {
        return Err(Error::new(
            "limit",
            span,
            "natural expression depth exceeds 128",
        ));
    }
    Ok(Natural { kind, span, depth })
}
fn tokens(source: &str) -> Result<Vec<Token>> {
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
pub(super) fn parse(source: &str) -> Result<Module> {
    let mut p = Parser {
        tokens: tokens(source)?,
        position: 0,
        depth: 0,
    };
    p.module()
}
struct Parser {
    tokens: Vec<Token>,
    position: usize,
    depth: usize,
}
impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.position]
    }
    fn at(&self, s: &str) -> bool {
        self.current().text == s
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.at(s) {
            self.position += 1;
            true
        } else {
            false
        }
    }
    fn need(&mut self, s: &str) -> Result<()> {
        if self.eat(s) {
            Ok(())
        } else {
            Err(error(self.current().span, format!("expected `{s}`")))
        }
    }
    fn name(&mut self) -> Result<(String, Span)> {
        let t = self.current().clone();
        if t.text
            .as_bytes()
            .first()
            .is_some_and(|b| b.is_ascii_alphabetic() || *b == b'_')
        {
            self.position += 1;
            Ok((t.text, t.span))
        } else {
            Err(error(t.span, "expected identifier"))
        }
    }
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= 64 {
            return Err(Error::new(
                "limit",
                self.current().span,
                "sized syntax nesting exceeds 64",
            ));
        }
        self.depth += 1;
        let r = f(self);
        self.depth -= 1;
        r
    }
    fn module(&mut self) -> Result<Module> {
        let mut imports = Vec::new();
        while self.eat("use") {
            let (mut path, start) = self.name()?;
            while self.eat("::") {
                path.push_str("::");
                path.push_str(&self.name()?.0);
            }
            let end = self.current().span;
            self.need(";")?;
            imports.push((path, Span::cover(start, end)));
        }
        let start = self.current().span;
        let public = self.eat("pub");
        let effect = match self.name()?.0.as_str() {
            "unitary" => Effect::Unitary,
            "iso" => Effect::Iso,
            "observe" => Effect::Observe,
            _ => {
                return Err(error(
                    start,
                    "expected ordinary unitary, iso or observe function",
                ));
            }
        };
        self.need("fn")?;
        let (name, _) = self.name()?;
        let mut parameters = Vec::new();
        if self.eat("[") {
            loop {
                self.need("static")?;
                let (name, _) = self.name()?;
                self.need(":")?;
                let param = if self.eat("Nat") {
                    Parameter::Natural(name)
                } else {
                    self.need("Op")?;
                    self.need("<")?;
                    let ty = self.basis()?;
                    self.need(">")?;
                    Parameter::Operation(name, ty)
                };
                parameters.push(param);
                if !self.eat(",") {
                    break;
                }
            }
            self.need("]")?;
        }
        self.need("(")?;
        let mut arguments = Vec::new();
        if !self.at(")") {
            loop {
                let (name, span) = self.name()?;
                self.need(":")?;
                arguments.push((name, self.ty()?, span));
                if !self.eat(",") || self.at(")") {
                    break;
                }
            }
        }
        self.need(")")?;
        self.need("->")?;
        let result = self.ty()?;
        let mut requires = Vec::new();
        if self.eat("requires") {
            loop {
                if matches!(
                    self.current().text.as_str(),
                    "Apply" | "Adjoint" | "Controlled"
                ) {
                    let (kind, span) = self.name()?;
                    self.need("(")?;
                    let (name, _) = self.name()?;
                    self.need(")")?;
                    requires.push(Requirement::Access(kind, name, span));
                } else {
                    requires.push(Requirement::Predicate(self.predicate()?));
                }
                if !self.eat(",") {
                    break;
                }
            }
        }
        let body = self.block(false)?;
        if !self.at("") {
            return Err(error(
                self.current().span,
                "this preparation profile permits one function per module",
            ));
        }
        let span = Span::cover(start, body.span);
        Ok(Module {
            imports,
            function: Function {
                name,
                public,
                effect,
                parameters,
                arguments,
                result,
                requires,
                body,
                span,
            },
        })
    }
    fn basis(&mut self) -> Result<Basis> {
        if self.eat("Bit") {
            Ok(Basis::Bit)
        } else {
            self.need("Bits")?;
            self.need("<")?;
            let n = self.natural()?;
            self.need(">")?;
            Ok(Basis::Bits(n))
        }
    }
    fn ty(&mut self) -> Result<Type> {
        self.nested(|p| {
            if p.eat("Q") {
                p.need("<")?;
                let b = p.basis()?;
                p.need(">")?;
                Ok(Type::Quantum(b))
            } else if p.eat("CBit") {
                Ok(Type::CBit)
            } else if p.eat("CBits") {
                p.need("<")?;
                let n = p.natural()?;
                p.need(">")?;
                Ok(Type::CBits(n))
            } else {
                p.need("(")?;
                let mut fields = Vec::new();
                if !p.at(")") {
                    loop {
                        fields.push(p.ty()?);
                        if fields.len() > 64 {
                            return Err(Error::new(
                                "limit",
                                p.current().span,
                                "tuple arity exceeds 64",
                            ));
                        }
                        if !p.eat(",") {
                            break;
                        }
                    }
                }
                p.need(")")?;
                if fields.len() == 1 {
                    return Err(error(
                        p.current().span,
                        "single-field tuple types are unsupported",
                    ));
                }
                Ok(Type::Tuple(fields))
            }
        })
    }
    fn natural(&mut self) -> Result<Natural> {
        let mut a = self.factor()?;
        while self.at("+") || self.at("-") {
            let sub = self.eat("-");
            if !sub {
                self.need("+")?;
            }
            let b = self.factor()?;
            let span = Span::cover(a.span, b.span);
            a = natural_node(
                if sub {
                    NatKind::Sub(Box::new(a), Box::new(b))
                } else {
                    NatKind::Add(Box::new(a), Box::new(b))
                },
                span,
            )?;
        }
        Ok(a)
    }
    fn factor(&mut self) -> Result<Natural> {
        let mut a = self.atom()?;
        while self.eat("*") {
            let b = self.atom()?;
            let span = Span::cover(a.span, b.span);
            a = natural_node(NatKind::Mul(Box::new(a), Box::new(b)), span)?;
        }
        Ok(a)
    }
    fn atom(&mut self) -> Result<Natural> {
        self.nested(|p| {
            let token = p.current().clone();
            if p.eat("(") {
                let n = p.natural()?;
                p.need(")")?;
                Ok(n)
            } else if token
                .text
                .as_bytes()
                .first()
                .is_some_and(u8::is_ascii_digit)
            {
                p.position += 1;
                let n = token
                    .text
                    .parse()
                    .map_err(|_| Error::new("limit", token.span, "natural literal exceeds i128"))?;
                natural_node(NatKind::Number(n), token.span)
            } else {
                let (name, span) = p.name()?;
                natural_node(NatKind::Name(name), span)
            }
        })
    }
    fn predicate(&mut self) -> Result<Predicate> {
        let left = self.natural()?;
        let comparison = match self.current().text.as_str() {
            "==" => Compare::Eq,
            "!=" => Compare::Ne,
            "<" => Compare::Lt,
            "<=" => Compare::Le,
            ">" => Compare::Gt,
            ">=" => Compare::Ge,
            _ => return Err(error(self.current().span, "expected static comparison")),
        };
        self.position += 1;
        Ok(Predicate {
            left,
            comparison,
            right: self.natural()?,
        })
    }
    fn argument(&mut self) -> Result<Argument> {
        self.nested(|p| {
            if p.eat("repeat_op") {
                let span = p.tokens[p.position - 1].span;
                p.need("(")?;
                let n = p.natural()?;
                let count = if p.eat("^") {
                    if !matches!(n.kind, NatKind::Number(2)) {
                        return Err(error(n.span, "only 2^e repetition counts are supported"));
                    }
                    Count::Power(p.atom()?)
                } else {
                    Count::Natural(n)
                };
                p.need(",")?;
                let child = p.argument()?;
                p.need(")")?;
                Ok(Argument::Repeat(count, Box::new(child), span))
            } else {
                let n = p.natural()?;
                if p.eat("[") {
                    let NatKind::Name(name) = n.kind else {
                        return Err(error(n.span, "only a function can have static arguments"));
                    };
                    let args = p.arguments_end("]")?;
                    Ok(Argument::Definition(name, args, n.span))
                } else {
                    Ok(Argument::Natural(n))
                }
            }
        })
    }
    fn arguments_end(&mut self, end: &str) -> Result<Vec<Argument>> {
        let mut args = Vec::new();
        if !self.at(end) {
            loop {
                args.push(self.argument()?);
                if !self.eat(",") {
                    break;
                }
            }
        }
        self.need(end)?;
        Ok(args)
    }
    fn pattern(&mut self) -> Result<Pattern> {
        self.nested(|p| {
            let start = p.current().span;
            if p.eat("(") {
                let mut fields = Vec::new();
                if !p.at(")") {
                    loop {
                        fields.push(p.pattern()?);
                        if fields.len() > 64 {
                            return Err(Error::new(
                                "limit",
                                p.current().span,
                                "tuple arity exceeds 64",
                            ));
                        }
                        if !p.eat(",") {
                            break;
                        }
                    }
                }
                let end = p.current().span;
                p.need(")")?;
                if fields.len() == 1 {
                    return Err(error(start, "single-field tuple patterns are unsupported"));
                }
                Ok(Pattern::Tuple(fields, Span::cover(start, end)))
            } else {
                let (n, s) = p.name()?;
                if n == "_" {
                    return Err(error(s, "implicit wildcard discard is unsupported"));
                }
                Ok(Pattern::Name(n, s))
            }
        })
    }
    fn runtime_arguments(&mut self) -> Result<Vec<Expr>> {
        self.need("(")?;
        let mut args = Vec::new();
        if !self.at(")") {
            loop {
                args.push(self.expr()?);
                if !self.eat(",") {
                    break;
                }
            }
        }
        self.need(")")?;
        Ok(args)
    }
    fn expr(&mut self) -> Result<Expr> {
        self.nested(Self::expr_inner)
    }
    fn expr_inner(&mut self) -> Result<Expr> {
        let start = self.current().span;
        let kind = if self.eat("if") {
            self.need("static")?;
            let predicate = self.predicate()?;
            let a = self.block(false)?;
            self.need("else")?;
            ExprKind::If(predicate, a, self.block(false)?)
        } else if self.eat("for") {
            self.need("static")?;
            let (index, _) = self.name()?;
            self.need("in")?;
            let start = self.natural()?;
            self.need("..")?;
            let end = self.natural()?;
            self.need("carry")?;
            let carry = self.pattern()?;
            self.need("=")?;
            let initial = Box::new(self.expr()?);
            let body = self.block(true)?;
            ExprKind::Fold {
                index,
                start,
                end,
                carry,
                initial,
                body,
            }
        } else if self.eat("adjoint") {
            self.need("(")?;
            let op = self.argument()?;
            self.need(",")?;
            let input = Box::new(self.expr()?);
            self.need(")")?;
            ExprKind::Adjoint(op, input)
        } else if self.eat("controlled") {
            self.need("(")?;
            let op = self.argument()?;
            self.need(")")?;
            ExprKind::Controlled(op, self.runtime_arguments()?)
        } else if self.eat("(") {
            let mut fields = Vec::new();
            if !self.at(")") {
                loop {
                    fields.push(self.expr()?);
                    if fields.len() > 64 {
                        return Err(Error::new(
                            "limit",
                            self.current().span,
                            "tuple arity exceeds 64",
                        ));
                    }
                    if !self.eat(",") {
                        break;
                    }
                }
            }
            self.need(")")?;
            if fields.len() == 1 {
                // Parentheses group an expression; a comma is required to
                // construct a tuple and singleton tuples are unsupported.
                let mut grouped = fields.pop().unwrap();
                grouped.span = Span::cover(start, self.tokens[self.position - 1].span);
                return Ok(grouped);
            }
            ExprKind::Tuple(fields)
        } else {
            let (name, _) = self.name()?;
            let args = if self.eat("[") {
                self.arguments_end("]")?
            } else {
                Vec::new()
            };
            if self.at("(") {
                ExprKind::Call(name, args, self.runtime_arguments()?)
            } else if args.is_empty() {
                ExprKind::Name(name)
            } else {
                return Err(error(
                    start,
                    "static function reference is not a runtime value",
                ));
            }
        };
        let end = self.tokens[self.position.saturating_sub(1)].span;
        Ok(Expr {
            kind,
            span: Span::cover(start, end),
        })
    }
    fn block(&mut self, fold: bool) -> Result<Block> {
        self.nested(|p| {
            let start = p.current().span;
            p.need("{")?;
            let mut statements = Vec::new();
            loop {
                if p.eat("let") {
                    let pattern = p.pattern()?;
                    p.need("=")?;
                    let value = p.expr()?;
                    p.need(";")?;
                    statements.push(Statement::Let(pattern, value));
                    continue;
                }
                let yielded = p.eat("yield");
                if yielded && !fold {
                    return Err(error(
                        p.current().span,
                        "yield is only valid in a static fold",
                    ));
                }
                let result = if p.at("}") {
                    Expr {
                        kind: ExprKind::Tuple(Vec::new()),
                        span: p.current().span,
                    }
                } else {
                    p.expr()?
                };
                if p.eat(";") && !yielded {
                    statements.push(Statement::Drop(result));
                    continue;
                }
                if fold && !yielded {
                    return Err(error(result.span, "static fold requires yield"));
                }
                let end = p.current().span;
                p.need("}")?;
                return Ok(Block {
                    statements,
                    result: Box::new(result),
                    span: Span::cover(start, end),
                });
            }
        })
    }
}
