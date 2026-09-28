//! Source documentation is descriptive metadata, never quantum evidence.

use super::ast::{Module, Span};
use super::lexer::{Token, TokenKind};
use super::parser::{ParseError, parse_documented_module};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DocStyle {
    Outer,
    Inner,
}

/// Text excludes delimiters, with CRLF normalized to LF. The span retains
/// original UTF-8 byte positions and includes the comment delimiters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocComment {
    pub style: DocStyle,
    pub text: String,
    pub span: Span,
}

/// Sidecar documentation preserves the existing public syntax-tree shape.
/// Item vectors align with `syntax.decls` and `syntax.uses`, respectively.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocumentedModule {
    pub syntax: Module,
    pub module_docs: Vec<DocComment>,
    pub declaration_docs: Vec<Vec<DocComment>>,
    pub import_docs: Vec<Vec<DocComment>>,
}

pub(crate) fn attach(
    syntax: Module,
    tokens: &[Token],
    comments: Vec<DocComment>,
) -> Result<DocumentedModule, ParseError> {
    use std::collections::BTreeMap;

    let declarations: BTreeMap<_, _> = syntax
        .decls
        .iter()
        .enumerate()
        .map(|(index, decl)| (decl.span.start, index))
        .collect();
    let imports: BTreeMap<_, _> = syntax
        .uses
        .iter()
        .enumerate()
        .map(|(index, item)| (item.span.start, index))
        .collect();
    let bodies: BTreeMap<_, _> = syntax
        .decls
        .iter()
        .enumerate()
        .map(|(index, decl)| {
            let opening =
                tokens.partition_point(|token| token.span.start < decl.return_type.span.end);
            debug_assert!(matches!(tokens[opening].kind, TokenKind::LBrace));
            (opening, index)
        })
        .collect();
    let mut result = DocumentedModule {
        declaration_docs: vec![vec![]; syntax.decls.len()],
        import_docs: vec![vec![]; syntax.uses.len()],
        syntax,
        module_docs: vec![],
    };
    let mut seen_outer = false;
    for comment in comments {
        let next = tokens.partition_point(|token| token.span.start < comment.span.end);
        match comment.style {
            DocStyle::Outer => {
                seen_outer = true;
                let position = tokens[next].span.start;
                if let Some(&index) = declarations.get(&position) {
                    result.declaration_docs[index].push(comment);
                } else if let Some(&index) = imports.get(&position) {
                    result.import_docs[index].push(comment);
                } else {
                    return Err(ParseError {
                        message: "outer documentation must precede a function or use item".into(),
                        span: comment.span,
                    });
                }
            }
            DocStyle::Inner => {
                if next == 0 && !seen_outer {
                    result.module_docs.push(comment);
                } else if let Some(&index) = next
                    .checked_sub(1)
                    .and_then(|previous| bodies.get(&previous))
                {
                    result.declaration_docs[index].push(comment);
                } else {
                    return Err(ParseError {
                        message: "inner documentation must start a module or function body".into(),
                        span: comment.span,
                    });
                }
            }
        }
    }
    Ok(result)
}

/// Render a parsed source file, including private functions. This does not
/// resolve names, verify contracts, execute examples or establish correctness.
pub fn render_markdown(source: &str) -> Result<String, ParseError> {
    let documented = parse_documented_module(source)?;
    let mut output = String::from(
        "# Module documentation\n\nSource documentation only; no type, ownership or contract verification is implied.\n\n",
    );
    render_comments(&mut output, &documented.module_docs);
    for (item, docs) in documented.syntax.uses.iter().zip(&documented.import_docs) {
        if !docs.is_empty() {
            output.push_str("## Import\n\n");
            render_source(&mut output, &source[item.span.start..item.span.end]);
            render_comments(&mut output, docs);
        }
    }
    for (decl, docs) in documented
        .syntax
        .decls
        .iter()
        .zip(&documented.declaration_docs)
    {
        output.push_str(&format!(
            "## {} ({})\n\n",
            decl.name.text,
            if decl.public { "public" } else { "private" }
        ));
        render_source(
            &mut output,
            &source[decl.span.start..decl.return_type.span.end],
        );
        render_comments(&mut output, docs);
    }
    Ok(output)
}

fn render_comments(output: &mut String, comments: &[DocComment]) {
    for comment in comments {
        for line in comment.text.split('\n') {
            output.push_str(line.strip_prefix(' ').unwrap_or(line));
            output.push('\n');
        }
    }
    if !comments.is_empty() {
        output.push('\n');
    }
}

fn render_source(output: &mut String, source: &str) {
    // A signature may contain ordinary comments with Markdown fence text.
    let longest = source
        .split(|ch| ch != '`')
        .map(str::len)
        .max()
        .unwrap_or(0);
    let fence = "`".repeat(3.max(longest + 1));
    output.push_str(&format!("{fence}qli\n{source}\n{fence}\n\n"));
}
