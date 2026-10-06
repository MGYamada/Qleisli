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

const MAX_IMPORT_DOC_COPIES: usize = 65_536;
const MAX_IMPORT_DOC_BYTES: usize = 1_048_576;

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
    let mut imports: BTreeMap<_, Vec<usize>> = BTreeMap::new();
    for (index, item) in syntax.uses.iter().enumerate() {
        imports.entry(item.span.start).or_default().push(index);
    }
    let bodies: BTreeMap<_, _> = syntax
        .decls
        .iter()
        .enumerate()
        .filter_map(|(index, decl)| {
            let start = match &decl.body {
                super::ast::FnBody::Natural(body) => {
                    let opening = tokens
                        .partition_point(|token| token.span.start < body.span.start)
                        .saturating_sub(1);
                    debug_assert!(matches!(tokens[opening].kind, TokenKind::LBrace));
                    return Some((opening, index));
                }
                super::ast::FnBody::Meaning { .. } => return None,
                super::ast::FnBody::Quantum(body) => body.span.start,
                super::ast::FnBody::Basis(_) => decl.return_type.span.end,
            };
            let opening = tokens.partition_point(|token| token.span.start < start);
            debug_assert!(matches!(tokens[opening].kind, TokenKind::LBrace));
            Some((opening, index))
        })
        .collect();
    let mut result = DocumentedModule {
        declaration_docs: vec![vec![]; syntax.decls.len()],
        import_docs: vec![vec![]; syntax.uses.len()],
        syntax,
        module_docs: vec![],
    };
    let mut seen_outer = false;
    let mut remaining_import_doc_copies = MAX_IMPORT_DOC_COPIES;
    let mut remaining_import_doc_bytes = MAX_IMPORT_DOC_BYTES;
    for comment in comments {
        let next = tokens.partition_point(|token| token.span.start < comment.span.end);
        match comment.style {
            DocStyle::Outer => {
                seen_outer = true;
                let position = tokens[next].span.start;
                if let Some(&index) = declarations.get(&position) {
                    result.declaration_docs[index].push(comment);
                } else if let Some(indices) = imports.get(&position) {
                    // Move the original comment once; bound the extra copies
                    // introduced by grouping before cloning any of its text.
                    let (&first, rest) = indices.split_first().expect("nonempty import group");
                    remaining_import_doc_copies = remaining_import_doc_copies
                        .checked_sub(rest.len())
                        .ok_or_else(|| ParseError {
                            message: "grouped import documentation exceeds the 65536 comment copies limit".into(),
                            span: comment.span,
                        })?;
                    remaining_import_doc_bytes = comment.text.len()
                        .checked_mul(rest.len())
                        .and_then(|bytes| remaining_import_doc_bytes.checked_sub(bytes))
                        .ok_or_else(|| ParseError {
                            message: "grouped import documentation exceeds the 1048576 copied comment bytes limit".into(),
                            span: comment.span,
                        })?;
                    for &index in rest {
                        result.import_docs[index].push(comment.clone());
                    }
                    result.import_docs[first].push(comment);
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
    render(source, false, |_| None)
}

/// Only immutable source-checking results call this renderer with their own
/// retained bytes and facts. The public source-only renderer cannot assert them.
pub(super) fn render_checked_markdown(
    source: &str,
    effect: impl Fn(&str) -> Option<super::effects::FunctionEffect>,
) -> Result<String, ParseError> {
    render(source, true, effect)
}

fn render(
    source: &str,
    checked: bool,
    effect: impl Fn(&str) -> Option<super::effects::FunctionEffect>,
) -> Result<String, ParseError> {
    let documented = parse_documented_module(source)?;
    let mut output = String::from(if checked {
        "# Module documentation\n\nChecked source interface; effects are inferred from typed bodies. This metadata does not establish exact Meaning, access evidence, source preservation or constitutional discharge.\n\n"
    } else {
        "# Module documentation\n\nSource documentation only; no type, ownership or contract verification is implied.\n\n"
    });
    render_comments(&mut output, &documented.module_docs);
    let mut last_import_span = None;
    for (item, docs) in documented.syntax.uses.iter().zip(&documented.import_docs) {
        if !docs.is_empty() && last_import_span != Some(item.span) {
            output.push_str("## Import\n\n");
            render_source(&mut output, &source[item.span.start..item.span.end]);
            render_comments(&mut output, docs);
            last_import_span = Some(item.span);
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
        let end = match &decl.body {
            super::ast::FnBody::Meaning { .. } => decl.span.end,
            super::ast::FnBody::Quantum(body) if !decl.requires.is_empty() => body.span.start,
            _ => decl.return_type.span.end,
        };
        render_source(&mut output, source[decl.span.start..end].trim_end());
        if let Some(fact) = effect(&decl.name.text) {
            output.push_str(&format!(
                "Inferred quantum effect: `{:?}`.\n\n",
                fact.inferred()
            ));
            if let Some(asserted) = fact.asserted() {
                output.push_str(&format!(
                    "Checked upper-bound assertion: `{asserted:?}`.\n\n"
                ));
            }
        }
        render_comments(&mut output, docs);
    }
    Ok(output)
}

fn render_comments(output: &mut String, comments: &[DocComment]) {
    let mut text = String::new();
    for comment in comments {
        for line in comment.text.split('\n') {
            text.push_str(line.strip_prefix(' ').unwrap_or(line));
            text.push('\n');
        }
    }
    if !comments.is_empty() {
        // Comments are descriptive text, not trusted Markdown/HTML. A fence
        // longer than every embedded backtick run isolates all block syntax,
        // including unfinished fences, HTML comments and raw HTML elements.
        render_fenced(output, text.trim_end_matches('\n'), "text");
    }
}

fn render_source(output: &mut String, source: &str) {
    render_fenced(output, source, "qli");
}

fn render_fenced(output: &mut String, source: &str, language: &str) {
    // A signature may contain ordinary comments with Markdown fence text.
    let longest = source
        .split(|ch| ch != '`')
        .map(str::len)
        .max()
        .unwrap_or(0);
    let fence = "`".repeat(3.max(longest + 1));
    output.push_str(&format!("{fence}{language}\n{source}\n{fence}\n\n"));
}
