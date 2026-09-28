# Comments and documentation in `.qli`

Status: **implemented extension specification; validation recorded separately**
(2026-09-28). The user requested Rust-style comments/documentation and explicitly
kept the product version at **0.1.6** after the MINOR requirement was explained.
This is a recorded exception for this extension, not a reclassification of new
features as routine PATCH maintenance. Other version-policy rules remain intact.

## Lexical forms and attachment

Follow the [Rust Reference's comment distinctions](https://doc.rust-lang.org/reference/comments.html)
for the spellings below. `.qli` does not implement Rust attributes, item syntax,
rustdoc link resolution, doctest execution or the complete Rust language.

| Spelling | Role in `.qli` |
| --- | --- |
| `// text` | Ordinary comment, ending at LF or end of file. |
| `/* text */` | Ordinary block comment; blocks nest. |
| `/// text` | Outer documentation for the following function or `use` item. |
| `/** text */` | Outer block documentation with the same attachment rule. |
| `//! text` | Inner documentation for the containing file/module or function. |
| `/*! text */` | Inner block documentation with the same attachment rule. |

Exactly three initial slashes mark outer line documentation; `////` is ordinary
comment text. `/**/`, `/***/` and blocks starting `/***` are ordinary comments.
All block forms nest, but only the outermost comment creates a documentation
entry; nested markers remain text inside it. Delimiters inside Markdown or
quoted prose still delimit comments. Unclosed blocks are lexical errors.

Module inner documentation precedes every `use`, declaration and outer doc
comment. Function inner documentation appears immediately after its opening
brace, before any body expression/statement; it documents that function and
follows its outer documentation. Ordinary comments/whitespace may intervene.
Outer documentation must precede a supported top-level item, including its
`pub` if present. Consecutive comments attach in source order. Orphan outer
docs, inner docs after an item/body expression, docs in a parameter list and
docs on local statements/expressions are errors. `.qli` has no nested module
items or general attributes; inner docs on arbitrary expression blocks are
outside this profile.

Examples:

```qli
//! Operations on basis labels; no quantum ownership is created.

/// Return the input basis label unchanged.
pub basis fn identity(x: Bit) -> Bit {
    /*! This inner documentation belongs to identity. */
    /* Ordinary /* nested */ comment. */
    x
}
```

```text
/// orphan at end of file                         -> reject
pub basis fn f(x: Bit) -> Bit { x } //! too late  -> reject
pub basis fn f(x: Bit) -> Bit { /// local
    x }                                         -> reject
/* unfinished                                   -> reject
```

CRLF is retained in source spans and normalized to LF in extracted doc text.
A bare CR is forbidden in doc comments. Ordinary line comments end only at LF,
so bare CR no longer terminates them. The existing `.qli` forbidden-character
policy still applies inside all comments; this is stricter than adopting all
Rust Unicode/source preprocessing rules. Spans are original UTF-8 byte ranges,
including comment delimiters, excluding line terminators for line comments.
Preserve doc contents after removing only their delimiters and normalizing
CRLF; Markdown layout is a presentation responsibility.

Block scanning is iterative, with work proportional to source length; nested
comments do not consume the recursive expression parser's stack/depth budget.
Existing expression limits are unchanged. This adds no new global source-byte
limit and makes no claim of unbounded practical memory availability.

## Public data and command

`frontend::parser::parse_module` keeps returning the existing `ast::Module`.
Existing public AST fields and public lexer token variants stay unchanged.
Both parsing entry points validate doc attachment; `lexer::lex` returns only
ordinary syntax tokens after checking comments lexically.

`frontend::parser::parse_documented_module` returns a
`frontend::documentation::DocumentedModule` containing `syntax`, `module_docs`,
`declaration_docs` and `import_docs`. The last two vectors align one-for-one
with `syntax.decls` and `syntax.uses`; an undocumented item has an empty vector.
Each `DocComment` contains `style` (`DocStyle::Outer` or `Inner`), `text` and
`span`. These are descriptive data, never checked quantum evidence.

`frontend::documentation::render_markdown(source)` parses one source file and
returns Markdown or a located `ParseError`. Include module text, import docs
and all function signatures/docs, marking public/private visibility. Strip one
conventional leading space on each displayed comment line; do not execute
examples or resolve links. Preserve raw extracted text in the data API.

`qleisli doc <source-file>` reads one UTF-8 `.qli` file and writes this Markdown
to stdout. It does not resolve imports, check types/ownership/contracts, run a
program or write files. Output states that it is source documentation, not a
verification result. Exit codes are 0 on success, 1 on I/O/parsing failure and
2 on command usage errors; diagnostics go to stderr. `check` and `run` continue
to accept source-root directories with their existing verification behavior.

## Trust, migration and library coverage

Comments/docstrings are lexical documentation metadata, not sealed operations,
ordinary executable definitions, type/effect annotations or proof declarations.
They carry no ownership/effect and emit no IR. Claims such as “unitary”, “clean”
or “verified” inside prose cannot bypass the same source and IR checks applied
to user code. Changing comment text can change source snapshots used to identify
function evidence; it does not permit reusing stale snapshots as authority.

Existing code using `///`, `//!` or doc-block spellings as arbitrary ordinary
comments must put them in valid documentation positions or replace them with
`//`, `////` or ordinary `/* ... */`. Convert bare-CR line endings to LF/CRLF.
No existing AST construction needs new fields, and ordinary `//` text remains
valid subject to the clarified line-ending rule. There is no string-expression
docstring syntax, Markdown execution, automatic contract verification or new
stdlib operation in this extension.

For example, `//! implementation note` after a statement must become
`// implementation note`; a function's public description belongs in `///`
comments before its declaration. An orphan `/// note` at end of file must
be moved to its item or changed to an ordinary comment. No executable code
change is needed for these migrations.

All four bundled `.qli` files receive module documentation and every one of
their twelve public and three private definitions receives a docstring. Public
contracts remain those in the [stdlib ledger](stdlib-contracts.md); prose
summarizes types, phase, bit order, ownership/effects and assumptions without
granting extra trust or claiming unproved general correctness.
