# Comments and documentation in .qli

Implemented 0.1.6 extension; current English contract. Comments carry no effects,
ownership, IR or evidence, and may change source-identity snapshots. Claims in prose
never bypass source/IR checks. [QLT #50](https://github.com/MGYamada/Qleisli/issues/50)
is future v0.4+ external test tooling; current fences are text only.

## Lexical forms and attachment

// ends at LF/EOF; /* */ nests. /// and /** */ are outer docs for the next function/use
(including pub); //! and /*! */ are inner module/function docs. Exactly three slashes
mark outer docs: //// is ordinary. /**/, /***/ and /*** prefixes are ordinary blocks.
All blocks nest, only outermost creates a doc entry; nested markers remain text.
Markdown/quoted delimiters still delimit comments; unclosed blocks reject.

Module inner docs precede every item/outer doc. Function inner docs immediately
follow its opening brace before statements/expressions, after its outer docs.
Ordinary whitespace/comments may intervene; consecutive docs attach in source order.
Orphans, late inner docs, parameter/local-expression docs and arbitrary-block inner
docs reject. No nested modules/attributes or string docstrings are implemented.

```qli
//! Operations on basis labels; no quantum ownership is created.
/// Return the input basis label unchanged.
pub basis fn identity(x: Bit) -> Bit {
    /*! This inner documentation belongs to identity. */
    /* Ordinary /* nested */ comment. */
    x
}
```

Original half-open UTF-8 spans include delimiters, exclude line endings for line docs.
Retain text after delimiter removal and normalize CRLF to LF in extracted text only.
Bare CR/forbidden source characters reject inside every comment too; LF/CRLF valid.
Iterative block scanning is source-linear and does not consume expression recursion;
existing expression and separate source-byte limits remain.

## Public data and command

parse_module retains ast::Module; lexer tokens/public AST fields unchanged. Both parser
entry points check attachment; lex validates comments and returns syntax tokens only.
parse_documented_module returns DocumentedModule{syntax,module_docs,declaration_docs,
import_docs}; last vectors align one-for-one with decls/uses, undocumented slots empty.
DocComment has Outer/Inner style, raw text and span, no checked authority.

render_markdown(source) parses one file or returns located ParseError, displays module/
import docs and every function signature with visibility. Strip one conventional
leading display space, keep raw text in data; no link resolution/example execution.
qleisli doc <file> (no --qrate) reads UTF-8 and writes Markdown stating source-documentation scope;
no imports/type/ownership/contract checking, execution or file writes. Exits0/1/2 for
success/read-parse/usage, errors on stderr. check/run retain their existing directory
interfaces; --format=json is unsupported for doc.

## Trust, migration and library coverage

Old arbitrary /// or //! text must move to valid attachment or become ordinary
//, //// or /* */. Convert bare CR to LF/CRLF; no executable/AST change is needed.
Bundled four files have module docs and twelve public/three private docstrings.
[Ledger](stdlib-contracts.md) remains the contract authority; extraction/rendering
provides no automatic correctness, doctests, Rust attributes or full rustdoc semantics.
