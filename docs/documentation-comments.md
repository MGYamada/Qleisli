# Comments and documentation in .qli

English implemented syntax metadata, no effect/owner/IR/evidence; prose never authorizes acceptance, comments may change source binding. QLT>=0.4 remains future, fences text only.

## Lexical forms and attachment

// LF/EOF, /* */ nested. /// and /** */ outer next function/use (including pub); //! and /*! */ inner module/function. ////,/**/,/***/,/*** ordinary. Only outermost block creates doc; nested markers text, quoted/Markdown delimiters still close comments, unclosed reject. Module inner before all items/outer docs, function inner immediately after `{` before statements. Ordinary comments/space may intervene, docs source order. Orphan/late/parameter/local/arbitrary-block docs reject. Original half-open UTF-8 spans include delimiters/exclude line LF; strip delimiters/normalize CRLF in text only, forbidden characters/bare CR reject. Iterative scan source-linear/separate depth/byte limits.

## Public data and command

parse_module keeps public AST/tokens; both parser entries validate attachment, lex returns syntax tokens only. parse_documented_module -> DocumentedModule{syntax,module_docs,declaration_docs,import_docs}, aligned vectors/empty undocumented slots. DocComment Outer/Inner,text,span/no seal. render_markdown parses or located ParseError, displays module/import docs/all signatures+visibility, strips one display space only, no link/example execution. `qleisli doc FILE` UTF-8->Markdown, no --qrate/JSON/import/check/execute/file write; exits0/1/2,error stderr.

## Trust, migration and library coverage

Move formerly arbitrary doc text to valid attachment or ordinary comment; bare CR->LF/CRLF. Four bundled files/twelve public/three private docstrings; [ledger](stdlib-contracts.md) authority, no automatic doctest/evidence/rustdoc guarantee.
