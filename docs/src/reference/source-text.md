# Source text and lexical boundary

These rules govern the current `0.3.0-alpha` source scanner and parser in
constitutional edition 2026. Both finite project loading and sized explicit
module loading use one scanner, token stream, parser and source `Module`/`Span`
representation under the
[common frontend decision](https://github.com/MGYamada/Qleisli/issues/32).
The sized checker temporarily consumes an explicit projection of that AST; it
does not parse source again. Name resolution, type/static/owner/effect checking
and lowering are not yet unified. A parsed AST does not accept a program or
confer native verification evidence.

## Bytes, characters and positions

Source is UTF-8. Every source span is a half-open byte interval in the original
input. Source loading, scanning and diagnostics must not normalize those bytes.
LF and CRLF are accepted line endings. Ordinary whitespace is ASCII space or
tab; bare CR, vertical tab, form feed and non-ASCII whitespace reject. Bidi
control characters and other control characters reject, including in comments.
A rejected Unicode scalar's span covers its complete UTF-8 encoding.

Identifiers use ASCII letters or underscore initially, followed by ASCII
letters, digits or underscore. Comment prose may contain other ordinary Unicode
characters. This does not admit Unicode identifiers or alternate whitespace.

The existing finite keywords are reserved in the common grammar, including
identifier positions formerly treated contextually by the sized parser:
`use`, `meaning`, `static`, `Op`, `requires`, `Apply`, `Adjoint`, `Controlled`,
`permutation_by`, `phase_by`, `bind_op`, `inverse_op`, `then_op`, `tensor_op`,
`controlled_op`, `repeat_op`, `conjugate_op`, `pub`, `basis`, `iso`, `unitary`,
`observe`, `fn`, `let`, `if`, `else`, `do`, `pure`, `with_computed`,
`apply_contract`, `adjoint`, `repeat_static`, `qif`, `true`, `false`, `not`,
`xor`, `and`, `Unit`, `Bit`, `CBit` and `Q`. The existing import exception admits
`basis` and `observe` immediately after `std::` as module names.

`Bits`, `CBits` and `Nat` are contextual type/kind names and remain valid names
in identifier positions. `for static`, the `in`/`carry` parts of that header,
and `yield` at the start of a fold tail recognize their existing sized roles.
Those words remain identifiers in other positions. `controlled(op)(args)` is
the existing controlled-application construct; `controlled(q)` remains an
ordinary call to an identifier. Neither spelling guesses a resolved provider
category or grants control access.

Numeral tokens retain their decimal spelling. The scanner does not convert
them to a machine integer, infer a Bit/Nat category or grant a static value.
The common natural-expression parser rejects leading zeroes except `0` and
literals exceeding `i128`. It retains addition/subtraction, multiplication and
parentheses with source spans; multiplication binds more tightly than addition
or subtraction. Existing static checks still require nonnegative, bounded and
supported expressions. A power repetition count has the existing `2^e` form,
with compound exponents parenthesized; this is not general exponentiation in
the natural-expression language. The finite lowering profile still requires
literal `repeat_op` counts in 0 through 4096. Final canonical value/type syntax
remains subsequent work.

## Comments and documentation

`//` starts a line comment. `/* ... */` is a nested block comment. Unclosed
block comments reject. Character validation applies equally to code, ordinary
comments and documentation comments; comments cannot hide forbidden controls.

`//!` and `/*! ... */` are inner documentation comments. `///` and
`/** ... */` are outer documentation comments, except that `////`, `/***` and
`/**/` begin ordinary comments. Documentation text may normalize CRLF to LF in
its extracted metadata; source offsets continue to refer to the original bytes.

Classification and placement are shared. Outer docs must precede a function
or use item; inner docs belong to the module or the initial documentation area
of a function body. The common declaration attachment check rejects misplaced
docs before either profile checks source. Metadata remains descriptive and is
available through `parse_documented_module`; ordinary module loading may retain
only the syntax and original source. No profile may silently ignore invalid
placement.

## Punctuation and bounded scanning

The physical scanner recognizes individual punctuation marks. The common lexer
forms composite tokens only from immediately adjacent marks: whitespace and
comments never join them. For example, `::` is distinct from
`: /* comment */ :`. The token stream includes the existing sized arithmetic
and comparison marks; `==>` is `==` followed by `>`, not a valid alternative
arrow. The scanner/parser never retries another grammar or chooses a backend
based on the input.

The sized entry retains its limit of 10,000 non-EOF tokens and block-comment
depth 64. Comments and EOF do not consume the token allowance; the next excess
token is rejected before allocating its owned text. The finite entry retains
its existing iterative comment processing without a newly imposed depth limit.
Source-byte and aggregate project limits remain separate entry-point policies.
The common parser applies its 64-level recursive syntax and runtime/type tree
bounds, 64-field tuple bound and 128-depth natural-expression bound. This counts
the quantum wrapper and its basis parse in the same recursion budget; certain
deep sized natural types therefore reach the common limit one level earlier
than the removed parser. These are engineering limits, not the constitutional
quantitative Resource Safety theorem.

All declarations remain in the common AST. The sized profile currently rejects
a second declaration at that declaration's span, pending declaration identity
and same-module cycle checking. Existing empty sized type/pattern/block,
empty `yield`, empty specialization brackets and parameter trailing-comma
spellings are represented by the shared syntax. Unsupported finite constructs
receive a located profile rejection; parsing a spelling does not add backend
support. This implementation step does not select final canonical syntax or
add `Op<A,B>`/Basis-generic features.

## Migration and evidence

The old sized scanner skipped bare CR/form feed and forbidden characters inside
comments. Those inputs now reject. Replace noncanonical whitespace with ordinary
space/tab or LF/CRLF and remove forbidden controls. VT already rejected before
this change; its diagnostic now comes from the shared character rule.

Reserved-word identifiers in old sized source must be renamed. Misplaced docs
must move to their module/declaration attachment boundary. Unclosed block
comments now use the common `unterminated block comment` diagnostic. The former
one-function parse error is now a profile restriction after the complete Module
is parsed; no additional recursion becomes valid. Edition remains 2026 because
edition names the constitutional regime, while release compatibility records
these source changes.

`tests/fixtures/frontend_v030/shared-scanner/` in the
[repository](https://github.com/MGYamada/Qleisli) preserves the original byte
fixtures and actual old/new CLI diagnostics. The two successful small source
pairs emitted identical untrusted proposal hashes. The subsequent
`tests/fixtures/frontend_v030/common-parser/` packet preserves ten initial
source observations, independent review counterexamples, exact commands/results
and four small before/after proposals with identical bytes. It also records the
shared-depth edge above. These are bounded migration evidence, not a general
source-preservation proof, new formal guarantee or native acceptance claim.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
