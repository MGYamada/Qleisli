# Source text and lexical boundary

These rules govern the current `0.3.0-alpha` source scanner in constitutional
edition 2026. They apply to both finite and sized entry points. The
[shared lexical decision](https://github.com/MGYamada/Qleisli/issues/32) is one
step toward the common frontend; the two parsers and their temporary token
adapters still exist. Recognizing a token does not accept a program or confer
native verification evidence.

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

Numeral tokens retain their decimal spelling. The scanner does not convert
them to a machine integer, infer a Bit/Nat category or grant a static value.
The parser and static checks apply canonical spelling, value and work limits.
The current sized adapter rejects leading zeroes except the numeral `0`.
The finite token API retains the spelling and its permitted use checks it.
Canonical shared value syntax is a subsequent language-migration step.

## Comments and documentation

`//` starts a line comment. `/* ... */` is a nested block comment. Unclosed
block comments reject. Character validation applies equally to code, ordinary
comments and documentation comments; comments cannot hide forbidden controls.

`//!` and `/*! ... */` are inner documentation comments. `///` and
`/** ... */` are outer documentation comments, except that `////`, `/***` and
`/**/` begin ordinary comments. Documentation text may normalize CRLF to LF in
its extracted metadata; source offsets continue to refer to the original bytes.

Classification is shared. Placement and attachment are currently checked by
the finite parser against its declarations. The sized parser still discards
documentation metadata. It therefore does not yet enforce the same attachment
rules; common AST/parser integration must remove this difference.

## Punctuation and bounded scanning

The physical scanner recognizes individual punctuation marks. Temporary token
adapters form their existing composite tokens only from immediately adjacent
marks: whitespace and comments never join them. For example, `::` is distinct
from `: /* comment */ :`. The scanner never retries a different grammar or
chooses a backend based on the input.

The sized entry retains its limit of 10,000 non-EOF tokens and block-comment
depth 64. Comments and EOF do not consume the token allowance; the next excess
token is rejected before allocating its owned text. The finite entry retains
its existing iterative comment processing without a newly imposed depth limit.
Source-byte and aggregate project limits remain separate entry-point policies.
These are engineering work limits, not the constitutional quantitative Resource
Safety theorem.

## Migration and evidence

The old sized scanner skipped bare CR/form feed and forbidden characters inside
comments. Those inputs now reject. Replace noncanonical whitespace with ordinary
space/tab or LF/CRLF and remove forbidden controls. VT already rejected before
this change; its diagnostic now comes from the shared character rule.

`tests/fixtures/frontend_v030/shared-scanner/` in the
[repository](https://github.com/MGYamada/Qleisli) preserves the original byte
fixtures and actual old/new CLI diagnostics. The two successful small source
pairs emitted identical untrusted proposal hashes. This is bounded migration
evidence, not a source-preservation proof or native acceptance claim.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
