# Terminal documentation and policy results

Root ran the reviewed thirteen-command policy wrapper after both Rust runs,
the forty-case comparison, metadata review and independent result audit had
terminal records. The frozen input map is
[reviewed-inputs.json](policy-validation/reviewed-inputs.json), SHA-256
`8e067dc5774423707fc603cae104d187c26e97a5261585fab39115128d76894d`.
It contains 1,147 declared inputs, including the independent audit, and is
explicitly incomplete for fixtures, system/build/runtime dependencies.

The actual process returned exit zero (tool session 87137, terminal chunk
`a24db9`). [Results](policy-validation/attempt-01/results.json),
[literal command records](policy-validation/attempt-01/commands.json) and raw
stdout/stderr retain all thirteen successful exits without launch or timeout
errors. Before/after declared inputs and selected binaries are unchanged.
The regression counts are 12 book, 7 authoring, 11 edition and 36 docs tests:
**66 passed**. These are derived from their actual outputs.

The selected mdBook reported exactly `mdbook v0.5.4`. Its rendered book has
23 HTML files, 920 checked local links and 343 checked anchors. The generated
HTML/assets total 3,858,305 bytes; their
[map](policy-validation/attempt-01/rendered-files.json) was saved before the
wrapper removed only its owned temporary book tree. External URL targets
were not fetched. The constitutional check used reviewed base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; the 254-source inventory and
production coverage checks also returned zero.

The [main results](results.md) and independent
[implementation review](independent-implementation-review-by-docs-01/review.md)
and [result audit](independent-validation-audit-by-cli-01/review.md) remain
separate. The first formatting failure and manual count correction remain
preserved. Each Rust run has 147 passes, zero failures and three existing
ignores, with two additional explicit project stress skips. The forty-case
comparison has six successes, 34 source refusals and 46 forwarded attempts;
the journal does not independently attest native starts or exits.

This policy run built no Rust/Lean program and executed no CLI/native replay.
It is not full CI or an exact-commit release validation. Complete original-AST
checking, canonical std/QFT, source/runtime preservation and general family or
resource proofs remain unfinished. No constitutional interpretation, guarantee,
Issue acceptance criterion or completion status changes. The selected scope
remains **111 Issues, 14 complete (12.61%), 97 remaining**; #317 remains open
with all 24 criteria unchecked.

This additive result was written after the frozen policy attempt completed;
it was not one of that attempt's inputs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
