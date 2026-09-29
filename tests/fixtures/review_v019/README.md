# v0.1.9 review reproductions

These local negative/performance fixtures are Apache-2.0 project material, not
a fourth external input source or a controlled model benchmark.

The sources were saved before the review repairs. [baseline.json](baseline.json)
records actual pre-repair debug-binary observations on the 0.2.0 development
tree, with each source's SHA-256. It is not a rerun of a published 0.1.9 release
binary. [after.json](after.json) records the same files and commands after the
repairs. Preserve the source bytes, especially the CR in
[bare_cr/main.qli](bare_cr/main.qli).

- Bare CR: the old lexer hid `x`, yielding `0` with probability one. The new
  lexer rejects at the original CR byte. Converting it to CRLF makes `x`
  executable and yields `1`; the regression checks both outcomes.
- Static work: [static_budget/main.qli](static_budget/main.qli) passes an unused
  five-bit operation with two nested repetitions of 150. The observed check
  fell from 12.333 seconds to 0.892 seconds after repeated squaring, with the
  same accepted result. These are single local debug observations, without
  process isolation; they are neither a timing guarantee nor the reviewer's
  unexecuted three-hour estimate.

[The integration regressions](../../review_v019.rs) additionally test all CR
contexts/offsets and shared exact work across unused static arguments. Semantic
mutation and logarithmic-work tests live in
[the operation module](../../../src/frontend/compile/operations.rs).
