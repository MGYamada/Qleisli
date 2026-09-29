# Bind actual shared-gradient subgraphs

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Continue the concrete shared-QFT producer, not a second standalone algorithm
model. Inspect actual definition indices for the recursive empty identity and
split-high-bit / tensor(phase, recursive child) / rejoin pattern. Bind every
body, scalar, ordered child, complete interface and actual routing map. Local
owner/axis labels must not be hard-coded. Reuse the complete-artifact typing
context and charge the caller's remaining structural budget; never reset it.

Prove that successful inspection characterizes the actual child operator's
complete diagonal, with no assumed whole-graph environment and no supplied
matrix receipt. Retain the empty owner at width zero. Relate the diagonal to
the independently defined low-axis-first integer phase, so the existing
controlled-gradient theorem can consume the result. Prove both actual body
binding and the semantic implication, including arbitrary reference amplitudes.

Test actual producer graphs at every precision 1–8, independent owner/axis
renaming, changed child references, order, counts, phase, routing and empty
ownership, and insufficient shared budgets. Keep the first source before
checking and real failure records. No external schema is enabled until the
complete QFT root, finite H equations and Fourier theorem are also connected.

## Completed component checkpoint

The bounded actual-body inspector, constructive complex diagonal theorem,
reference columns and direct/repeated-control bridges are implemented and
proved. [Final native evidence](gradient-binding-native.json) passes 175 cases
and 574 numerical vectors; [registry/build/audit evidence](gradient-binding-registry.json)
and [runtime regressions](gradient-binding-runtime-validation.json) pass.
The compiled-declaration policy caught a generated partial helper; explicit
`Nat.rec` removed it without an exception. The full outer QFT/H/Fourier binding
and external production/source/corpus gates remain separate, open work.
