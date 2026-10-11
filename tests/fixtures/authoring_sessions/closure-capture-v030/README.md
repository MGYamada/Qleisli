# Unsupported unrestricted closure capture

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed maintenance study preserves four complete first sources and
actual CLI JSON observations before and after the diagnostic change under #89.
No external model was invoked; this is not a blind authoring benchmark.
The first sources and edition manifest have unchanged recorded hashes.

Before the change, all three closure candidates fail at the first pipe with a
parser diagnostic. After the change, the genuine `Q<Bit>` capture fails with
`ownership` at the resolved outer `q` use. The ordinary `Bit` named `q` and
the parameter that shadows an outer `Q<Bit>` fail with `unsupported` instead.
The explicit first-order H H control passes both checks. These are source
checks, not execution observations or a source-preservation proof.

Separate regression tests exercise both public source paths, original Unicode
and CRLF locations, nested and zero-width owners, consumed bindings, nested
closures, typed parameters and return annotations, block-local shadowing and
existing parser depth/arity limits. An annotation grants no ownership fact.
All runtime closure values remain unsupported; no closure can lower to IR or
obtain native acceptance. Static operation descriptions and scoped
`with_computed` bodies retain their separate contracts.

The session records actual commands, times, executable hashes and diagnostics.
Executable identity does not attest build provenance. The first observations
are retained rather than regenerated, and no new constitutional discharge is
claimed.
