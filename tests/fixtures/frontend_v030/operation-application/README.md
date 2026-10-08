# Canonical QPE operation application

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This bounded #33 migration follows commit
`5d4c50ac2a0f6da47bbbc990385fa3027e210153`. The source map retains that
commit's current `const`-header source and selects a complete successor.
Only `repeat_op(2^k,U)` becomes `power(U,2^k)` and
`adjoint(fourier[m],phase)` becomes `inverse(fourier[m])(phase)`.
The quantum fold, provider, interface, axes and phases remain unchanged.
The generic QFT sources are unchanged and their implementation remains excluded.

The repository selection test checks these exact changes. Missing stages and
stale destination bytes reject. The independent Python proposal parser
understands the canonical spellings and retains historical parsing for frozen
comparisons. Ordinary declarations named `inverse` or `power` still resolve;
count limits and unknown-provider refusals remain in force.

`experiment.json` records equality of parsed QPE and three small proposals
at `(n,m) = (1,1), (1,2), (2,2)`. A Rust-generated three-qubit proposal agrees
with the independent complex oracle on all eight basis columns, with maximum
error below `4e-16`. Public source checking with the actual native checker
succeeded, retaining its producer-consistency disclosure. These checks do not
prove general source preservation, certify the algorithm, or discharge QS/PR/RS.

The first independent-parser refusal is retained in `first-refusal.txt`.
Two initial CLI mistakes (obsolete command/argument names and a missing explicit
edition manifest) are preserved in the experiment record. The corrected command
uses the actual public CLI and schema-2 edition-2026 manifest.

Migration also exposed stale source-mutation needles in the QPE and client
negative tests. Their failures are retained. Current mutation needles now use
canonical forms and reject a missing match, preserving power-order, sign,
zero-power, count/access and dependent-client counterexamples. None was deleted.

Selection tests passed 53 cases, parser/guard tests passed 22, related Rust
targets passed 45 cases on latest and MSRV, and both native CLI tests were run
explicitly on each toolchain. Five bounded Python/native/oracle checks passed;
the shared source-integrity group passed all five commands and docs passed.
The unchanged 4,000-case ownership suite and full CI are not claimed here.
No Lean executable definition or admitted constitutional evidence was changed.
