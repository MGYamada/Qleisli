# v0.2.2 review repairs in development v0.2.3

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The review reproductions remain executable regressions:

- [Interop stdin race](../../connections.rs): file invocations leave stdin
  unused; early usage rejection may close a pipe.
- [Capture diagnostics](../../with_computed_diagnostics.rs): hidden outer
  bindings and genuinely consumed owners receive distinct errors.
- [Finite/sized ownership comparison](../../frontend_ownership_differential.rs):
  4,000 deterministic common-subset programs, at most three qubits.
- [Rust/Python dialect comparison](../../sized_review_dialects.rs): generic
  obligations, static comparisons, GHZ and arithmetic providers. Concrete
  Python acceptance and generic Rust acceptance have explicit scopes.
- [Profile and native-failure diagnostics](../../sized_review_diagnostics.rs):
  error-only process injection preserves codes and identifies checking scope.
- [Delayed QFT source](../sized_clients/delayed_fourier.qli) and
  [root/inverse regressions](../../sized_source.rs): equivalent commuting
  schedules retain phase, axes, source endpoints and the original precursor.
  [Fourier validation](fourier-validation.json) separately compares original
  and candidate graphs with the independent DFT and native named bindings for
  closed operation candidates.

Ordinary direct roots retain their source input/output identities. Their
producer-consistency check plus numerical Fourier comparison is distinct from
the closed-endpoint named Fourier contract. Named QPE `(1,2)` accepts both
schedules with the same work. Both `(1,3)` schedules return `limit` under the
existing budget; equivalent source no longer produces a false arity-contract
error. Native failure replies do not report required work.

New validation uses small systems only. The reviewer's width-five/eight results
are reported observations, not rerun validation. Historical reports and VM-22
artifact/request bytes remain unchanged. Current source/harness pins are reviewed
separately in the VM-22 inventory. Rust production verification remains
authoritative; these repairs add no new evidence rule or Lean authority transfer.

[Validation](validation.json) records the commands, source pins and observed
small-system results. [Issue 102](https://github.com/MGYamada/Qleisli/issues/102)
tracks commit and integration of this working-tree repair.
