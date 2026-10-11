# Exact instrument contract experiment

This bounded #46 study investigates the observing overload of `apply_contract`
**adopted by the human maintainer on 2026-10-11** in the
[separate decision record](https://github.com/MGYamada/Qleisli/issues/46#issuecomment-6104666552).
The [reviewed packet](proposal.md) retains its original candidate notice and
SHA-256 `5bd33aa0c2064a61b195ab4f692e5bd15d31af7c44bf2807dfdb1cc1e0f80052`.
It states its scope, expected
programs, native boundary, equality limits and remaining proof obligations.
It is ordinary language design under the existing adopted interpretations.

Run the independent host algebra, optionally with fresh VM-26 reconstruction:

```sh
python3 experimental/instrument-meaning/check.py --record /tmp/instrument-host.json
python3 experimental/instrument-meaning/check.py --native --record /tmp/instrument-native.json
python3 experimental/instrument-meaning/check.py --native-compare --record /tmp/instrument-comparison.json
python3 experimental/instrument-meaning/check_proof.py --record /tmp/instrument-proof.json
```

The [first source study](../../tests/fixtures/authoring_sessions/instrument-contract-v030/README.md)
retains four original projects, their current refusals and the actual native
experiment record. Native compilation uses the existing shared harness; its
temporary driver is removed on exit. No results or acceptance decisions are
cached. The host CP comparison is an independent experimental oracle.
`--native-compare` freshly reconstructs both original VM-26 bodies, then runs
the [Mathlib-free streamed coefficient component](../../lean-kernel/QleisliKernel/Raw/InstrumentEquality.lean).
All eight pairs agree with the host oracle, and a zero-budget request rejects;
the [comparison record](native-comparison-validation.json) retains the actual
driver, input, library and response identities. Physical sizes in this driver
do not establish complete source types or principal Observe effects. It is
an unwired component, not a production contract gate or guarantee discharge.

[ReferenceEquality.lean](ReferenceEquality.lean) independently defines the
complete hidden-history channel and its Choi coefficients. Its checked theorem
derives equality of each public outcome map on arbitrary joint input/reference
matrices, even with different hidden-history counts. The
[proof record](proof-validation.json) retains the actual Lean 4.30.0 compilation
and axiom output; only `propext`, `Classical.choice` and `Quot.sound` occur.
This mathematical foundation is not yet connected to a production native
instrument-comparison gate.

[NativeCoefficient.lean](NativeCoefficient.lean) connects the actual preparation
and comparison definitions to that independent reference: ordered public
projection preserves the reconstructed matrices, each streamed scalar equals
the complete complex coefficient sum, and successful comparison implies
equality of every unnormalized outcome map on any joint input/reference
matrix. Different hidden-history counts and absent zero outcomes are allowed.
The [bridge record](native-coefficient-validation.json) includes fresh compilation
and four axiom checks; only the same three standard Lean axioms occur.
[Twelve small checked regressions](ComponentChecks.lean) cover split Kraus
histories, zero outcomes, empty/malformed histories, arity/dimension/entry-count
mismatches, noncanonical scalars and exhausted work. The proof runner uses the
existing pinned project and removes its temporary modules on exit.

Both Lean packages were built and audited; the kernel root and native Main
were freshly replayed. Existing scoped
guarantees were rechecked against unchanged typed bindings and protected
Raw/Basis expressions before updating their current technical evidence; this
adds no guarantee. The production request decoder, complete signature/source
gate, both source adapters and call-boundary validation remain unimplemented.
Rust suites, hosted completion CI, packaging and full release checks were not
rerun for this unwired component. Source, decoder/native/runtime and realization
correspondence remain separate obligations. Issue #46 stays open.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
