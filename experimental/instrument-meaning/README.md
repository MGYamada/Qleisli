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
python3 experimental/instrument-meaning/check_gate.py --record /tmp/instrument-gate.json
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

[the independent instrument reference](../../lean/Qleisli/Semantics/InstrumentEquality.lean) independently defines the
complete hidden-history channel and its Choi coefficients. Its checked theorem
derives equality of each public outcome map on arbitrary joint input/reference
matrices, even with different hidden-history counts. The
[proof record](proof-validation.json) retains the actual Lean 4.30.0 compilation
and axiom output; only `propext`, `Classical.choice` and `Quot.sound` occur.
The original experimental sources remain in Git history; the current proofs
now live in the production Lean tree and connect to the native byte gate below.

[the coefficient bridge](../../lean/Qleisli/RawInstrumentEquality.lean) connects the actual preparation
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
existing pinned project, freshly compiles the production bridge, checks twelve
axiom sets and removes its temporary outputs on exit.

Both Lean packages were built and audited; the kernel root and native Main
were freshly replayed. Existing scoped
guarantees were rechecked against unchanged typed bindings and protected
Raw/Basis expressions before updating their current technical evidence; this
adds no guarantee.

The [original-QIRF component](../../lean-kernel/QleisliKernel/Qirf/InstrumentContract.lean)
now freshly checks both complete original graphs before reconstructing them.
Its continuous work-state success witness retains identity validation, exact
complete signature equality, ordered classical/quantum projections, principal
Observe checks from the actual body, complete Gram checks and coefficient
comparison. Ordinary Unit/Bit/Bits, entire tuple trees, each quantum basis tree
and zero-width owners are kept separately. Requested signatures are type data;
this is not a proof that native IR independently recovers a source type.
Factoring the existing reconstruction preserves its previous complete WorkM
recipe, including failures and remaining work, by definitional equality.

[the original-gate bridge](../../lean/Qleisli/QirfInstrumentContract.lean) proves that shared reconstruction denotes
the original body and has complete Kraus sum. It connects original ordered
result IDs to the independent full instrument, proves all compared original
dimensions are retained, and derives exact equality on arbitrary finite joint
references. The [gate proof record](original-gate-proof-validation.json) retains
fresh compilation, nine axiom checks and the existing twelve small regressions.
Only the same three standard Lean axioms occur. The
[39 fresh native checks](original-gate-validation.json) include wrong complete
types of equal width, missing/extra zero-width owners, false Observe annotation,
ordinary Bits<0>, malformed type trees, result/residual-axis order, wrong roots,
fresh dependency replacement and exhausted work. Their temporary experimental
driver reads original QIRF bytes; it is not a public protocol definition.
Malformed prefix trees reject before allocating more children than their
remaining atoms can contain, keeping pending storage within the structural cap.

The strict production decoder now carries both complete signatures, source
identity and original expected QIRF text in the existing `--qirf-contract` mode.
[The protocol contract](../../docs/src/reference/production-boundary.md#original-artifact-observing-instrument-requests)
fixes its exact fields, bounds and refusals. Production byte acceptance is
connected to both original meanings, complete Kraus sums and exact public
outcome maps on arbitrary finite external references. The existing native
verification runner includes its transport and small semantic regressions.
The [native-wire record](native-wire-validation.json) retains 381 process checks,
the unchanged 799 original decisions, fresh production proofs and audits,
both toolchains' focused native tests and the two existing guarantee checks.

The private paired Rust handle now retains the exact original accepted
implementation/reference artifacts, complete signature and source identity.
Ordinary concrete compilation executes only the implementation, rechecks its
actual call interval through a fresh native request, and retains that call
alongside the original pair. Whole-root request disclosure stays unchanged.
The [focused Rust integration record](finite-source-validation.json) describes
this bounded unit and its limitations. Explicit specialization and its source
replay remain unimplemented; this does not complete both adapters or #46.
Complete source type preservation remains an open proof obligation. Hosted
completion CI, packaging and full release checks were not rerun. Source, decoder/native/runtime and realization
correspondence remain separate obligations. Issue #46 stays open.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
