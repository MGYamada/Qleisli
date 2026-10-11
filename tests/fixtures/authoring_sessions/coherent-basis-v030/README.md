# Coherent basis syntax: informed first sources

Issue #81 adopts `basis q as p { e }` as the coherent basis-map spelling.
These 9 semantic controls are separately authored desired/legacy pairs:
18 complete schema-2 edition-2026 projects with at most 3 source qubits.
The context and source identities were saved before checking. This is an
informed study, not a blind model benchmark, an implemented syntax claim or
an algorithm/source-preservation proof.

The fixed existing CLI has SHA-256
`a7c2b2d387dc0c3ae360b047ff433abb7e341cc21c8a9aefbfe8b5056c791ae8`;
the explicitly selected native checker has SHA-256
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
The checkout marker is `73355382a3db94893982e5954e9400fffcd7f48e`.
Executable identity is not compiled-HEAD attestation or a fresh Lean replay.
No rebuild or download was performed. Source and executable hashes were
checked before and after every actual invocation.

`observations-before/capture.json` registers 44 real commands: 9 succeeded
and 35 refused. All 18 checks of the new spelling rejected at parsing in this first capture.
The old entangle, permutation and phase/reference projects each pass finite
check, run and IR emission. Their three original artifacts total 2,553 bytes.
The original floating-point streams retain rounding residues: the phase/reference
uncompute has probability 1 for 000 and `6.162975822039156e-33` for 100.
These observations do not replace the separately stated exact equations.

The legacy zero-owner control is not falsely reported as an executable positive:
finite check/run/emission refuse `std::quantum::unit`, and its selected path
refuses CoherentLift projection. Selected checking of the other legacy positives
also retains its located concrete CoherentLift eligibility restriction. Generic
full-body checking and concrete materialization remain separate obligations.

Legacy negative controls retain actual noninjectivity, quantum capture,
runtime-classical capture, consumed-owner reuse and non-Basis call refusals.
The new spelling could not yet reach those conditions in the first capture; its parser errors
are retained without pretending they validate downstream rules.

`first-files.json` records the expected +1 basis maps, exact ordered permutation,
external-reference correlation and T phase before running any command.
The three-qubit phase/reference source has joint intermediate state
`(|000> + exp(i*pi/4)|111>)/sqrt(2)` in a,b,r order; the prescribed uncompute
returns 000. Computational-basis probabilities before that interference
would not establish the phase. No independent numerical oracle was invoked
in this first capture.

Keep every first source, prediction, command, raw stdout/stderr, exit and
emitted artifact unchanged. Append later results separately. Do not replay
commands read from observations. `capture_before.py` is the original authored
driver and refuses to overwrite its first capture. It does not count native
child starts/exits or establish source/runtime correspondence.

`consumer-inventory-01.json` identifies the frozen direct consumers and selected
fixture/corpus sources requiring derivative migration.
`active-source-migration-01.json` records the 72 spelling-only changes in
18 Rust test files and 3 live examples; no build or test accompanied that edit.
`external-qlippy-consumer-01.json` records the actual external qargo consumer:
its linked Qleisli pin is 0.2.1, so an upstream diagnostic change does not by
itself validate Issue #81's qlippy requirement. That component remains pending.

The applicable QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 obligations
remain; the two ordinary QLV1 structural guarantees are unchanged. No Guardian
act, guarantee admission, Issue completion or release approval follows.

## Subsequent validation and correction

The fixed AFTER CLI `4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50`
was built separately. `observations-after/capture.json` and its supplementary
capture register 57 actual commands on the unchanged first sources. The three
supported desired controls reproduce the frozen legacy QIRF bytes exactly and
retain their numerical distributions. Independent small-system calculations
check the +1 maps, ordered permutation and phase/reference interference.
Five finite negative controls retain their earlier semantic diagnostics.
All old spellings now receive targeted parse refusals with source locations.

The first AFTER analysis preserves 64 successful checks and one omission in
the authored numerical oracle: it had not implemented structural `join`.
`analysis-after-02.json` separately records the ordered-axis concatenation
extension and seven successful supplemental checks; it does not overwrite the
first failure or repair a Qleisli source.

The earlier paragraph's selected-path claim needs this correction: the actual
original commands select private `main::main`, so the positive controls and
Unit control fail with **visibility**, not CoherentLift projection. Those raw
observations stay unchanged. Four subsequently recorded public-entry controls
reach the current `unsupported runtime expression` projection diagnostic.
They establish the current limitation, not an unrecorded OLD public-entry test.

The external qlippy record remains an accurate account of what was inspected.
The maintainer subsequently authorized omitting its diagnostic update and
validation from #81's completion conditions. That component is now explicitly
excluded; no upgraded consumer is claimed. Qleisli text/JSON diagnostics and
the language contract remain required and are independently recorded.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
