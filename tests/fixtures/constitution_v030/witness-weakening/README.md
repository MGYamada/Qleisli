# Initial v3 witness-binding enforcement counterexample

This is a defect in the first v3 **evidence enforcement**, not a counterexample
to either admitted Lean theorem or its independent ownership/scope property.
The admitted proposal includes a witness connecting the original input bytes
to their decoded artifact. The initial enforcer preserved the property
definitions and theorem types but did not preserve the witness's field meanings.

The two-line `mutation.patch` weakens `Acceptance.packetBound` to `True` and
changes its constructor argument accordingly. In an isolated copy of the
historically reviewed sources:

- The pre-fix identity checker accepted refreshed mutable records.
- The changed `Protocol.Validity` and unchanged `Qleisli.NativeValidity` both
  compiled with warnings treated as errors.
- The unchanged historical `Review.lean` produced exactly the original 4,692
  output bytes, with the same axiom sets and no diagnostics.

That review printed only `Acceptance`'s outer type, so weakening a field was
invisible. The theorem remained true about a weaker witness; it no longer
expressed the complete originally admitted byte binding. Fresh hashes and the
unchanged theorem name/type output could not restore the missing meaning.

`before-fix.json` records source identities, observed command results and output
hashes. `check_initial_guarantees-before.txt` is the exact tested enforcer
(SHA-256 `79db4a2301d1d80def6b29d984ddf99710663534ca4c80552a15debd0a314e45`).
The other `*-before.txt` files retain its helper context. These are inert evidence
snapshots; the repository uses the fixed scripts under `scripts/`.
`weakened-validity.lean.txt` preserves the actual compiled mutation.
`reproducer-original.py.txt` preserves the original scratch driver; its absolute
temporary paths and sibling-olean setup describe the observed local run.

The temporary fresh audit/source records were synthesized specifically to test
identity enforcement. They were never presented as actual whole-project build
or audit results. The two changed-module compilations and the historical review
were real Lean executions against temporary modules. No adopted proposal,
historical review/output, repository proof source or normal build artifact was
overwritten. A separate `after-fix.json`, when present, records the current
enforcer's rejection of this same mutation.
