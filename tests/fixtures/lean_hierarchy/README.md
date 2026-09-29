# First shared-hierarchy development record

This is the informed, local CD-3 experiment for the
[experimental phase DAG](../../../docs/lean-hierarchy-slice.md). It is not a
controlled model benchmark or a new external input corpus. All files are
Apache-2.0, Copyright 2026 Masahiko G. Yamada.

## Preserved first attempts

- [first_source/main.qli](first_source/main.qli) is the original current-syntax
  source, saved before checking. It applies T through two 4096-fold repetition
  definitions. The independent expectation is identity, retaining phase.
- [shared.qhd](shared.qhd) and [identity.qhr](identity.qhr) are the desired shared
  artifact and separately fixed request, also saved before implementation.
- [baseline.json](baseline.json) retains hashes, real commands and diagnostics:
  the Rust source check fails its finite evidence limit, and the former native
  executable rejects the then-unsupported `--phase-dag` invocation.
- [first_dag_proof.lean.txt](first_dag_proof.lean.txt) and
  [first_dag_diagnostics.txt](first_dag_diagnostics.txt) retain the first failed
  generic DAG proof. Reserved-name and Option/Array map proof errors were
  repaired in the final module. This is not a complete edit-by-edit transcript;
  no measured total repair-count claim is made.

The first source is deliberately **not overwritten**. It still fails in Rust;
there is no sized-source or source-to-DAG producer in this slice. The new
independently checked IR removes expansion during verification, not an authoring
obligation in currently executable `.qli`.

## Independent decision and counterexamples

[The native test suite](../../../scripts/test_lean_hierarchy.py) executes gates
directly on both basis bits for small generated DAGs. A separate complex-column
calculation checks the intended phase interpretation with a test tolerance;
no tolerance enters acceptance. The well-typed `x p16 x p16` action retains a
nontrivial global phase and must reject an identity request.

The second reuse experiment generates 100 mixed leaf/call/sequence/repetition
DAGs, rather than relying on the nested-power example alone. Every case also
changes the independently requested meaning and an intermediate producer claim.
Further cases cover all 256 scalar phases, odd/even powers through count 4096,
changed bodies/dependencies, exact shape tags, zero-width owner ports, invalid
zero-repeat bodies, cycles, unreachable entries, depth/work and wire limits.
Each decision runs a new native checker process. This does not yet supply the
required order-finding/amplitude-estimation reuse of common QPE.

## Measured after-state

[after.json](after.json) records actual native observations, input hashes/sizes
and timings, plus the source's unchanged rejection. It includes the complete
generated depth-64 artifact so its measurement is reproducible.

| Observation | Original | After this slice |
| --- | --- | --- |
| Desired source | 283 bytes; finite evidence limit | Same source and rejection |
| Shared artifact / request | 122 / 53 bytes; unsupported command | Accepted; 3 definitions, 2 references, 47 charged units |
| Implied primitive execution | 16,777,216 T gates | Same count; not actually simulated |
| Larger sharing experiment | Not implemented by old phase-word mode | 1639-byte artifact; 64 definitions, 63 references, 1328 units; `4096^63` implied gates |
| Dense matrices during verification | No successful old DAG verification | Zero |
| `.qli` duplicate definitions / manual conversions removed | Zero | Zero; source integration remains open |

Input sizes include the proposed evidence summaries in each definition.
`work_units` is an explicit accounting model, not measured CPU instructions or
an elapsed-time guarantee. Recorded native process times are single local runs,
not a controlled performance comparison. No fully expanded large IR was built.

The final Mathlib-free kernel passed native build, tests, the **697-declaration**
compiled audit and fresh-environment Lean-kernel replay. The Python hierarchy
suite passed **11 tests / 647 native decisions**. The
[clean build record](clean-build-record.json) retains a separate source-copy
build and checks without `.lake` state or external Lake packages. This is not
the clean Git distribution or release gate. Full H1–H5, complex interpretation,
general ownership, QFT/QPE and source translation remain unproved/unimplemented
as detailed in the profile document.
