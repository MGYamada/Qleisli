# Typed phase/layout development record

This informed CD-3 implementation exercise belongs to Qleisli (Apache-2.0).
It adds no external corpus source and is not a controlled model benchmark.
The [bounded contract](../../../lean-kernel/QleisliKernel/PhaseLayout.lean) preceded the
new acceptance path. The [first source](first_source/main.qli) and actual
[baseline](baseline.json) preserve a working finite program and the old Lean
executable's unsupported-command response. The old command was probed with
placeholder path arguments; it rejected the flag before reading files.
The first desired [artifact](shared.qhd) and [request](expected.qhr) were saved
before implementing their transport, and remain unchanged.

## Actual repairs and scope

- The first source needed **zero revisions**. It preserves a quantum Unit owner,
  calls the same phase-and-swap body twice and adds a controlled T.
- [First polynomial source](PhasePolynomial-first.lean.txt) and [diagnostics](first-polynomial-diagnostics.txt)
  retain incorrect library lemma assumptions and simplification direction.
  Repairs use existing modulo simplification laws, a proved list-permutation
  sum lemma and a separate zero-filter proof. No axiom or numerical tolerance
  was introduced into acceptance.
- [First graph source](PhaseLayout-first.lean.txt) and [diagnostics](first-graph-diagnostics.txt)
  retain namespace ambiguity with the earlier one-bit `normalize`, plus a
  monadic proof reduction. Qualification and explicit option reduction resolve
  them. The transport request type also needed qualification to distinguish
  its layout/polynomial summary from the one-bit summary.
- [First closed-reduction diagnostics](first-reduction-diagnostics.txt) retain
  the ordinary `decide` tactic's failure to unfold a sorting definition. The
  final tests use kernel reduction and the sort's defining equations. They do
  not use `native_decide` or admit a failed goal.
- Implementation review identified that claim/request validation must itself
  be charged before inspecting large sparse expressions. The final checker
  includes those charges; a dedicated 14-leaf false-claim regression exhausts
  the budget before composition. Verified cached results match their claims
  immediately, so false small counts cannot become cheap later premises.

These are diagnostic checkpoints and repair descriptions, not a complete
editing transcript or measured total repair count. First-attempt errors remain
historical fixtures. Final proof declarations and generated runtime helpers
pass the compiled audit. No new source syntax, public standard-library API,
complex semantic bridge or source-to-new-IR producer is claimed.

## Independent checking and reuse

The [native suite](../../../scripts/test_lean_phase_layout.py) executes literal
phase conditions and owner-wise layouts on small assignments, following calls
without reading their claimed summaries. It covers all 256 ticks, scalar and
controlled phase, remapped axes, ordering, stale evidence, exact types and
zero-wire owners, canonical forms, graph/byte/work limits, and joint complex
reference coefficients. **11 tests / 382 fresh process decisions** pass.

The [wrong-axis circuit](wrong_axis.qhd) is structurally valid and accepted by
its [actual contract](axis_actual.qhr), but rejected by the independently
specified [intended axis contract](axis_expected.qhr). This is a semantic
counterexample rather than a syntax/type error.

The separately saved [interference client](interference_client/main.qli) prepares
two qubits and observes them after Hadamard interference. Its
[first execution](interference-source.json) required zero repairs. For each
output y, the independent expected probability is

```text
| (1/4) Σ_{x∈{0,1}²} (-1)^(x·y) exp(iπ(x0+x1+x0*x1)/4) |².
```

All four outcomes agree on both installed primary/MSRV Rust binaries. CI checks
the same formula on both toolchains with `--source-only`. This client uses the
finite T profile; π/8 and smaller phases are exercised by the Lean experiment.
This is testing of separate boundaries, not a source-translation proof.

Source-body duplication and manual source conversions remain unchanged; no
authoring-time or generation-time improvement was measured. The removed checker
burden is manual phase/axis reasoning and expanded shared circuit bodies.

## Observations and validation

[After observations](after.json) retain commands, results and source/binary
hashes. [Prior-profile/source/helper regressions](regressions.json) preserve their
actual outputs. The examples below have dense dimension **zero**:

| Artifact | Nodes / references | Work / phase work | Cached terms | Expanded phase terms |
| --- | --- | --- | --- | --- |
| `shared.qhd` | 5 / 5 | 12,289 / 3,048 | 3 | 3 |
| [Depth 64](depth64.qhd) | 64 / 126 | 22,664 / 9,096 | 0 | 9,223,372,036,854,775,808 |
| [16 axes plus Bits0](sixteen_axes.qhd) | 2 / 1 | 30,502 / 3,456 | 3 | 3 |

The depth-64 artifact is 9,555 bytes. Its phase polynomial cancels, but expanded
application accounting still records 2^63 literal phase operations. These are
static counts, not a measured execution-time guarantee or a completed QPE case.

The [isolated build record](clean-build-record.json) contains a fresh copy without
`.lake`, no external packages and cleared Lean path/toolchain overrides. It
passes build, reductions, compiled audit, fresh `Main` kernel replay and all
382 native tests. A subsequent README-only command prerequisite is identified
separately in that record; compiled sources are unchanged. This is not clean
Git release-distribution validation. See the
[release checkpoint](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md#typed-phase-and-layout-checkpoint-2026-09-29)
for performed checks and remaining gates.
