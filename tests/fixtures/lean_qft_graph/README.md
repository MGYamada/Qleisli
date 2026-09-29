# Typed shared QFT graph development record

This informed 2026-09-29 packet continues the full v0.2.0 goal under the
[selected checking contract](../../../docs/lean-qft-graph-packet.md). It is not
a controlled model benchmark or an enabled external schema importer.

The original [desired sized source](../authoring_sessions/shared-qpe-v020/attempt-01/estimation.qli)
remains the authoring target. The [unchanged finite round trip and wrong reversal](../lean_qft/README.md)
retain their original hashes and checks. Source repairs, body duplication and
manual wiring remain unchanged. This packet removes the need to trust a
separate, unbound flattened QFT witness.

[first-graph.json](first-graph.json) retains the initial native three-bit graph.
[First.lean.txt](First.lean.txt) and [first-diagnostics.txt](first-diagnostics.txt)
retain the actual checker/proof attempt: incomplete unfolding of option binds
and a conjunction projection before simplification. Repairs make those steps
explicit. [Fourier-first.lean.txt](Fourier-first.lean.txt) retains the mathematical
proof; its [first invocation](first-fourier-diagnostics.txt) found a missing
prerequisite object because the runtime proof was still being repaired. After
the dependency built, the [actual proof run](fourier-proof-diagnostics.txt)
succeeded without a theorem change.

The [first reduction-test diagnostics](first-test-diagnostics.json) show ordinary
`decide` stuck at private imported definitions. The final examples use `cbv` to
produce kernel-checked proofs through the definitions' equations, without native
proof evaluation or a new axiom. The full checker and mathematical statements
are proved independently of these finite reduction examples.

[native.json](native.json) records 68 C-compiled decisions and 744 independent
literal graph paths, plus code hashes. Semantic wrong-axis/phase/dependency/final-
permutation cases pass metadata and graph checks before failing the QFT matcher.
It also records zero-owner/type-tree/port/effect mutations, cycles, dead nodes,
36/37-gate, 64/65-depth and 256/257-node boundaries. The large shared-identity
case has 170 nodes, 228 references, 773 charged gate entries, depth 62 and
2^59+37 expanded literal actions. Verification does not expand or execute them.

[proof-checks.json](proof-checks.json) records both builds, runtime reductions,
compiled/axiom audits and source policy. [regressions.json](regressions.json)
records fresh kernel replay, compiled-policy/helper tests and the previous
independent QFT experiment. Numerical oracles remain test evidence; they cannot
issue semantic receipts.

```sh
python3 scripts/test_lean_qft_graph.py
```

The completed theorem binds typed internal fragments and actual graph semantics.
The external hierarchy's finite-leaf/control/rewire projection, theorem manifest,
transport, source producer, full QPE instrument and release gates remain open.
Production Rust authority is unchanged; this record claims no publication.
