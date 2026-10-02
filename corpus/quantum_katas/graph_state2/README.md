# graph_state2

Translation of `AllBasisVectorWithPhaseFlip_TwoQubits_Reference` from the [frozen source](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs); `MIT`. Original notices and [permission records](../../POLICY.md) apply.

Contract: CZ (H tensor H); U[y,x]=(-1)^(x dot y+y0*y1)/2. Zero input has the negative |11> coefficient; absolute phase and all columns are retained.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0, 0] and measures each returned leaf in Z.

Scope: Exactly one two-wire graph edge; no scalable graph-state API or general state-preparation inverse.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `graph_edge_erased` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
