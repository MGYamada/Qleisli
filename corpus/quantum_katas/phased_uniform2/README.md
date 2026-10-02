# phased_uniform2

Translation of `AllBasisVectorsWithPhases_TwoQubits_Reference` from the [frozen source](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs); `MIT`. Original notices and [permission records](../../POLICY.md) apply.

Contract: U[y,x]=(-1)^(x dot y+y0) i^y1/2, with wire 0 the first/low leaf. Prepares |- > tensor |+i> on zero, retaining every signed input column.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0, 0] and measures each returned leaf in Z.

Scope: Exactly two wires; preserves the selected preparation circuit as a whole-space unitary. No generic array preparation.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `uniform_phase_conjugated` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
