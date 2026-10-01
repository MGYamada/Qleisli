# toffoli3

Frozen source: [ToffoliGate_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/BasicGates/ReferenceImplementation.qs). Translation license: **MIT**; upstream notices are retained in both QLI files.

Contract: |a,b,t> -> |a,b,t xor (a*b)> with amplitude +1, preserving both controls and an arbitrary target.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: Exactly three wires. The sealed Toffoli replaces CCNOT; no scalable multicontrol synthesis or extra workspace claim.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [toffoli_ignored_second_control](../../semantic_faults/toffoli_ignored_second_control/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
