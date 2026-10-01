# controlled_z2

Frozen source: [TwoQubitGate2_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/BasicGates/ReferenceImplementation.qs). Translation license: **MIT**; upstream notices are retained in both QLI files.

Contract: |a,b> -> (-1)^(a*b)|a,b>; full diagonal CZ, including relative phase under an additional control.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: Two wires, whole-space gate kernel; preserves the upstream controlled-Z operation. No new controlled API or array syntax.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [cz_replaced_by_identity](../../semantic_faults/cz_replaced_by_identity/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
