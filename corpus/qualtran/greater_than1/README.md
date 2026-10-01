# greater_than1

Frozen source: [GreaterThan](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/comparison.py). Translation license: **Apache-2.0**; upstream notices are retained in both QLI files.

Contract: |a,b,t> -> |a,b,t xor [a>b]> with amplitude +1, retaining both unsigned one-bit inputs and supporting target one.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: One-bit specialization of LessThanEqual followed by target X. Uses a direct negative-control Toffoli; no upstream decomposition/cost claim.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [greater_than_input_not_restored](../../semantic_faults/greater_than_input_not_restored/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
