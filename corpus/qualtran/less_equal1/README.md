# less_equal1

Frozen source: [LessThanEqual](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/arithmetic/comparison.py). Translation license: **Apache-2.0**; upstream notices are retained in both QLI files.

Contract: |a,b,t> -> |a,b,t xor [a<=b]> with amplitude +1 for unsigned one-bit a,b and either target value.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: Both register widths are one. A direct reversible gate kernel replaces the upstream general decomposition; no T-count or scaling equivalence.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [less_equal_changed_to_strict](../../semantic_faults/less_equal_changed_to_strict/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
