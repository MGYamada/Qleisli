# rotation_mixed_sign

Frozen source: [circuit(params)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py). Translation license: **Apache-2.0**; upstream notices are retained in both QLI files.

Contract: RY(-pi/2) RX(pi/2), in upstream order, with all complex column signs and absolute scalar phase retained.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: Fix params=(pi/2,-pi/2). Gate kernel only; expval(Z) is computed from the measured distribution, with no optimizer or continuous-angle API.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [mixed_rotation_order_reversed](../../semantic_faults/mixed_rotation_order_reversed/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
