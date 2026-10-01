# qaoa_mixer2

Frozen source: [U_B(beta)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_maxcut/demo.py). Translation license: **Apache-2.0**; upstream notices are retained in both QLI files.

Contract: RX(pi/2) tensor RX(pi/2)=(I-iX) tensor (I-iX)/2, including its scalar and arbitrary two-wire input.

QLI axis 0 is the first leaf; integer labels are low-weight-first and result bits retain tuple order. All owners are returned; no scratch is silently released.

Scope: Restrict U_B to two wires and beta=pi/4. This isolated product mixer excludes the original four-node graph, cost layer, Hadamard preparation and optimization.

[Authoring record](../../authoring/v025-small/session.json) preserves the full source before checking. Independent arithmetic/complex-column oracles and controlled X/Y probes check every matrix entry. [mixer_erased_scalar](../../semantic_faults/mixer_erased_scalar/kernel.qli) must typecheck and disagree with that contract. Numerical comparison uses 1e-11; it supplies no exact evidence or general proof. No upstream framework is executed.
