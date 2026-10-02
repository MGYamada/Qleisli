# qaoa_edge_layer2

Pinned source symbol: `U_C; U_B` in `demonstrations_v2/tutorial_qaoa_maxcut/demo.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: (RX(pi/2) tensor RX(pi/2)) exp(-i*pi*Z0*Z1/4); gamma=pi/2, beta=pi/4, cost before mixer.

Scope: Graph narrowed to one edge (0,1), two wires and one layer. No initial Hadamards, complete four-node QAOA port or optimizer.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/qaoa_edge_layer2 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `edge_layer_reversed_order` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
