# rotation_half_x

Pinned source symbol: `circuit(params)` in `demonstrations_v2/tutorial_qubit_rotation/demo.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: RX(pi)=-iX, params=(pi,0), including the scalar on both columns and under control.

Scope: Fixed exact angles; no optimizer, continuous-angle input or expectation-only equivalence.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/rotation_half_x --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `half_rx_missing_scalar` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
