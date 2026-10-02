# ising_zz_half2

Pinned source symbol: `U_C(gamma), single-edge factor` in `demonstrations_v2/tutorial_qaoa_maxcut/demo.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: exp(-i*pi*Z0*Z1/2)=-i Z0 Z1, gamma=pi; complete phase-fixed diagonal.

Scope: One isolated edge; excludes the original four-node graph, mixer, preparation and optimization.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 1], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/ising_zz_half2 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `half_zz_missing_scalar` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
