# add_one3

Pinned source symbol: `AddK` in `qualtran/bloqs/arithmetic/addition.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: |x> maps to |(x+1) mod 8>, phase +1 on all eight inputs; first leaf low bit.

Scope: bitsize=3, k=1; explicit carry circuit, not scalable synthesis or an upstream resource-cost claim.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [1, 1, 1], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/add_one3 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `increment_wrong_carry_order` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
