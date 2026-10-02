# greater_constant2

Pinned source symbol: `GreaterThanConstant` in `qualtran/bloqs/arithmetic/comparison.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: |x,t> maps to |x,t xor [x>1]>, x=a+2b, phase +1; arbitrary target retained.

Scope: Unsigned two-bit x and val=1; translates the documented comparison contract, not the general upstream decomposition or resource count.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 1, 1], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/greater_constant2 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `greater_constant_wrong_threshold` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
