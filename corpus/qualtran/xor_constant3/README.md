# xor_constant3

Pinned source symbol: `XorK` in `qualtran/bloqs/arithmetic/bitwise.py`; commit and original hash are in [the manifest](../../manifest.json).

Contract: |x> maps to |x xor 5>, phase +1; first leaf low bit.

Scope: bitsize=3, k=5; no symbolic-width or signed-integer API.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 0, 0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/xor_constant3 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `xor_constant_missing_high_bit` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
