# even_numbers3

Pinned source symbol: `EvenOddNumbersSuperposition_Reference` in `Superposition/ReferenceImplementation.qs`; commit and original hash are in [the manifest](../../manifest.json).

Contract: I(0) tensor H(1) tensor H(2); prepare the uniform labels 0,2,4,6 from zero.

Scope: Width three, isEven=true; QLI axes reverse the upstream array so the unchanged upstream last wire is the low bit. Full unitary extension retained.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 0, 0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/even_numbers3 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `even_numbers_wrong_low_bit` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
