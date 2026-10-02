# controlled_h2

Pinned source symbol: `ControlledRotation_Reference` in `Superposition/ReferenceImplementation.qs`; commit and original hash are in [the manifest](../../manifest.json).

Contract: CH(0,1) H(0), with the first QLI leaf the low bit; |00> becomes |00>/sqrt(2)+(|01>+|11>)/2.

Scope: Two-wire preparation and its full unitary extension; no continuous rotation or arbitrary-width API.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/controlled_h2 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `controlled_h_unconditional` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
