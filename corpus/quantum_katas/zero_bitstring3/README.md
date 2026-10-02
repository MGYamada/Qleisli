# zero_bitstring3

Pinned source symbol: `ZeroAndBitstringSuperposition_Reference` in `Superposition/ReferenceImplementation.qs`; commit and original hash are in [the manifest](../../manifest.json).

Contract: CNOT(0,2) H(0), bits=[true,false,true]; |000> becomes (|000>+|101>)/sqrt(2).

Scope: Fixed three-wire bit string. Upstream array positions are preserved; QLI first leaf has integer weight one. Return every owner; no postselection.

`kernel` consumes and returns the same ordered Q owner; effect Unitary. `main` prepares input [0, 0, 0], then consumes every output through Z measurement. No auxiliary owner is implicitly released.

Validate every complex entry with `python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/zero_bitstring3 --exhaustive` from the repository root. The analytic oracle uses no QLI lowering or upstream runtime. Paired fault `bitstring_wrong_target` must typecheck and disagree with that oracle. Numerical tolerance 1e-11 is not a formal source-preservation proof.

[Intake policy](../../POLICY.md) and [notices](../../NOTICE) apply; upstream files and licenses remain frozen.
