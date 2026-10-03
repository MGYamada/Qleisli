# w2_retained3

[WState_PowerOfTwo_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs), frozen MIT input; [license](../../upstream/quantum_katas/LICENSE).

N=2 recursion: X(a), H(r), controlled-SWAP(r;a,b), CNOT(b,r). On zero input, output is (|100>+|010>)/sqrt(2) in returned (a,b,r) order, with r=0; the full three-wire unitary is checked.

The upstream temporary ancilla is an explicit third input/output owner. It is zero only for the promised preparation input; no general clean-release claim or ancilla disposal is made.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests omit the ancilla disentangling cnot; data probabilities alone agree. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
