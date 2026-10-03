# two_bitstrings3

[TwoBitstringSuperposition_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs), frozen MIT input; [license](../../upstream/quantum_katas/LICENSE).

For bits1=[true,false,true], bits2=[false,true,true], apply X(2) X(1) CNOT(0,1) H(0). Zero becomes (|101>+|110>)/sqrt(2), in low-bit integer labels 5 and 6.

Fixed two distinct three-bit strings; preserve the original full unitary extension, not an arbitrary state-preparation API.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests omit the bit-string offset x on the second wire. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
