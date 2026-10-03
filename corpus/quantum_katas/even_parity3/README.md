# even_parity3

[AllStatesWithParitySuperposition_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/Superposition/ReferenceImplementation.qs), frozen MIT input; [license](../../upstream/quantum_katas/LICENSE).

Width three, parity=0: coefficients U[y,x]=(-1)^popcount((x&3)&(y&3))/2 when y2=x2 xor y0 xor y1, zero otherwise. Zero prepares the four even-parity labels.

Specialize the recursive unitary preparation to three wires; no postselection variant or general-width synthesis.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests flip the required parity from even to odd. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
