# Explicit ownership-structure conversions: implementation packet

Scope: close the sized-register part of A020-01 needed by shared QFT/QPE. This
packet implements internal hierarchical data/checking, not source syntax or an
externally enabled schema. Desired source remains the preserved take_bit /
put_bit helper in docs/imaginary-v1/qpe.md. A type-preserving rewire cannot split
one Bits(8) owner into Bit and Bits(7); the six-bit finite matrix adapter cannot
justify that eight-bit boundary. This is an ownership/encoding obligation.

Add explicit unitary structural definition and meaning nodes for:
- take_bit(n,k) and put_bit(n,k), 1 <= n <= 8, k < n;
- split_tuple and join_tuple, preserving immediate tuple arity and nested trees;
- Bit <-> Bits(1), with explicit conversion in each direction;
- Unit <-> no owners and Bits(0) <-> no owners, explicitly consuming/creating
  the one-dimensional owner, never allowing an implicit drop or duplication.

Nodes cover exactly the converted quantum ports; unchanged frames compose via
existing tensor/call rules. All input owners are consumed, output owners are
fresh against those inputs, and every physical axis survives exactly once.
Classical ports are absent. take_bit returns selected Bit first and the Bits(n-1)
remainder in original order, including a fresh linear Bits(0) owner for n=1.
put_bit is its inverse. Tuple conversion concatenates/splits only the immediate
fields; it cannot conflate flat and nested tuple types. Labels may be renamed
separately by checked calls, never used as positional indices.

The meaning is the phase-free basis bijection selected by the actual wire
routing, extended by identity on an arbitrary reference. Check complete types,
owner transition, axis order and both finite inverse laws without matrices.
Prove actual checker acceptance implies those conditions and the two coefficient
round trips. The generic semantic derivation must later bind the same operation
and exact endpoints in definition and meaning; adding these nodes does not
turn structural typing into arbitrary semantic evidence.

Validation: n=1..8/all selected axes, both directions and phase-sensitive joint
coefficients; Unit/Bits(0) ownership, explicit Bit/Bits1 and flat/nested tuple
conversions; wrong axis order/types/arity, missing or duplicated remainder,
owner capture, missing axes, scalar and storage limits, depleted shared budgets.
Run definition/contract/preparation regressions and both Lean audits. Retain the
first implementation and real diagnostics. No release or source-completion claim.
