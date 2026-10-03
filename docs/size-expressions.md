# Linear sizes and explicit reshape

Adopted direction, no production symbolic solver/array/reshape API. Bounded sized experiments and R14/H1–H5 remain separate.

## Existing intact-atom helper

[Reshape.check](../lean-kernel/QleisliKernel/Reshape.lean) removes tuple/Unit structure but compares complete ordered atoms; never splits Bits(k). Bit/Bits(1)/Bits(0) differ. One owner becomes fresh owner with same axes/frame and reference identity, coefficient +1, including zero width; no ports/gates/allocation/phase. Reject malformed types/requests/axes/owners/limits. Linear atom comparison and conservative quadratic uniqueness charge are no compiler theorem. [First source](../tests/fixtures/authoring_sessions/reshape-v021/session.json)/[tests](../scripts/test_lean_reshape.py) grant no production seal. New producers need checked endpoints; inverse swaps them without granting opaque access.

## Size arithmetic and equality

Quantifier-free naturals/binders/addition/constant multiplication/=,!=,<,<=/Boolean combinations. Exclude symbolic products/exponents/calls/division/remainder/min/max/quantifiers. a-b requires b≤a; prefer n+1. Equality holds under assumptions, not one assignment; contradictory contexts grant no evidence. Generic/concrete/zero-body checking separate.

Normalize exact coefficients in stable binder order, combine terms/remove zeros/constant last/fixed association; precharge work/storage. Guarded subtraction retains nonnegativity, no unsound Nat.sub/definitional equality. Transport changes indices only within identical constructors, preserving full trees/order/owners. No implicit Bits<n+m>/segments/Bit/Bits1/Unit/Bits0 coercion.

## Ordered bit-segment reshape

Future extension compares ordered Bit/Bits<e>/Unit segments without per-bit expansion, preserving non-bit atoms and zero-field distinctions. One owner in/out; splitting owners separate. x=low+2^n high, low=x mod2^n, high=x div2^n; prove bounds/encodings/both inverses/reference identity with coefficient +1, no dense tables. Bits<n+1>→(Bit,Bits<n>) selects low bit; reverse partition/SWAP/phase explicit. Exponentiation is semantic, not grammar. Future [Bits<d>;L] needs separate indexing/layout/ownership/bounds and grants no nonlinear size or limit escape.

## Lean boundary and acceptance

Recheck expressions/context/instantiation/endpoints; flags/casts/hashes/submitted Lean code are not evidence. Production equality needs closed checked certificate/theorem or concrete reconstruction. Lean4.30 omega lacks dark/grey shadows; failure means unproved, no native fallback. n+1 follows recursion, BitVec.cons/concat layout still explicit. Audit private/generated/transitive definitions.

Before new acceptance specify parsing/domains/diagnostics/effects/owners/lowering/migration; prove normalization/context/endpoints/encoding/inverses/reference. Test zero/commuted/doubled/guarded sums, missing/conflicting premises/products/bounds/fresh-empty owners and axis/phase/drop/forgery faults. Six-bit leaves, QPE n,m1..8/combined16 unchanged; small validation only. [Sized attempt](../tests/fixtures/authoring_sessions/sized-reshape-v021/session.json) records rejection, not compilation.
