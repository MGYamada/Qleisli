# Linear sizes and explicit reshape

Adopted direction, not a production symbolic solver/array/reshape API. [Sized source](sized-corpus-source.md), capacities and R14/H1-H5 are separate.

## Existing intact-atom helper

[Reshape.check](../lean-kernel/QleisliKernel/Reshape.lean) strips tuple/Unit constructors and compares ordered complete atoms: never splits Bits(k); Bit/Bits(1)/Bits(0) differ. One Q<A> becomes fresh Q<B>, retaining owner/frame/axes with coefficient +1 and reference identity; no classical ports/gates/allocation/phase. Unit factors may change, including zero width, not ownership. Malformed types/requests/axes/owners/limits reject. Atom comparison linear, uniqueness charge conservatively quadratic, not compiler complexity proof. [First attempt](../tests/fixtures/authoring_sessions/reshape-v021/session.json)/[native tests](../scripts/test_lean_reshape.py) supply no production seal. Future producers need independently checked structural/tensor/sequence endpoints; inverse swaps endpoints without broadening static/opaque access.

## Size arithmetic and equality

Initial quantifier-free linear fragment: natural constants/binders, addition, constant multiplication, =/!=/</<= and Boolean connectives. No symbolic products/exponents/calls/division/remainder/min/max/quantifiers. a-b requires b<=a before normalization; prefer n+1. Equality must hold under assumptions, not one assignment; contradictory contexts yield no evidence. Generic and instantiated profile checks remain separate; zero bodies still checked.

Canonical exact coefficients use stable binder order, combine like terms, remove zeros, constant last/fixed association; precharge storage/work. Guarded subtraction retains nonnegativity, no unsound Nat.sub rewrite/universal Lean definitional equality. Explicit equality transport reconciles indices only within identical constructors; full trees/order/owners remain. Bits<n+m>, tuple segments, swapped factors, Bit/Bits<1>, Unit/Bits<0> never implicitly coerce.

## Ordered bit-segment reshape

Future extension, not Reshape.check: compare ordered Bit positions/Bits<e> segments/empty Unit without per-bit expansion, retaining non-bit atoms and zero field positions/distinctions. One owner in/fresh owner out; splitting owners separate.

x=low+2^n*high; low=x mod2^n<2^n; high=x div2^n<2^m; x<2^(n+m). Relabelling coefficient +1/otherwise0; prove encoding, both inverses and arbitrary-reference identity without dense tables. Dimension exponentiation is not type grammar. Bits<n+1>->(Bit,Bits<n>) selects low bit; (Bits<n>,Bit) partitions differently. Reversal/SWAP/phase explicit. Future [Bits<d>;L] needs separate grammar/layout/indexing/ownership/bounds, permits neither nonlinear Bits<L*d> nor escaped limits.

## Lean boundary and acceptance

Bind/recheck original expressions/context/instantiation/endpoints, never producer flags/casts/hashes/submitted Lean code. Production equality needs closed checked certificate+theorem or concrete-natural reconstruction. Pinned4.30 omega lacks dark/grey shadows: failure/exhaustion means unproved. No native-evaluation fallback. n+1 convention follows Lean addition recursion; BitVec.cons/concat place bits differently, layout specified independently.

[Formal policy](formal-core.md) audits all private/generated/transitive declarations; [guards](../lean-kernel/Tests.lean) supplement audits, prove only existing atoms. Save first sources; specify parsing/domains/diagnostics/effects/owners/lowering/compatibility. Prove normalization/context/endpoints/encoding/inverses/reference and justify any new acceptance obligation. Test zero/commuted/doubled sums/guarded predecessors/missing or conflicting premises/products/bounds/fresh and empty owners; independently detect reordered axes/phase/drop/forgery. Six-bit leaves/QPE n,m1..8/combined16 unchanged. [Sized attempt](../tests/fixtures/authoring_sessions/sized-reshape-v021/session.json) rejected + in Bits<n+m>, not successful compilation.
