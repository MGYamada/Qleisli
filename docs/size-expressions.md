# Linear sizes and explicit register reshape

Adopted direction 2026-09-29, not a production symbolic solver/array/reshape API.
[Experimental source](sized-corpus-source.md) and current capacities/R14/H1–H5 stay separate.

## Existing intact-atom helper

[Reshape](../lean-kernel/QleisliKernel/Reshape.lean) checks canonical single-owner
adapter metadata, not arbitrary circuits. Remove tuple/Unit constructors to ordered
complete atoms; accept equal sequences, never split Bits(k). Bit/Bits(1)/Bits(0)
remain distinct. Consume one Q<A>, issue fresh Q<B>, preserve ordered axes with
coefficient +1/reference identity; no classical ports, allocation/gates/phase.
Unit factors may change inside this owner, including width zero, but no owner/frame
may vanish or merge. Reject malformed types, changed atoms/axes/owners/requests or
limits. Leaf comparison is linear; uniqueness charging remains conservatively
quadratic, not a compiler complexity proof. [First source](../tests/fixtures/authoring_sessions/reshape-v021/session.json)
and [native tests](../scripts/test_lean_reshape.py) retain scope; no production seal.
Future producers need explicit independently checked structural/tensor/sequence
operations and complete endpoints. Inverse swaps endpoints; same-type static adjoint
and opaque access restrictions do not broaden implicitly.

## Size arithmetic and equality

Natural constants/variables, addition, closed-constant multiplication and comparisons
=,!=,<,<= with Boolean connectives form the selected quantifier-free linear fragment.
2*n is permitted; symbolic L*d, symbolic exponentiation, calls, division/remainder,
max/min and quantifiers are outside initial grammar. a-b needs b<=a proved in the
static context before normalization; no wrap or silently truncated negative size.
Prefer recursive n+1 interfaces. Equality means validity under assumptions, not one
satisfying assignment; contradictory contexts issue no usable evidence. Generic and
concrete domain/profile checks remain separate; zero folds/powers still check bodies.

Normalize exact coefficients by stable binder identity/fixed variable order, combine
like terms/remove zeros and put constants last with deterministic association.
Precheck storage/work; guarded differences retain nonnegativity, never unsound Nat.sub
identities. No universal Lean definitional-equality claim. Proved equality reconciles
indices only for the same constructor via explicit transport; full type tree/order
and owner shape remain. Bits<n+m>, (Bits<n>,Bits<m>) and swapped factors differ;
Bit/Bits<1>, Unit/Bits<0> never coerce.

## Ordered bit-segment reshape

Separate future extension, not changed Reshape.check. Interpret Bit as one position,
Bits<e> as ordered segment and Unit as empty, comparing segment lengths without
per-bit expansion. Preserve complete axis order and non-bit atom identity. Consume
one Q<A>/return fresh Q<B>; owner splitting is an additional explicit operation.
Zero fields retain positions/owners and Unit/Bits<0> distinction.

```text
x = low + 2^n * high
low = x mod 2^n, 0 <= low < 2^n
high = x div 2^n, 0 <= high < 2^m
0 <= x < 2^(n+m)
```

Relabelling coefficient +1/zero otherwise extends by identity on every reference;
prove encoding, both inverses and reference preservation without dense tables.
Hilbert dimension exponentiation is not type-level grammar. Bits<n+1> to
(Bit,Bits<n>) selects the low bit; (Bits<n>,Bit) partitions the same axes differently,
not moving the first bit. Reversal/SWAP/scalar phase remains explicit. Nested arrays
[Bits<d>;L] are a future structural direction with separate grammar/indexing/layout/
ownership/bounds; they neither permit nonlinear Bits<L*d> nor evade wire limits.

## Lean boundary and library convention

Bind original expression/context/instantiation/full endpoints, independently recheck
acceptance obligations. Producer flags/casts/hashes are not evidence; never execute
submitted Lean code/tactics/imports. A production solver needs a closed checked
certificate and acceptance theorem or direct concrete-natural reconstruction.
omega is useful kernel proof search, but pinned4.30 omits dark/grey shadows; failure/
exhaustion means unproved, not inequality. No native-evaluation axiom/fallback grants
acceptance. n+1 and variable-before-constant emission suit Lean's second-argument
addition recursion; BitVec.cons/concat both return n+1 but place bits at opposite ends,
so low-axis layout is independently specified.

Global compiled audits cover private/generated/transitive axioms, permitting only
propext/Classical.choice/Quot.sound. Keep source bans on native_decide/decide +native
and CI transport-fault rejection; focused axiom guards supplement rather than replace
audits. [Kernel guards](../lean-kernel/Tests.lean) cover existing intact-atom results,
not future segment/normalization theorems.

## Implementation and acceptance packet

Preserve desired sources before checks; specify parsing/domains/equality diagnostics,
ownership/effect/lowering and compatibility. Prove normalization evaluation and actual
context/endpoints, encoding/inverses/reference; identify any existing-core semantic
obligation that structural operations cannot express before extending acceptance.
Test zero sizes, n+1/1+n/commuted/doubled sums, guarded predecessors, missing/conflicting
premises, unsupported products, bounds/fresh/empty owners; detect swapped/reversed
axes, extra phase, dropped owner and forged evidence with independent small encoders.
Six-bit leaf, positive QPE n/m1..8, combined16 wires and all gates remain unchanged.
[Original attempt](../tests/fixtures/authoring_sessions/sized-reshape-v021/session.json)
rejects + in Bits<n+m>; it claims no successful sized reshape compilation.
