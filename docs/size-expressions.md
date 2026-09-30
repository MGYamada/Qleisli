# Linear size expressions and explicit register reshape

Status: **adopted design direction for the 0.2.1 continuation, 2026-09-29**.
This extends the intact-atom helper below and the G020-1 sized-source
specification packet; the remaining continuation is [0.2.2](v0.2.2-plan.md). Source grammar, a production size solver,
array types and sized reshape lowering are not implemented by this decision.
The existing concrete profile, compatibility policy and R14/H1–H5 gates remain.

## Existing intact-atom helper

The Mathlib-free [Reshape checker](../lean-kernel/QleisliKernel/Reshape.lean)
checks canonical single-owner adapter metadata, not arbitrary circuit bodies.
For ordered prefix types A/B, remove tuple constructors and Unit factors to
obtain L(A)/L(B); accept only equal sequences of complete atomic types.
Bit, Bits(1) and Bits(0) remain distinct atoms, and Bits(k) is never split into
Bit leaves. The request consumes one Q<A> and returns one fresh Q<B> with
identical ordered physical axes, no classical ports, measurement, physical
allocation, gate or phase parameters. Unit factors may change within that
basis tree; the owner remains, including at width zero. This does not erase
ordinary products of owners, merge owners or drop a frame.

Its operator is exactly `|x:A⟩ → |x:B⟩`, with coefficient +1 and unchanged
encoded labels under the first-field-low-axis convention, extended by identity
on every reference. Equal endpoint leaves cannot certify an arbitrary X, SWAP
or scalar phase. Reject malformed trees, atom/axis changes, reused owners,
mismatched independently requested endpoints and capacity excess. Type-leaf
comparison is linear in type storage; existing well-formedness/uniqueness work
retains conservative quadratic charging, without a claim about whole-compiler
complexity.

The [saved first source](../tests/fixtures/authoring_sessions/reshape-v021/session.json)
and [native differential tests](../scripts/test_lean_reshape.py) retain the
experiment and mutations. These metadata proofs issue no production evidence
or new hierarchy rule. A future untrusted producer must emit existing explicit
split/join, Unit pack/unpack and checked tensor/sequence operations; independently
check their complete endpoints and actual artifact. Source grammar, effects,
diagnostics, execution, compatibility and H1–H5 integration remain open.
The inverse exchanges A/B; the existing same-type adjoint restriction and
opaque-operation capability requirements remain unchanged. The following
bit-segment design is a separate extension, not a broadened Reshape.check.

## Size arithmetic and equality

Static sizes range over natural numbers. Select quantifier-free linear
arithmetic for size obligations: natural constants and size variables,
addition, multiplication by a closed natural constant, and comparisons
`=`, `!=`, `<`, `<=`, combined by Boolean connectives. Size expressions may
not multiply two symbolic variables, exponentiate a symbolic exponent or call
an arbitrary user function. Multiplication with a statically evaluated closed
constant is linear; `2*n` is permitted, `L*d` with two parameters is not.

Subtraction in a size expression is guarded: `a-b` requires a proof of
`b <= a` in the current static context before normalization. It denotes the
natural difference on that domain, never wrapping or silently treating a
negative size as zero. This is a chosen source restriction, distinct from
Lean's total, truncated `Nat.sub`. Recursive library interfaces should prefer
`n+1` with residual size `n`. Division, remainder, symbolic maxima/minima and
quantifiers are outside the initial expression grammar; later additions need
their own specification even where Presburger arithmetic can express them.

Equality is validity under the declared static assumptions, not satisfiability
at one convenient assignment. For example, `n+m = m+n` is valid; `n+1 = m`
needs a corresponding premise. A contradictory static context must not issue
evidence for a usable instantiation. Generic body obligations and each concrete
instantiation's domain/profile checks are separate. An empty fold or zero power
still checks its actual body and does not discharge missing ownership evidence.

Normalize coefficients using stable binder identities and a fixed variable
order; combine like terms, remove zero coefficients and place the constant
term last. Use exact arithmetic, with explicit storage/work limits checked
before expansion. For nonnegative affine sums, emission uses a deterministic
association with the final constant as the last addition operand, preserving
`n+1`. Guarded differences retain nonnegativity obligations rather than being
rearranged using unsound truncated-subtraction identities. No claim is made
that all propositionally equal expressions become definitionally equal in Lean.

For the same type constructor, proved size equality may reconcile its size
indices, with explicit proof transport in Lean. Structural type equality still
compares the constructor, tuple arity/nesting and complete fields. Thus
`Bits<n+m>` and `Bits<m+n>` can share a size after arithmetic checking, while
`Bits<n+m>`, `(Bits<n>,Bits<m>)` and `(Bits<m>,Bits<n>)` remain different basis
type trees. `Bit` and `Bits<1>` also remain distinct. There is no implicit
register split, tuple flattening, owner conversion or wire permutation.

## Ordered bit-segment reshape

The earlier helper treats `Bits(k)` as an intact atomic leaf. This adopted
extension is a separate, explicit bit-segment adapter; do not silently broaden
the existing `Reshape.check` predicate or relabel its current proof.

For `Unit`, `Bit`, `Bits<e>` and their ordered products, interpret `Bit` as one
Boolean position and `Bits<e>` as an ordered segment of e positions. Tuple
association and segment boundaries may change explicitly, but the complete
ordered sequence of physical axes must be identical. Compare segment lengths
symbolically without expanding one leaf per bit. Future non-bit basis atoms
must retain their identity and order; equal total dimension is insufficient.

The initial adapter consumes one `Q<A>` and returns one fresh `Q<B>`. It may
convert `Q<Bits<n+m>>` to `Q<(Bits<n>,Bits<m>)>` when the size proof and complete
endpoint checks pass. Returning two separate quantum owners requires the
existing explicit split operation. Zero-length fields retain their positions
in the type; a zero-width owner cannot disappear. Preserve Unit/Bits<0>
distinctions and require explicit operations when creating or consuming owners.

With the first field on the low axes, the register-label equation is

```text
x = low + 2^n * high,
low  = x mod 2^n,       0 <= low  < 2^n,
high = x div 2^n,       0 <= high < 2^m,
0 <= x < 2^(n+m).
```

The coefficient is exactly +1 on this relabelling and zero otherwise; extend
it by identity on every reference. Prove the encoding equation, both inverse
laws and arbitrary-reference preservation. Exponentiation here describes the
mathematical Hilbert-space dimension, not a permitted type-level size expression.
Unbounded local algebraic theorems do not enlarge the concrete acceptance profile.

`Bits<n+1>` can therefore be explicitly split into `(Bit,Bits<n>)`, with the
first bit on the low axis. A reshape to `(Bits<n>,Bit)` partitions the same
ordered axes at a different boundary. It does not move the first bit to the
last axis. QFT output reversal, SWAP and other permutations remain explicit;
neither commutativity of size addition nor equality of bit counts proves their
meaning. A scalar phase is likewise never part of reshape.

For rectangular data, select nested array structure such as `[Bits<d>; L]` as
the design route instead of introducing `Bits<L*d>` into size arithmetic.
Array grammar, ownership, indexing, encodings and bounds require a separate
extension; this notation is not yet a source API or part of the required 0.2.1
QPE deliverable. Flattening such an array needs an explicit independently
checked layout and concrete resource accounting. Array shape does not make its
total physical width magically linear or remove the profile's wire limit.

## Lean boundary and library convention

The frontend may normalize or search for a size proof, but its success flag,
cast, hash or generated source is not evidence. Bind the original expression,
static context, concrete instantiation and both complete endpoints; independently
recheck every obligation that affects acceptance. Never execute producer-supplied
Lean code, tactics, imports or attributes as an artifact-verification mechanism.
The executable core remains Mathlib-free; Lean elaboration tactics belong in
audited proof development. A production symbolic solver needs a closed checked
certificate format and an acceptance theorem, or the concrete hierarchy must
reconstruct and check the instantiated naturals itself.

Lean's `omega` produces ordinary kernel-checked proofs and is useful for these
obligations. Decidability of Presburger arithmetic does **not** imply that the
pinned tactic proves every valid formula: the Lean 4.30.0 implementation omits
the dark/grey-shadow cases of the full procedure. Solver failure or exhaustion
means **unproved/unsupported**, not mathematical inequality. No native-evaluation
axiom or unchecked fallback may turn that failure into acceptance. See the
[pinned implementation](https://github.com/leanprover/lean4/blob/v4.30.0/src/Lean/Elab/Tactic/Omega.lean).

Use `n+1` in recursive stdlib interfaces and variable terms before constants in
generated Lean expressions. Lean's addition recurses on its second argument;
this convention makes the successor case convenient, but it is not a proof
of a universal cast-elimination property. `BitVec.cons` and `BitVec.concat`
both return `BitVec (n+1)` while placing the new bit on opposite ends. Choose
them according to the documented low-axis convention, independently of size
normalization. See the [pinned bitvector definitions](https://github.com/leanprover/lean4/blob/v4.30.0/src/Init/Data/BitVec/Basic.lean).

The existing compiled audits inspect every project declaration and transitive
axiom dependency, including generated/private helpers, allowing only
`propext`, `Classical.choice` and `Quot.sound`. Preserve these audits and the
existing CI mutation that rejects a transport theorem using `native_decide`.
Focused `#guard_msgs in #print axioms` regressions may pin the key size and
reshape theorems, but do not replace the global compiled audit. The source
policy also bans both `native_decide` and `decide +native`; see
[proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

## Implementation and acceptance packet

1. Preserve desired split/merge, recursive-QFT and QPE concatenation sources
   before checking. Specify G020-1 parsing, domains, equality diagnostics,
   ownership, effect and lowering; classify the explicit reshape spelling and
   review compatibility before adding any public AST/IR variant.
2. Prove normalization preserves size evaluation and that accepted obligations
   bind the actual context and endpoints. Prove the ordered bit-segment adapter's
   label and reference equations without dense tables. Pin these actual
   theorems' allowed axioms in CI after implementation.
3. Generate existing structural/tensor/sequence operations from the untrusted
   adapter. Where existing operations cannot express a required conversion,
   identify the missing semantic obligation and design/prove a compatible
   extension explicitly; convenience alone is not an acceptance rule.
4. Check n or m equal to zero, `n+1` versus `1+n`, commuted sums, doubled sizes,
   guarded predecessors, mismatched widths, unsupported `L*d`, missing premises,
   contradictory contexts, exact resource boundaries, fresh owners and complete
   axes. Retain faults that reverse bits, swap equally sized fields, drop an
   empty owner, add phase or forge a size certificate. Compare small instances
   against an independent encoder and retain phase/reference correlations.

The existing six-bit leaf bound, selected positive QPE n,m in 1..8, combined
16-wire cap, zero-width ownership rules and all release/proof gates remain in
force. The QFT convention must be tested on nontrivial basis/superposition inputs;
an all-zero output or matching dimensions is not evidence of correct bit order.

The [preserved first source](../tests/fixtures/authoring_sessions/sized-reshape-v021/session.json)
contains split/merge, `n+1` and `2*n` examples. Its actual first check rejects
`+` in `Bits<n+m>`; no successful sized compilation is claimed. Existing
`Reshape.check_encoding` and `check_reference_coefficients` now have focused
axiom guards in [kernel tests](../lean-kernel/Tests.lean). They cover the intact-atom
helper, while the new size and segment theorems remain implementation obligations.
