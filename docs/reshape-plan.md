# Explicit canonical reshape: the pre-sized-source experiment

Status, 2026-09-29: the review motivates a bounded 0.2.1 experiment before
shared `Bits<n>` source. The spelling below is a **desired-source draft**, not
an adopted grammar or a shipped standard API. The independent Lean helper
checks a single-owner adapter request; production integration remains pending.

```text
unitary fn flatten(q: Q<((Bit,Bit),Bit)>) -> Q<(Bit,Bit,Bit)> {
    reshape::<(Bit,Bit,Bit)>(q)
}
```

The intended author obligation removed is writing and exhaustively checking a
basis function just to regroup a register. Exact structural type equality stays
unchanged: source and destination are different types connected by an explicit
unitary conversion. This is not a license to accept an arbitrary implementation
whose input and output happen to have the same leaf types.

## Contract and counterexamples

For canonical prefix trees A and B, let L remove tuple constructors and `Unit`
leaves, retaining the ordered sequence of **complete atomic types**. Accept the
canonical adapter only when L(A) = L(B). `Bit`, `Bits(1)` and `Bits(0)` remain
distinct atoms. `Bits(0)` is not erased as Unit, nor is `Bits(2)` expanded into
two Bit leaves. Future basis atoms must retain their identity as well.

The request consumes exactly one `Q<A>` owner and returns one fresh `Q<B>`
owner, with exactly the same physical axes in exactly the same order. There
are no classical ports, measurements, allocations of physical qubits, gates,
phase parameters or arbitrary circuit bodies in this request. Unit factors
inside this single basis type may be inserted/removed explicitly; the owner
itself cannot disappear. In particular, this does not convert an ordinary
`(Q<Unit>,Q<Unit>)` product to `Unit`, merge its two owners or erase a frame.
Ordinary/mixed product adapters are outside this experiment.

The mathematical operator is the phase-fixed basis relabelling
`|x:A> -> |x:B>`, extended by identity on every reference system. With Qleisli's
first-field-low-axis convention, each non-Unit leaf contributes its label
times 2 to the power of the total width of all preceding leaves. Changing
brackets or inserting Unit contributes no new width or scalar. This gives
literal equality of encoded labels, not equality modulo phase.

Positive cases include nested/flat triples, inserted/removed Unit factors,
Unit-only trees, and regrouping intact sized atoms. Negative cases include
malformed prefix trees, changed atoms, exchanged axes (even for two Bit
leaves), duplicated axes, reused owner IDs, mismatched independently required
endpoints and resource-limit violations. An X gate, SWAP or scalar phase is
not a canonical reshape, even when its endpoint leaf sequences agree.

The type-leaf comparison traverses each prefix stream once and compares the
resulting leaves: linear in type storage, with no basis table or dense matrix.
The complete helper retains conservative quadratic charging for existing
well-formedness/uniqueness checks. This is not a claim that the entire compiler
or hierarchy verifier has linear complexity.

## Implementation boundary and adoption gate

The user's subsequent [linear-size and bit-segment decision](size-expressions.md)
adopts explicit `Bits<n+m>` to `(Bits<n>,Bits<m>)` reshape as the next design
extension. It changes segment boundaries while preserving the entire ordered
axis sequence; it is more than the intact-atom reassociation proved above.
Keep this existing helper and its public contract unchanged, and implement the
new adapter separately through checked structural operations. Arithmetic size
equality does not make those two basis type trees equal, nor authorize a bit
reversal, scalar phase or loss of an empty owner.

Linear size obligations, guarded subtraction, constant multiplication,
`n+1` recursive interfaces, normalization, proof transport and fail-closed
solver behavior are specified in that decision. The production grammar and
normalization/bit-segment acceptance theorems remain to be implemented.

The helper and its encoding proofs belong to the Mathlib-free executable Lean
package. Its result is ordinary checked adapter metadata, **not** a new
hierarchical rule, schema receipt or production evidence handle. A future
untrusted producer must expand the adapter through the existing explicit
split/join, Unit pack/unpack and checked tensor/sequence operations, retaining
complete endpoint bindings. The existing independent rule checker must check
those emitted operations. Convenience is not a reason to add a trusted rule.

Before adopting source syntax, specify parsing, name resolution, effects,
diagnostics and lowering, and perform the public Rust AST/API compatibility
review. Adding a public enum variant can require 0.3.0; this 0.2.1 experiment
does not do so. An inverse is the adapter with its two basis types exchanged;
the existing same-type `adjoint` source restriction is unchanged. No opaque
operation gains Apply, Adjoint or Controlled access from this helper.

The acceptance experiment preserves the desired source before its first check,
proves properties of the actual executable helper, and compares native results
against a separately implemented recursive Python tree encoder. Include
phase-sensitive coefficients with a reference, atom/axis/owner mutations and
exact budget boundaries. Source production, emitted-artifact conformance,
execution and H1–H5 remain separate adoption requirements.

Two focused `#guard_msgs in #print axioms` sentinels in
[kernel tests](../lean-kernel/Tests.lean) now pin the existing `check_encoding`
and `check_reference_coefficients` theorems to `propext` and `Quot.sound`.
They supplement the full compiled declaration audits and the CI regression
rejecting `native_decide`; they do not claim the future size solver is proved.

## Reading the review precisely

The reviewed bundled ordinary library has four files and 160 lines at this
snapshot; sealed operations and executable corpus projects are separate.
Handwritten QFT2/3 and finite contract checks do not establish a scalable
standard library. The review correctly identifies a useful next exercise.

The current sized profile is bounded (`n,m <= 8`, combined width <= 16).
Introducing that bounded source profile does not itself assert a theorem for
every natural size. A general scalable library needs compositional and, where
applicable, inductive proofs; structural label preservation can already be
proved generally while acceptance retains explicit resource bounds. Neither
this exercise nor the existing bounded QFT results completes those gates.

The access distinction is consistent with the circuit-model no-go for a
completely unknown controlled operation in
[Araújo–Feix–Costa–Brukner](https://arxiv.org/abs/1309.7976).
Its assumptions matter: a known circuit or extra implementation access is
different data. Likewise, exact deterministic *single-query* inversion of an
arbitrary unknown unitary must not be confused with all multiple-query
inversion: [Yoshida–Soeda–Murao](https://arxiv.org/abs/2209.02907) give an exact
deterministic qubit protocol with multiple calls. These are motivations for
access contracts, not proofs of the Qleisli compiler.

The associativity/unit coherence idea is used in this concrete ordered encoding.
We do not claim a formalization of Mac Lane's general theorem. Leaf equality
selects the canonical order-preserving adapter; it cannot certify every map
between those types. Permutations remain explicit operations.
