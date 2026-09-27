<a id="qleisli-が量子プログラミング言語として満たす条件"></a>

# Requirements for Qleisli as a quantum programming language

Status: **adopted design requirements** (2026-09-26). These are conditions
**imposed on the specification and implementation**. This English edition
is authoritative for those requirements and replaces the earlier Japanese
text without changing their meaning. It introduces no new source syntax,
API, implementation, or proof claim. The [finite-core v0 specification](language-spec.md)
fixes its scope and rules in accordance with these requirements, but general
soundness and implementation-correspondence proofs remain incomplete;
the requirements are not all proved implementation guarantees.

As consequences of the [adopted design principles](design-philosophy.md),
the Stage 0 standard-library design, Stage 1 language specification, and
subsequent Rust implementation must satisfy the same requirements.
The [language evolution framework](language-evolution.md) preserves them
when distinguishing proposed extensions from the accepted language.

<a id="意味論と純粋性"></a>

## Semantics and purity

**Q1. Coherent pure operations.** Interpret a finite basis type `A` as
`H(A) = C^(A)`. The meaning `V : H(A) -> H(B)` of an `iso fn` must satisfy
`V†V = I_A` on the whole input space; a `unitary fn` must also satisfy
`VV† = I_B`. Preserve global phase in IR and controlled composition. Pure
functions are total and terminating; initial-version iteration is statically
finite. Do not expose arbitrary `bind` from the free-vector-space monad as
an execution API.

**Q2. Functional execution model.** Top-level `.qli` declarations perform
no quantum operations when loaded and contain no implicit mutable quantum
state or I/O. Programs compose effectful transformations of classical values
and quantum ownership. Source `Q<A>` is an ownership type, not a computation
effect type. The explicit `observe` effect accounts for measurement
probabilities; host display, file access, and device operations are separate.

<a id="量子資源と補助系"></a>

## Quantum resources and auxiliary systems

**Q3. Ownership and nonduplication.** `Q<A>` is the linear right to operate
on a logical register. Reject duplicated ownership, repeated specification
of one wire, implicit discard, and use after the ownership's lifetime ends.
Physical discard is explicit as `observe::discard`. `split/join` rebind
handles; they do not assert that split registers form a product state.
v0 has no general borrowing syntax. It checks the capture prohibition in
restricted auxiliary computation and disjointness of protected regions and
target wires in raw IR. General borrow signatures and their conflict rules
belong to subsequent specifications.

**Q4. Sharing basis information.** A coherent basis label is not a measured
classical `CBit`. Allow the linear extension of the injective map
`x -> (x,x)`, but do not allow duplication of `Q<A>` itself. Do not lift a
noninjective map, such as the constant map `x -> 0` from `Bit -> Bit`, into
a pure quantum operation.

**Q5. Auxiliary-bit release.** Pure release requires static evidence that
the auxiliary returns to `|0⟩` and separates from the rest for every input
and every reference system. In the original restricted
`compute; use; uncompute` form, `use` is restricted to a unitary preserving
the source and auxiliary basis labels. The
[finite semantic-contract extension](semantic-contracts-v0.1.md) independently
checks `W E_f=E_f u` exactly for the actual circuit `W` and the explicit
logical operation `u`. It also permits operations that change both registers
while preserving the computed relation. Both forms reject measurement,
reset, or discard of protected resources. This does not implement general
borrowing, and a borrow lifetime alone is not evidence of zero return.

<a id="観測と制御"></a>

## Observation and control

**Q6. Separate irreversible operations.** Measurement, reset, and discard
of arbitrary states have effect `observe`. Interpret `observe` as a family
of completely positive maps indexed by classical outcomes, whose sum is
trace preserving. Subsystem measurement acts on the entire, possibly entangled
system. The initial interface `measure_z : Q<Bit> -> CBit` consumes logical
ownership of the measured subsystem and returns no new quantum handle.
Reset and discard explicitly lose correlations. Reusing a physical device
is handled by preparing a different logical wire and assigning it in the
backend.

**Q7. Two kinds of branching.** Each arm of classical `if` exclusively
receives the same linear context and returns compatible ownership.
Coherent `qif` retains the control qubit and requires unitary branches on
the same target type. Preserve relative phase between branches under
controlled composition. Classical branching does not itself mean measurement.

<a id="実行できる言語としての条件"></a>

## Requirements for an executable language

**Q8. Minimum expressiveness.** The initial version must express known-state
preparation, gates producing interference, entanglement, phase oracles from
basis functions, measurement of part of an entangled system, and feedback
from measurement results. A closed `main` returns a classical result and
leaves no quantum ownership.

**Q9. Checkable boundary.** Ordinary standard-library `.qli` definitions
obey the same type/effect rules as user code. Primitive gates, injective lifts,
measurement, ownership-structure operations, and certified release must go
through sealed built-in operations or checked language forms. The IR verifier
checks validity of evidence, not just its presence. The reference simulator
must execute the accepted initial core; external backends must reject
unsupported features or provide meaning-preserving translations.

**Q10. Boundary between ownership and correlations.** An ownership context
represents exclusive rights to operate; separate ownership does not imply a
product state. Local gates, partial measurement, reset, and discard must
have the correct meaning on the possibly entangled whole system and any
reference. Use Q5's separation evidence for pure auxiliary release and Q6's
`observe` effect to discard correlations. Finite core v0 adopts whole-system
interpretation of local operations and restricted auxiliary evidence.
Proving soundness, including its function boundaries, remains a
[central Stage 1 obligation](design-philosophy.md); general evidence
signatures belong to subsequent specifications.

**Q11. Conditions for soundness claims.** Establish resource safety for the
finite, terminating core's type rules. Show that accepted programs denote
quantum instruments with classical outcomes, assuming valid sealed
primitives, checked injective lifts and auxiliary release, and composition
following the effect rules. Until the frontend and IR verifier's acceptance
conditions are shown to meet those theorem premises, do not describe
compilation success as proved physical validity. The
[development goal](ai-era-goal.md) states the intended theorem and the
properties it does not guarantee.

<a id="判定に使う例"></a>

## Examples for acceptance decisions

| Expected decision | Example | Main requirements |
| --- | --- | --- |
| Accept | `do x <- q; pure (x,x)` | Q1, Q3, Q4 |
| Accept | `C_f; Z; C_f†` using an auxiliary bit | Q1, Q5 |
| Accept | Measure one half of a Bell pair and use the remainder | Q3, Q6 |
| Accept | Explicitly discard one half of a Bell pair and treat the remainder as mixed | Q6, Q10 |
| Accept | Select `X` using a measurement outcome | Q6, Q7 |
| Reject | `(q,q)` or `do x <- q; pure 0` | Q1, Q3, Q4 |
| Reject | Measure a protected resource in restricted auxiliary computation, or discard an auxiliary without evidence in a purported pure computation | Q5, Q6 |
| Reject | Purely release half of a Bell pair based only on its ownership | Q5, Q10 |

<a id="参考となる先行仕様研究"></a>

## Relevant prior specifications and research

- [QML: A functional quantum programming language](https://people.cs.nott.ac.uk/psztxa/publ/qml.pdf):
  finite types, sharing of basis information, coherent branching, and
  irreversible operations.
- [Qurts: Automatic Quantum Uncomputation by Affine Types with Lifetime](https://arxiv.org/pdf/2411.10835):
  lifetimes and auxiliary uncomputation.
- [OpenQASM 3.1 quantum instructions](https://openqasm.com/versions/3.1/language/insts.html)
  and [QIR Adaptive Profile](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Adaptive_Profile.md):
  mid-circuit measurement, reinitialization, and differing device capabilities.
