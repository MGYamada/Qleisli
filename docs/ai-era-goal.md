<a id="第1開発目標-ai時代の量子言語"></a>

# Development goal 1: a quantum language for the AI era

Status: **adopted long-term development goal** (2026-09-26). This English
edition is authoritative for this goal and replaces the earlier Japanese text
without changing its mathematical premises or guarantee boundaries. It does
not introduce accepted syntax or establish an implementation soundness theorem.
The original 2026-09-26 status described a partially implemented
[Rust IR verifier and reference executor for closed IR](ir-prototype.md),
with type rules, soundness theorems, and the `.qli` implementation still
incomplete. Subsequent progress in the declared finite profile is recorded
below; the general implementation proofs remain open.

This goal develops the [adopted design principles](design-philosophy.md) from
the perspective of an era in which AI writes code. The same rules apply to
human-written and AI-generated `.qli`.

**Project north star (2026-09-27):** make the language people use to think
about quantum algorithms coincide with the language they use to write
programs. Goal 1 provides the foundation on which humans and AI can use the
same contracts, by checking the correspondence between program concepts and
their implementations. This direction and the release conditions below
follow the authoritative [release milestones](release-milestones.md).

> Qleisli aims to pass generated quantum programs through type, effect, and
> ownership checking and verified IR, and to show at compile time which
> soundness guarantees have been established.

The [second development goal](algorithm-structure-goal.md) extracts common
structures from representative algorithms and develops reusable components
inside this verification boundary. The [Layer 3 plan](stdlib-roadmap.md)
collects those components into a standard vocabulary with semantic contracts.
The three layers—verification foundations, structure extraction, and the
standard library—share one trust boundary.

The 2026-09-30 [Resource Safety adoption](resource-semantics.md) adds a third
theorem pillar alongside Soundness and Physical Realizability: finite static
resource bounds preserved through compilation for the supported profile.
This is a future **to prove** obligation, not a present consequence of typing
or ownership checking. Resource accounts should compose with meanings/effects;
AI-generated cost annotations receive no authority without checking.

AI can propose code and proofs. Acceptance rests on derivations checked by
the compiler and on IR constructors and evidence, not on a proposal's origin
or accompanying explanation. Operations that cannot be checked receive no
special treatment based on who generated them. Diagnostics should identify
the failing resource, effect, or evidence and its source location.

**Authoring priority (2026-09-28):** expand executable `.qli` components,
examples and source-level semantic regressions before adding abstractions.
Record concrete writing failures and workarounds in the
[authoring report](qli-authoring-feedback.md); use the checked
[quick reference](qli-quick-reference.md) as the concise LLM/human entry point.
Judge convenience by obligations removed and evidence retained. A successful
authoring session is not a measured model benchmark or a protocol proof.

The [adopted development method](design-philosophy.md#start-with-the-quantum-programs-we-want-to-write)
starts with quantum programs as they ought to be written, then grows the
language with AI to express and check them. Keep desired-source drafts distinct
from implemented syntax. The [fixed three-source corpus](../corpus/README.md)
provides executable translations and concrete authoring evidence for that cycle.

<a id="v01-と-v1-の到達条件"></a>

## v0.1 and v1 acceptance conditions

As **release goals adopted by the user on 2026-09-27**, the
[v0.1 minimum semantic-contract conditions](release-milestones.md#v01-minimum-semantic-contracts)
are the first version milestone for Goal 1. This section summarizes the
authoritative release plan; adopting a goal does not declare completed
implementation, proof, or a new mathematical invention.

For isometric encodings `E_in, E_out` from finite-dimensional logical spaces
to implementation spaces, an ideal pure implementation operator `U`, and a
logical operation `u` fixed by a public specification, connect the equation
`U E_in = E_out u` to checkable finite semantic evidence. The v0.1 minimum
requires substitution of implementations satisfying the same contract and
independent rechecking of IR and evidence, regardless of their producer.
Check the input encoding, phase, and ownership; an AI explanation is not
evidence. This plan starts with pure-operation contracts. The equation alone
does not guarantee observation semantics or general algorithm correctness.

The [concrete v1 acceptance target](release-milestones.md#v1-north-star-textbook-algorithm-structure)
is that Shor, QPE, and Grover can be read in their textbook quantum-algorithm
structure. These three actual source programs assess the north star. Preserve
the priority of the finite-core specification, proofs, and IR correspondence:
the v0.1 meaning contracts come first. Sized types, operation parameters, and
standard vocabulary then support v1 programs on that verification foundation.

The [bounded exact checker and three-argument auxiliary form](semantic-contracts-v0.1.md)
have been connected to [public function contracts and final-IR evidence](function-contracts-v0.1.md),
implementing and checking v0.1's declared finite profile. v1 remains unmet.
Current validation results belong in the [conformance ledger](specification-status.md).
Neither AI explanations nor successful finite examples replace a general
soundness proof.

The [imaginary Qleisli 1.0 code prerequisite](release-milestones.md#pre-v020-imaginary-v1-code)
was adopted before v0.2.0: write all six initial drafts and their necessary
meaning contracts and open questions before implementing generalization.
Use the drafts with AI to make missing abstractions and checking methods
concrete. They need not compile and may be revised; their origin and
explanations are not verification evidence. The
[six drafts and requirements index](imaginary-v1/README.md) and semantic
review now exist. This completes the prerequisite concerning initial
artifacts and recorded requirements, not verified language features or a
general soundness guarantee. The [language evolution framework](language-evolution.md)
preserves that distinction when selecting subsequent specifications.

<a id="保証の階層"></a>

## Levels of guarantees

| Level | Intended guarantee | Checking boundary |
| --- | --- | --- |
| 1. Resource safety | Reject operations on unowned wires, repeated use of the same ownership, reuse of a measured handle, unhandled quantum ownership, and protected-region conflicts. Conflict checking for general borrowing is a goal for future signatures and syntax. | Type, effect, and ownership checking, with IR linear-token verification. |
| 2. Quantum soundness in ideal semantics | Pure `iso` operations are isometries, `unitary` operations are unitaries, and programs containing observation denote valid quantum instruments. | Sealed primitive meanings, injective lifts, phase, separation evidence, effectful composition, and verification of IR semantics. |
| 3. Protocol correctness | For example, a teleportation output preserves the input's quantum information. | A protocol-specific specification and additional proof obligations; basic types do not automatically establish this property. |
| 4. Algorithm correctness | Produce the intended answers or satisfy the required success probability. | Algorithm-specific mathematical proof, analysis, and validation; type checking alone is insufficient. |

At Level 1, the ownership checker rejects `(q,q)` as duplicated ownership.
That alone is not a proof that no machine can clone arbitrary unknown states.
Level 2 requires primitive semantics and evidence of separation for pure
auxiliary release. Matching input and output wire sets cannot by itself detect
correlations lost inside an implementation.

<a id="目指す健全性定理"></a>

## Intended soundness theorem

For the initial finite, terminating core, use the following conceptual
judgment. `Γ` is a classical context, `Δ` a quantum-ownership context, and
`ε` an effect in `Unitary ≤ Iso ≤ Observe`; *pure* abbreviates the first two.
This is whole-computation shorthand based on the
[projection of mixed source values](source-semantics.md#1-mixed-values-and-ordered-quantum-interfaces),
not a convention that treats only an expression's residual environment as
the quantum output.

```text
Γ ; Δin ⊢ P : B ; Δout ! ε
```

The intended theorem has these premises: sealed primitives have the specified
valid meanings; injective lifts and the zero-return conditions of structured
`ComputeUseUncompute` are verified; and composition obeys the type/effect
rules. For each classical input `γ` and outcome `b : B` in the finite
classical result type `B`, it states that
`⟦P⟧_{γ,b} : L(H(Δin)) -> L(H(Δout))` is completely positive and
trace-nonincreasing, and that `Σ_b ⟦P⟧_{γ,b}` is trace preserving. This
family of maps is a quantum instrument. Retaining the classical outcome
gives a CPTP map to a classical–quantum output; forgetting the outcome by
summing the maps also gives a CPTP map. When a closed `main` has no quantum
input or output, its meaning is a normalized probability distribution over `B`.

Separately establish `V†V = I` for a pure `iso fn`, and additionally
`VV† = I` for a `unitary fn`. The theorem premises, typing preservation,
meanings of all IR constructors, and composition lemmas are responsibilities
of Stages 1 and 2. The [finite-core formalization](formal-core.md) records
the current theorem statements and proof outline. A
[paper proof of Q1–Q3](source-soundness.md) exists for the mathematical
source-rule system. General correspondence with Rust acceptance and IR
translation, and an implementation soundness guarantee, remain unproved.

This guarantee concerns ideal language semantics. External-backend
capabilities, hardware noise and calibration, and the outcomes of a specified
protocol or algorithm require separate validation. Adding unchecked external
operations or postselection in a future version requires restating the
theorem's premises and conclusions.

<a id="ai-を含む開発の流れ"></a>

## Development workflow involving AI

1. A human or AI proposes `.qli` and, where needed, an individual specification.
2. The frontend checks types, effects, and ownership, and generates typed IR
   with evidence.
3. The IR verifier independently rechecks wire linearity, constructors, and
   evidence without trusting the producer.
4. Only accepted programs go to the reference executor or a backend whose
   capabilities have been checked. Protocol claims have separate validation
   results.

Do not accept AI-generated explanations or proof prose as evidence when the
verifier cannot understand it. Aim for diagnostics with source locations that
help revise AI proposals, together with machine-readable checking results.
Keep the checking kernel small and document its trust boundary.

<a id="到達判定"></a>

## Acceptance criteria for this goal

- Specify accepted/rejected examples, resource preservation, and the meanings
  of pure and observing operations unambiguously in the
  [language specification](language-spec.md).
- Following the [roadmap](../ROADMAP.md), verify every typed-IR constructor
  and reject invalid linear use, effect violations, and release without evidence.
- Prove the finite-core theorem above and establish that the implemented
  checker meets its premises before claiming that compilation success
  guarantees soundness.
- Compare expected Bell-state, partial-measurement, phase-oracle, and
  measurement-feedback results with the reference executor. Keep these
  example checks distinct from a general soundness proof.

[QWIRE](https://arxiv.org/abs/1803.00699) is prior work combining linear-wire
typing with density-operator semantics; the
[Proto-Quipper formalization](https://arxiv.org/abs/1812.03624) is prior work
formalizing linear-type soundness. Qleisli's goals and theorem statements do
not claim that these results have already been implemented in Qleisli.
