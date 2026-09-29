<a id="qleisli-の設計思想"></a>

# Qleisli design principles

Status: **adopted design principles** (2026-09-26), with release-direction
additions dated 2026-09-27, a trusted-core boundary adopted on 2026-09-28,
and the Rust type/ownership default and standard-library goal adopted on
2026-09-29.
This English edition is authoritative for these
principles and replaces the earlier Japanese text without changing them.
Adopting the principles does not finalize syntax or establish a mathematical
soundness theorem. Concrete type rules, standard APIs, and IR are specified
from Stage 1 onward in accordance with these principles. The
[finite-core specification](language-spec.md) defines the current source
rules; the [language evolution framework](language-evolution.md) separates
future design from accepted syntax and implementation.

**Project north star (2026-09-27):** make the language people use to think
about quantum algorithms coincide with the language they use to write
programs. State preparation, oracles, reflections, phase estimation,
uncomputation, and their composition and assumptions should be expressed in
actual source. Checking the connection between these concepts' meanings and
their implementations is part of this goal. The release-policy summaries
below follow the authoritative [release milestones](release-milestones.md).

## Standard library as foundation, textbook and formal specification

**Library goal fixed by the user on 2026-09-29:** build a BLAS/LAPACK-like
foundation for quantum computing that integrates reusable computational
components, a textbook of quantum information and formal specifications.
Readers should be able to learn quantum information by reading the standard
library. The [authoritative library goal](stdlib-roadmap.md#adopted-library-goal)
connects concepts and derivations, readable implementations, examples,
contracts and explicit verification/proof status.

This fixes the purpose of the library. Comprehensive module organization and
generalized APIs remain separate design decisions; existing specified APIs and
the trusted-core boundary remain in force. Adopting this goal does not assert
that today's library already provides complete teaching material or proofs.

## Follow Rust for type and ownership discipline

**User decision, 2026-09-29: when uncertain about type or ownership discipline,
follow Rust.** Rust is the default reference for type identity, tuple arity and
nesting, moves, bindings and scopes. Do not introduce a different convention
merely because a representation or compiler implementation makes it convenient.
The [type contract](type-system.md) records current Qleisli rules and the
intentional differences from Rust.

A difference must identify the quantum-semantic or evidence obligation that
requires it, specify acceptance/rejection rules and have corresponding checks.
Quantum owners remain linear: no copying or implicit discard, and pure auxiliary
release requires zero-return/separation evidence. Applying the Rust default
does not weaken those obligations. Rust syntax or features not yet specified
and implemented in Qleisli remain future extensions, not implicit APIs.

The [linear-size decision](size-expressions.md) is an explicit adopted
extension: independently checked size arithmetic supports register contracts
and ordered reshape. It does not inherit Rust const-expression acceptance,
alter tuple identity or make isomorphic basis types implicitly equal.

The user's wording, as a supporting Japanese statement of the English policy:

> type/ownershipの規律に迷ったらRustに従う。

## Start with the quantum programs we want to write

**Development method adopted by the user on 2026-09-28:** first write quantum
programs that express how the algorithms ought to be written; then develop,
together with AI, a language capable of expressing and checking those programs.
The desired program and its mathematical contract lead the design. Existing
parser limitations should not silently define the ideal algorithm vocabulary.

Keep both the intended source and an executable version in the current finite
language where possible. Compare them to discover missing abstractions,
repeated author obligations and poor diagnostics. Retain failed attempts and
counterexamples, specify the proposed meaning and evidence obligations, and
then implement and validate the smallest justified language or library change.
Repeat this cycle on concrete algorithms with AI as a collaborator.

The user selected [code-driven development from 0.2.0 onward](code-driven-development.md),
after completing the finite B019 foundation in 0.1.x. That procedure records
existing desired/current sources, obstacles, independent acceptance experiments
and bounded work packets. It does not replace the specification or evidence
gates with successful authoring alone.

Desired source may be an explicitly labelled, unimplemented design draft;
it is not accepted syntax or proof of a supported algorithm. Executable
translations in the [three-source input corpus](../corpus/README.md) and the
[imaginary-v1 drafts](imaginary-v1/README.md) serve different roles in this
process. Neither AI authorship nor an attractive notation can bypass the
trusted-core boundary, mathematical premises or release acceptance criteria.

The user's formulation, retained as a supporting Japanese statement of the
English policy above:

> 「こう書けるべきだ」という量子プログラムを先に置いて、それを書ける言語をAIと育てていく。

> Qleisli is a functional quantum language that treats quantum data as owned
> resources that cannot be duplicated. Programs compose effectful
> transformations of classical values and quantum resources. Coherent
> transformations of quantum systems are interpreted as isometries,
> transformations involving observation as quantum instruments, and
> irreversible discard is explicit.

**Release goals adopted on 2026-09-27:** the user selected implementation
substitution through finite evidence for the meaning contract
`U E_in = E_out u`, together with independent IR checking, as the
[v0.1 minimum conditions](release-milestones.md#v01-minimum-semantic-contracts).
This contract relates an ideal pure implementation operator `U` to a logical
operation `u` fixed by its public specification, through isometric input and
output encodings `E_in, E_out`. It preserves the principle that ownership alone
does not establish correlations or separation. Check conformance to the input
encoding separately from linear ownership of quantum resources. This adoption
record follows the release plan; it does not claim a new theory or completed
implementation or proof merely from adopting a goal.

The [concrete v1 acceptance target](release-milestones.md#v1-north-star-textbook-algorithm-structure)
is that Shor, QPE, and Grover can be read in their textbook quantum-algorithm
structure. These three actual source programs assess the north star. The
finite-core specification, proofs, and IR correspondence, together with v0.1's
contract foundation connecting meaning to implementation, come first. Sized
types and operation parameters are subsequent design tasks that build on that
foundation to support v1.

The [bounded exact contract checker and three-argument auxiliary form](semantic-contracts-v0.1.md)
and [function-contract reuse with evidence retained through final IR](function-contracts-v0.1.md)
are now implemented and checked, meeting v0.1's declared finite profile.
Generalization for v1 remains incomplete. Keep existing paper proofs, finite
regression checks, and a correctness proof of the entire implementation distinct.

[Quantum bookkeeping is the language's responsibility](quantum-bookkeeping.md)
is a design note presenting these principles from the algorithm author's
perspective. It considers ownership, auxiliary cleanup, control, and phase as
one language responsibility and proposes QPE as an early design acceptance test.

**Abstraction criterion adopted for the v0.x plan (2026-09-27):** each new
abstraction must identify an obligation it removes from the algorithm author,
the evidence that replaces that obligation, and the independent check that
enforces it. The [v0.x plan](v0x-roadmap.md#responsibilities-beyond-ownership)
separates ownership, operation capabilities, effects, established auxiliary
invariants, proof contracts and resource accounting. Capability is the next
design focus, building on current finite transforms and effects. Ordinary
composition should reuse library evidence; this is not a promise of unrestricted
automatic proof search. Mathematical unitarity does not grant opaque controlled
access, and a proposed clean-state label cannot replace exact cleanup evidence.
The plan adopts no new grammar or public type.

**Prerequisite before v0.2.0, adopted on 2026-09-27:**
[write ideal code in an imaginary Qleisli 1.0 first](release-milestones.md#pre-v020-imaginary-v1-code).
Produce all six initial drafts and record their semantic requirements and open
questions before generalization, new feature implementation, and the v0.2.0
release. The drafts need not compile and may be revised. Preserve the fixed
principles and v1's execution and validation conditions. Adoption of this
policy and completion of the drafts are separate events; the current artifact
record is the [corpus and requirements index](imaginary-v1/README.md).

## Resource semantics as a first-class account

**User decision, 2026-09-30:** add the
[Resource Safety Theorem](release-milestones.md#resource-safety-theorem-v1)
as a third pillar toward v1, alongside semantic Soundness and Physical
Realizability. It remains **to prove**. The intended guarantee is a finite,
statically computable safe resource bound preserved through compilation for
the supported profile, rather than merely the existence of a finite estimate.

Develop [resource semantics](resource-semantics.md) alongside types, meanings
and effects. Accounts for live qubits, auxiliary space, gate counts, depth and
measurements must compose with actual program structure and target assumptions.
Keep peak space, additive work, shared representation and repeated execution
distinct. Compilers must preserve the accepted resource contract, with explicit
checked bound translation where representations change. Finite does not imply
efficient; budgets and ownership safety are not a proof of this theorem.
The [dated trust-boundary amendment](../TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30)
extends proof duties without trusting estimators or changing current acceptance.

## Keep the trusted core small

**Boundary adopted on 2026-09-28:** the independent-checking architecture is
viable only while the discipline of keeping its trusted base small continues.
Convenience features belong in the desugaring layer, not in the checker.

The **[desugaring layer](terminology.md#desugaring-layer)** translates convenient
source/adapter representations into already specified core operations with
explicit ownership and effects, preserving their meaning. It adds no primitive
meaning or acceptance rule. Its output and proposed evidence remain untrusted
until independently checked; core validity alone does not prove translation
correctness. Parsing, source checking and approximate synthesis remain distinct
responsibilities. A post-verification runtime adapter is not this layer.

Surface syntax, library conveniences, foreign-format spellings and host APIs
must lower to the shared core outside its acceptance boundary. The checker
validates ownership, effects, sealed primitive meanings and evidence bound to
the actual interfaces and operations. Do not add a checker case merely to
mirror a frontend feature or an external gate name. A necessary new core rule
must identify the irreducible semantic/proof obligation and why the existing
core cannot express it; convenience alone is never that justification.

Maintain a constructor inventory with production emitters, consumers, required
checking obligations and a migration/removal plan. IR variants accepted by
the trusted core but never emitted by a production frontend are an early sign
of drift from this discipline. Tests, handwritten examples or a hypothetical
future importer do not by themselves justify keeping such a variant in the
core. Record existing compatibility debt explicitly, stop expanding it, and
move convenience representations to untrusted adapters through a versioned
migration. Preserve current public acceptance until that migration is adopted.

Trust follows the assurance claimed, not the module name. The IR verifier,
independent evidence extractor and exact arithmetic lie on the finite evidence
acceptance path. Moving code into a helper or sharing a numerical interpreter
does not shrink that trusted base. Desugaring output must still pass independent
checking; preserving the input program's meaning is a separate translation
obligation, not a consequence of producing valid core IR. Keep ownership,
phase, effects, zero-return evidence and resource limits intact during reduction.

The [pipeline migration policy](lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary)
keeps independent IR checking at the Rust/Lean boundary throughout a sequence
of pass migrations. Moving and proving an adjacent pass extends the verified
downstream segment; changing implementation language alone does not. The IR
level may move while the fixed trust partition and checking obligation remain
unchanged. Frontend and backend translation preservation remain explicit.
Apply the [de Bruijn criterion per pass](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker):
external search may propose results, while proved Lean checkers establish their
correctness. Rotation-synthesis norm-equation search can stay outside Lean;
the planned `LeafRealizer` checker validates its bound circuit and witnesses.
The migration targets correctness-critical transformations and checks, not
rewriting every search algorithm.

The [IR reduction inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
records the current deviations and initial maintenance work. This adopted
boundary constrains future work; it is not a claim that the current trusted
core is already minimal or that its correctness has been proved.

The [coefficient-domain recommendation](coefficient-domains.md) records a related
risk: do not tie the long-term language to one forecast of early-FTQC gates.
Prepare future exact algebra for a coefficient-domain type parameter and keep
exact meanings, approximation bounds and device/noise claims separate. Domain
arithmetic/equality remains trusted code requiring review; a generic parameter
cannot delegate evidence acceptance to arbitrary user implementations. This is
a future design direction, not a change to the current R8 implementation.

<a id="1-量子データは所有される資源"></a>

## 1. Quantum data consists of owned resources

In source, `Q<A>` is an **owned right to operate** on a logical register with
basis type `A`, not a value whose quantum state vector can be copied. Handles
for disjoint subsystems may belong to one entangled whole system; a handle
does not own an independent pure state. A quantum context is more than a set
of variable names: it includes types, wire IDs, and the ownership consumed
and produced by each operation.

Reject `(q,q)` because it uses the same ownership twice. This is forbidden
aliasing, not a claim that the expression itself implements a physical machine
that clones an unknown state. In contrast, `x -> (x,x)` for a coherent basis
label `x : Bit` is allowed as an isometric map because `⟨xx|yy⟩ = δ(x,y)`.
A basis label is not a measured classical value.

Physical discard is possible, but it is not **implicit weakening** in the
source language. Pure code passes quantum ownership linearly. Discarding an
arbitrary state requires the explicit irreversible operation `observe::discard`.
Pure release of an auxiliary bit requires static evidence of zero return and
separation for every input. In this sense quantum resources admit physical
discard, as an affine discipline would allow, but the language does not adopt
implicit affine discard that hides the effect.

<a id="2-プログラムは資源の効果付き変換"></a>

## 2. Programs are effectful transformations of resources

Read a program signature conceptually as follows:

```text
(classical input A; quantum context Δin) -[effect ε]->
    (classical output B; quantum context Δout)
```

`Δin` and `Δout` describe ownership received, returned, newly created, and
consumed. `ε` uses the normative order `Unitary ≤ Iso ≤ Observe`. This is a
conceptual picture of a whole computation's inputs and outputs, not a separate
judgment form. Its projection from source judgments with mixed values is
defined in the [formalization overview](formal-core.md#1-scope-and-judgments)
and [value semantics](source-semantics.md#1-mixed-values-and-ordered-quantum-interfaces).
Resource transitions alone do not describe isometry, measurement probabilities,
or correlations lost by discard; effects and semantics must remain explicit.

In a coherent operation, classical output `B` can be computed only from the
classical input. Obtaining a `CBit` from quantum basis contents requires a
measurement effect. Track the quantum output's basis type separately from
this classical output type.

| Operation | Ownership transition | Effect and meaning |
| --- | --- | --- |
| `init0` | `∅ -> {q}` | An isometry preparing the known state `\|0⟩`. |
| `h` | `{q} -> {q}` | A unitary. |
| `measure_z` | `{q} -> ∅`, with a `CBit` result | A quantum instrument returning the measurement outcome and consuming the logical wire. |
| `discard` | `{q} -> ∅` | An observation effect taking a partial trace. |

Measurement ends ownership of the logical wire; it does not make a physical
device disappear. If a qubit is needed later, prepare a new logical wire with
`init0`. The backend decides whether the corresponding physical device can
be reused.

From this perspective, `h : Q<Bit> -> Q<Bit>` is a valid **linear function
signature**. It does not mean a function on sets of ordinary copyable values.
Transformations acting on states, rather than state values themselves, are the
mathematical focus. The initial version does not require operations to be
first-class source values.

<a id="3-合成は-kleisli-的に行う"></a>

## 3. Composition follows a Kleisli-style principle

Compose transformations when the quantum context returned by the first is
compatible with the quantum context accepted by the next:

```text
(A; Δ0) -[ε1]-> (B; Δ1)
(B; Δ1) -[ε2]-> (C; Δ2)
--------------------------------
(A; Δ0) -[ε1 ∨ ε2]-> (C; Δ2)
```

This **Kleisli-style composition principle** motivates the name Qleisli.
`ε1 ∨ ε2` is conceptual notation for the composite effect; in v0 it is the
maximum of the normative specification's three effect values. Context
compatibility requires checking types and wire ownership.

Distinguish two mathematical layers. Kleisli composition for the free vector
space `Vec(A) = C^(A)` on a finite basis `A` explains the linear origin of
coherent computation. However, unrestricted `bind` can construct nonisometric
maps. For example, the map `Bit -> Vec(Bit)` given by
`0 -> |0⟩, 1 -> |0⟩` sends two orthogonal inputs to the same output; it is not
exposed as a safe execution API. Whole programs containing measurement, reset,
or discard instead compose quantum instruments with classical outcomes.
A rigorous formulation of this structure as an indexed monad has not been
proved.

The [finite-core v0](language-spec.md) form `do x <- q; pure e(x)` is restricted
syntax for the coherent lift of an injective basis map. It does not decide
that the same `do` syntax will implement composition of whole effectful
programs. The fact that consecutive operations such as
`init0; h; measure_z` form one transformation is a design principle that
precedes its choice of surface syntax.

<a id="4-古典と量子は型レベルで非対称"></a>

## 4. Classical and quantum data are asymmetric at the type level

Classical values such as `CBit` may be copied and used as branch conditions.
Ownership of `Q<A>` may not be copied. A coherent basis label of type `Bit`
cannot be read through an implicit conversion to `CBit`; readout requires
explicit measurement. Classical `if` and coherent `qif`, which preserves
the control qubit's coherence, are different constructs.

<a id="5-純粋関数型の意味"></a>

## 5. Meaning of purely functional

Do not update quantum state as a hidden mutable global value. `let` and
function composition describe the transfer of ownership to new names.
Measurement is probabilistic and irreversible, but it has an explicit
`observe` effect and quantum-instrument semantics. Host I/O and device
failures must not silently enter pure functions.

Linear ownership and wire-ID checks prevent reuse of an old measured handle
or repeated specification of the same wire. Isometry, phase under coherent
control, and auxiliary zero return additionally require type/effect checks
and IR verification that account for quantum semantics.

<a id="未解決の中核課題-所有権とエンタングルメントの分離"></a>

## Open central issue: separating ownership from entanglement

A quantum context `Δ` describes rights to operate on subsystems, not a claim
that those subsystems are in a product state. For example, `q` and `r` obtained
by applying `split` to the Bell pair `(|00⟩ + |11⟩)/√2` can be owned separately, although
their state is not separated. Discarding `q` leaves `r` in state `I/2`.
Measuring `q` in the Z basis with outcome `b` leaves the conditional state of
`r` equal to `|b⟩`.

**The task is to express the boundary between ownership-based resource safety
and correlation-dependent quantum guarantees in type/effect rules and IR that
can be checked across function boundaries.** Interpret local gates on the
whole system, measurement as a local instrument, and discard as partial
trace. A pure `release0` step requires evidence that the target returns to
`|0⟩` and separates from the rest for every input and reference system.
Matching input and output ownership sets does not establish that an internal
auxiliary was cleaned up purely. Choosing irreversible discard must appear
as an `observe` effect. In current v0, `release0` is an internal certified
step, not a standalone source API.

Finite core v0 makes whole-system local action and restricted auxiliary
evidence normative. General soundness, function-boundary, and IR-correspondence
proof obligations remain in Stage 1. Passing general correlation/separation
evidence through signatures belongs to subsequent specifications. The initial
version does not require a general entanglement decision procedure.
Reordering or parallelizing operations on separate wires must be justified
by their acted-on wires, classical dependencies, effects, and target-device
constraints, rather than an assumed product state.

<a id="添付議論からの用語の確定"></a>

## Terminology adopted from the supplied discussion

| Expression in the supplied discussion | Adopted Qleisli interpretation |
| --- | --- |
| `Qubit` or `Q<A>` | The source ownership type `Q<A>`, not a state vector itself. |
| The outer `Q` in `Q(Qubit)` | A computation-effect concept. Express it using the effectful transformations above rather than stacking the same `Q` on the ownership type `Q<A>`. |
| “It is affine, so it may be discarded” | Physical discard is possible. Pure code has no implicit discard; irreversible discard is explicit. |
| “Quantum operations are not ordinary functions” | A linear signature such as `Q<Bit> -> Q<Bit>` is valid. Its input is not interpreted as a copyable state value. |
| “Transformations are first-class” | Transformations are central to the semantics. First-class operation values and general higher-order functions are not requirements of the initial version. |

**Fixed principles:** ownership that cannot be duplicated; explicit discard;
effectful composition of classical values and quantum resources; asymmetry
between classical and quantum data; and a semantic distinction between pure
operations and observation.

General borrowing syntax and signatures belong to subsequent specifications.
v0 uses the protection rules for restricted auxiliary computation.

**Responsibilities assigned to Stage 1 in the design plan:** syntax, precise
type/effect judgments, the formal structure supporting Kleisli-style
composition, static evidence at the ownership/correlation boundary, and the
decision of when operations become first-class values. The current finite
syntax and judgments are recorded in the v0 specification; assigning these
responsibilities does not declare all associated proofs complete.

Subsequent drafts must follow the fixed principles. If a principle itself
needs to change, provide a counterexample or a new execution requirement and
update the language requirements, specification, and roadmap in the same change.

The [quantum-language requirements](quantum-language-requirements.md) record
the related conditions; the [v0 language specification](language-spec.md)
records finite-core rules and operation examples. The
[AI-era quantum-language goal](ai-era-goal.md) develops these principles from
the perspective of compile-time soundness, without claiming that the desired
guarantees are already proved. For the effect of implicit discard on
coherence, see the [original QML paper](https://people.cs.nott.ac.uk/psztxa/publ/qml.pdf);
for prior work on lifetime-based uncomputation, see
[Qurts](https://arxiv.org/pdf/2411.10835).
