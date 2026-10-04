# Initial QS, PR and RS interpretations

**Status: adopted on 2026-10-04 (Asia/Tokyo); binding pending discharge.**
The human Guardian, Masahiko G. Yamada, explicitly adopted all three
interpretations below. None is a discharged ledger guarantee. The separate
human adoption record is `governance/interpretations/initial-2026-adoption.json`;
constitutional ratification, the appointment, tests, proofs, audits and document
checks did not substitute for that act.

The authoritative adopted text is the exact reviewed packet preserved in
`governance/interpretations/initial-2026-reviewed.txt`, with SHA-256
`7a79a18ad66e4b7cdaa87865eff1bf87ce933da758461cb45cc13a87fb1555b3`.
This chapter updates only status wording, headings and adoption tenses for the
book. Its mathematical scopes, properties and premises are unchanged. Changing
that adopted meaning requires a new human Guardian judgment; editing this
chapter cannot amend it.

Implementation note: the reviewed packet's ownership-only `ResourceSafe`
predicate and theorem names are now spelled `OwnershipSafe` and
`ownershipSafe` under [Issue #287](https://github.com/MGYamada/Qleisli/issues/287).
This identifier-only change preserves their mathematical content; references
below retain the reviewed names. It does not discharge quantitative RS.

Subsequent admission: the human Guardian has approved
[two scoped QLV1 guarantees](initial-guarantees.md) for ownership and classical
scope, with their checked proof evidence. They discharge only those recorded
components; the three broader obligations in this interpretation remain pending.

This packet records initial applications of the three existing obligations in
`CONSTITUTION.md`, under Articles V–VIII. It adds no
Fundamental Theorem and changes no constitutional text. Its mathematical scope
belongs to interpretation records, outside the entrenched Constitution. The
[ratification record and process](ratification.md), `GOVERNANCE.md` and the
[authority hierarchy](../reference/authority.md) identify the human authority;
they do not substitute for that authority's recorded decision on this packet.

## Shared production boundary and premises

The initial scope is the currently admitted finite/raw and sized/hierarchical
production paths of edition 2026, including their source, Rust, CLI, Python and
foreign-format callers. A future feature remains subject to all applicable
obligations; omission from today's examples or proofs creates no exemption.
The scope and evidence must be updated when the admitted language grows.

[Decision #276](https://github.com/MGYamada/Qleisli/issues/276) places production
acceptance in the Mathlib-free native Lean checker. For ordinary QIRF, the
concrete chain includes the original artifact and optional independent request
bytes in the QLV1 packet, `QleisliKernel.Protocol.Validity.check`, and
`QleisliKernel.Qirf.Validity.inspect`. On the Rust side,
`interchange::native::Kernel` obtains the fresh decision and authorizes private
accepted handles associated with those bytes. The hierarchy has its own native
structural/request checks and freshly checked finite obligations. The ordinary
QIRF theorem alone does not cover that entire hierarchy.

For each claimed guarantee, its release record must identify the real entry
points, admitted profile, original inputs, requested contract when present,
checked representation and current artifact consumed by execution or export.
It must account for the selected checker and its compatibility/provenance
assumptions. A theorem about an unused predicate, a subset chosen only to make
the theorem easier, or a producer's success receipt cannot stand for production
acceptance. A structural hierarchy derivation cannot silently stand for the
missing analytic meaning of its complete accepted operator.

The policy in `TRUSTBOUNDARY.md` remains in force, as described in the
[production authority chapter](../reference/authority.md#production-acceptance-and-the-trust-boundary):
reference meanings require human specification review; frontend output, synthesis search
and other proposals require independent validation. Native compilation/runtime,
decoding, source lowering, Rust re-materialization, execution and emitted-output
correspondence must retain their actual assumptions and proof gaps. Moving code
into Lean or obtaining an accepted handle does not discharge all those links.
Source acceptance must be connected to the source's specified meaning before
source preservation is claimed.

New sealed semantics require the admission review proposed in
[Issue #154](https://github.com/MGYamada/Qleisli/issues/154): exact meaning,
reference behavior, owners/effects, phase/coordinates, target/workspace and
resource obligations, and why ordinary checked source or a verified
transformation is insufficient. Popularity or performance alone is insufficient.
An implementation intrinsic must implement an existing meaning or undergo that
review. No interpretation here authorizes project axioms, unsafe/partial executable
definitions or runtime replacements. A reviewed semantic assumption is not a
permission to add a Lean project axiom.

Adoption identifies obligations and their current gaps. It does not confer
full pre-v1 certification on existing accepted paths, change the acceptance
implementation or enable external schemas. Article VIII requires truthful
scope-specific claims throughout this work. The full supported-profile
Soundness/specification/review milestone remains v0.5.0; the complete three-
obligation conformance requirement remains the separate v1 milestone.

## 1. Interpretation QS-2026-01 — Meaning of accepted programs

**Scope:** the current production program/evidence acceptance boundary
above, with the particular guarantee stated separately for an ordinary root,
an independently requested finite contract, a hierarchy, or a source-level
claim. These are coverage distinctions within QS, not alternative acceptance
authorities.

**Obligation:** the actual accepted program must satisfy its declared
typing, ownership, effect and semantic contracts, interpreted independently of
the checker and evidence producer. An independently supplied requested meaning
must bind the accepted implementation, its dependency evidence and its full
interface. An ordinary acceptance without such a request must not be advertised
as proof of an arbitrary external functional specification.

The required properties and premises are:

- Preserve logical owners, including zero-width owners, complete tuple/basis
  shape, finite sizes and the ordered mapping from interface axes to the
  interpreted operator. Equal width alone does not identify an interface.
- Preserve linear use, global identity freshness, lexical classical scope,
  simultaneous branch-phi inputs and the complete live caller frame. Separate
  owners do not imply separable quantum states. Measurement consumes its
  logical owner; discard is explicit and has its declared semantics.
- Interpret pure operations as the specified exact maps, including exact phase
  before taking a density-operator interpretation. Matching probabilities or
  equality up to global phase cannot replace an exact operation contract,
  especially when coherent control can expose relative phase. Unitarity alone
  supplies neither an inverse API nor controlled access.
- Interpret observing programs by their unnormalized, outcome-indexed
  completely positive maps, acting correctly with arbitrary external
  references. Account for hidden measurement, reset and discard histories and
  the declared classical output/coarse-graining map. Trace preservation is a
  property of the complete admitted instrument; checking individual sampled
  results or renormalized branches does not establish it.
- Require exact semantic discharge of clean workspace, and the distinct
  restoration obligation for dirty workspace, as described below.
- Preserve these properties through the actual admitted composition and
  transformations. Any source or runtime claim needs its corresponding
  preservation link, beyond acceptance of a proposed IR object.

For clean workspace `A`, suppose the program denotes a finite-dimensional CPTP
map `E_p` from `A ⊗ R_in` to `A ⊗ R_out`, with `A` initially in `|0><0|`.
For an observing program, `R_out` includes its declared classical outcome
register: the premise concerns the complete instrument, not a normalized
selected branch. Define the reduced live-system channel by
`Phi(rho) = Tr_A(E_p(|0><0|_A ⊗ rho))`. Exact return of the workspace marginal
to `|0><0|` for **every density operator on `R_in`** is equivalent to the
following separation condition for every finite external reference `E` and
every joint density operator `rho` on `R_in ⊗ E`:

```text
(E_p ⊗ id_E)(|0><0|_A ⊗ rho)
  = |0><0|_A ⊗ (Phi ⊗ id_E)(rho)
```

The equivalence requires the all-input, exact, fixed-pure-state premises; the
two formulations are not independent extra obligations. Observing branches
must retain their unnormalized probabilities in the corresponding instrument
formulation. Dirty workspace instead requires restoration of its unknown state
and reference correlations according to its declared identity contract. A
known-input test or workspace marginal alone is insufficient for dirty return.
This follows the proposed distinction in
[Issue #157](https://github.com/MGYamada/Qleisli/issues/157). Approximate marginal
cleanliness does not imply separation with the same error parameter; this
packet admits no approximate cleanup or epsilon contract.

**Candidate evidence and gaps:** `Qleisli.NativeValidity.check_sound` binds
success of the actual Lean QLV1 checker definition to
`Qleisli.Qirf.Validity.VerifiedMeaning`. Its ordinary root carries structural
postconditions, independent linear `ResourceSafe` and classical `ScopeSafe`;
an optional finite request additionally carries the stated original-instrument
finite contract. `Qleisli.Qirf.Validity.requested_reference_laws` supplies the
stated finite-reference inverse laws for that requested contract. These are useful candidate evidence,
not a complete ordinary-root EffectSound/CPTP or source/runtime theorem.
`Qleisli.NativeHierarchy.checkLeaves_semantics` and
`Qleisli.NativeHierarchy.conditional_derives` connect
fresh native finite leaves to their structural derivations; general analytic
LeafMeaning-to-Operator closure remains a separate duty. Their existing scope,
reference definitions, assumptions and relation to each public acceptance path
still need review before any ledger discharge is recorded.

## 2. Interpretation PR-2026-01 — Accepted target realizations

**Scope:** each target realization for which Qleisli claims executable
or exported implementation of an accepted semantic program, including its
actual emitted circuit/artifact, target/profile and checked evidence. A
semantic accepted handle alone is not target-realization certification.

**Obligation:** every realization admitted by the production
realization gate must implement the already accepted meaning under its stated
target and workspace contract. The record must bind the current accepted
program/request, target, emitted artifact and evidence to that gate. Checking a
different internal circuit or retaining a producer's claim is insufficient.

Required premises include the declared primitive gate actions and device
assumptions, input/output encoding and coordinate order, effects and classical
outcomes, admitted synthesis workspace, initialization/restoration, and the
exact equality contract. Workspace may exceed the semantic program's original
wires; semantic unitarity does not prove same-wire synthesis. Clean and dirty
workspace obey the QS distinctions above and remain counted while live under RS.

Exact operation contracts retain their phase. A projective equality claim
would require an explicit permitted contract and a proof that its intended
contexts respect that quotient; it cannot discharge an existing exact or
coherently controlled contract by silently discarding phase. No target gate
set, coefficient ring, projective relaxation or approximate synthesis facility
is admitted merely by adopting this interpretation.

This is the **forward correspondence** duty proposed in
[Issue #281](https://github.com/MGYamada/Qleisli/issues/281). It does not require
that every matrix in an independently specified mathematical domain have a
realization, or that Qleisli implement a complete synthesis algorithm for it.
Target/profile existence and synthesis-completeness theorems may be proved
separately and used to produce evidence. Independently supplied realizations
are admissible only through the same checked correspondence gate. Missing
synthesis is an unsupported target realization; it is not permission for a
fallback that certifies unchecked output. Inverse and controlled capabilities
remain separate obligations.

**Candidate evidence and gaps:** finite circuit/contract, hierarchy and exact
algebra theorems may supply components of correspondence. They do not by
themselves connect every current exporter, target lowering or synthesized
artifact to the requested meaning. This packet identifies no discharged
production-wide PR theorem and does not treat successful QIR emission,
simulation, native acceptance or physical-device assumptions as that theorem.
Each concrete target claim must expose the missing links or provide their
checked proof before that scope is certified.

## 3. Interpretation RS-2026-01 — Quantitative resource accountability

**Scope:** finite, statically computable bounds for the resource
semantics applicable to the current accepted program, its admitted
specialization/family and, where claimed, its current target realization. The
resource contract must state input/size premises, counted quantities, target
capacity and scheduling assumptions, and all permitted branches.

**Obligation:** actual accepted behavior and actual admitted
transformations must respect independently checked finite resource bounds.
Composition, lowering, optimization, synthesis and emission must preserve the
bound contract or produce and validate a justified replacement bound for the
resulting artifact. An estimate about a different circuit cannot certify the
emitted artifact.

The current resource model must explicitly select its measures: for example,
peak live width, clean/dirty/backend workspace, gate or non-Clifford counts,
measurement and feed-forward counts, and depth under a specified schedule.
Alternative classical outcomes require the declared safe bound over permitted
execution paths; a mean from sampled runs does not establish that bound.
Workspace returned clean still counts for its live interval. Correct semantics
or a valid realization alone does not prove compliance with a target capacity.

A closed finite specialization may admit concrete checked accounting. An
admitted family needs a justified bound function over its stated parameters,
without treating finitely many tested instances as its proof. New runtime
control, opaque providers or target-dependent synthesis must activate the
corresponding bound obligations before claims of certified resource coverage.
Untrusted external annotations require checking and composition; they cannot
grant their own resource authority.

This applies the proposed quantitative jurisdiction in
[Issue #280](https://github.com/MGYamada/Qleisli/issues/280). Linear ownership,
no implicit discard and clean/dirty restoration belong primarily to QS.
`ResourceSafe` in the current ownership proofs does not establish this RS
claim. Checker work counters, input limits and host timeouts constrain the
verification implementation; they do not constitute a program/target resource
bound unless a separately specified correspondence establishes such a claim.

**Candidate evidence and gaps:** finite accounting structures and ownership
proofs can support later constructions, but this packet identifies no completed
production-wide quantitative RS discharge. Required resource semantics,
certificate rules and preservation links must be specified and checked against
current production artifacts. The existing Resource Safety target remains
distinct from clean discharge. Later compatible features may strengthen its
proof burden without creating a fourth obligation or escaping edition 2026.
This interpretation grants no permission for approximation or other future syntax.

## Evidence, continuity and the recorded human decision

The working directions in
[Issues #135](https://github.com/MGYamada/Qleisli/issues/135),
[#136](https://github.com/MGYamada/Qleisli/issues/136) and
[#139](https://github.com/MGYamada/Qleisli/issues/139) inform this packet. Their
text and the cited Lean declarations are not binding interpretations merely
because they exist. This packet's binding force comes from the recorded human
adoption. Current theorem statements may evolve; mathematical
meaning requires reviewed reference definitions independent of the checker or
proof decomposition. The statement-isolation work in
[Issue #306](https://github.com/MGYamada/Qleisli/issues/306) remains a v0.5.0
obligation and must preserve the link to actual production acceptance.

Each adopted interpretation is recorded first as a **binding pending
obligation**, with its exact reviewed text, human decision, scope and premises.
Existing proof coverage must then be matched to the interpreted requirement
and independently verified before a separate discharge record can enter the
ledger. A successful audit, an ordinary helper lemma or approval of this packet
alone does not create a discharged guarantee.

For every later discharge, bind the protected property, fragment, premises,
semantic definitions, proof/evidence and current acceptance/artifacts. Later
releases must preserve applicable ledger guarantees against their own real
acceptance machinery, with justified embeddings and semantic transport where
representations differ. An implication between two old closed theorems is
insufficient. New capabilities outside old fragments remain subject to the
current obligations. Acceptance continuity and source support also retain
their separate published compatibility duties.

**Recorded decision:** on 2026-10-04 (Asia/Tokyo), the human Guardian adopted
**QS-2026-01**, **PR-2026-01** and **RS-2026-01** as one exact packet, each with
its separate scope, properties and premises. The question identified the
reviewed packet's SHA-256 above and all three identifiers. The answer was:

> 3件とも提示された本文どおり採択する

The adoption event preserves that question and answer. Its SHA-256 is
`bb9e4b68024b4153515d3a2652feb3b64d16907522bf9575fd18e3a9e61a7c9e`.
This was affirmative adoption of all three; none remains proposed. No response,
general implementation permission, a CI result or machine-generated approval
could have substituted for this human decision. Adoption establishes the stated
obligations; it does not declare them proved or alter the Constitution's fixed
three obligations.
