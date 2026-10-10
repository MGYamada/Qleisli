# Operations, meanings and capabilities: implementation decision candidate

**Status: nonnormative candidate for an ordinary implementation decision.**
This packet makes the operation part of the [type foundation](type-foundation.md)
concrete. It proposes rules and desired source; none of the examples below is
reported as compiled. It does not ratify text, record a Guardian judgment,
admit a guarantee, change the adopted QS/PR/RS interpretations, or close an
Issue. The [authority hierarchy](../reference/authority.md) still applies.

**Naming update (2026-10-08):** [Issue #45](https://github.com/MGYamada/Qleisli/issues/45) selects `Applicable`, `Adjointable` and `Controllable`, with `adjoint(U)` as the general constructor. The older `Apply`/`Adjoint`/`Controlled` and `inverse(U)` candidate notation below is superseded by this naming decision; it is not current executable syntax. The [static-language Reference](../reference/static-language.md#operation-repetition-and-access) specifies the bounded implementation. A future two-sided inverse API requires its own law; this update grants no general isometry adjoint or new provider access.

**Naming decision:** [#82](https://github.com/MGYamada/Qleisli/issues/82)
selects `checked_op(implementation, Meaning)` for the existing closed-declaration
constructor. The proposed `bind` spelling below is superseded by that name.
Its broader proposed operation-expression inputs, arrow kinds, Meaning forms
and other constructor renames remain candidates. The naming decision adopts
none of those extensions; [Checked operations](../reference/checked-operations.md)
specifies the current bounded contract.

**Implementation review update (2026-10-10):** the earlier
[operator-arrow study](https://github.com/MGYamada/Qleisli/blob/09e21a305c7e6fca1e8d82378756ca35ae5a305b/tests/fixtures/authoring_sessions/operator-arrow-v030/README.md)
is a historical observation, not a list of current limitations. Rechecking its
unchanged preparation `Q<Unit> -> Q<Bit>` and explicit unitor sources now succeeds
through the selected hierarchy path. These checks report producer consistency,
`request_origin: producer` and `source_meaning_verified: false`; they do not
establish independent expected-meaning equality or general static arrows.
The unchanged quantum-capturing closure now rejects at the resolved owner's
use with an ownership diagnostic, rather than a parser failure. A false
`unitary` assertion on preparation still rejects with inferred Iso effect and
the explicit unsupported-external-unitarity explanation. No historical source
or observation has been rewritten. The older comma-form domain/codomain syntax,
rectangular Meaning evidence and complete instrument requests below remain
unimplemented; these bounded repairs do not settle #83 or complete #46.

The current bodies of [#45](https://github.com/MGYamada/Qleisli/issues/45),
[#46](https://github.com/MGYamada/Qleisli/issues/46),
[#83](https://github.com/MGYamada/Qleisli/issues/83) and
[#89](https://github.com/MGYamada/Qleisli/issues/89) were read from GitHub on
2026-10-04. All four were open design issues at that observation. Their respective last-update times
were 08:19:58Z, 08:19:59Z, 08:20:02Z and 08:18:25Z on that date. Issue examples
such as the old `Op<A,M>` are inputs to this decision, not adopted grammar.

**Current boundary evidence (2026-10-10):** #45 and #89 are now closed against
their own scoped acceptance conditions; #83 and #46 remain open. The
[arrow-interface study](https://github.com/MGYamada/Qleisli/tree/codex/v0.3.0-foundation/tests/fixtures/authoring_sessions/arrow-interfaces-v030)
preserves six unchanged first sources. Direct unitor/preparation and an
endomorphic static control pass the existing selected CLI; a unitor supplied
to `Op<(Unit,Bit)>` rejects at its exact provider tree. Both desired comma-form
arrows reject in the existing Meaning slot. These observations do not implement
general arrows or independently verify the candidate's requested meaning.

**Bounded Meaning implementation (2026-10-10):** declared finite monomial
Meanings now support contextual `compose(First, Second)` and
`tensor(Left, Right)` in both source adapters. The
[Reference](../reference/checked-operations.md#bounded-exact-meaning-composition)
specifies exact endomorphic typing, order, phase and limits. Fresh native
provider checks reject reversed Z/X order and exchanged tensor axes. The
observing and pure-entry adapters and their actual profile refusals are retained
in the [composition study](https://github.com/MGYamada/Qleisli/tree/codex/v0.3.0-foundation/tests/fixtures/authoring_sessions/meaning-composition-v030).
This does not implement the general rectangular, nonmonomial/reference or
instrument Meanings proposed below, complete native extensional equality,
prove source-to-request preservation or close #46/#83.

### Implementation constraints exposed by the current checker

The generalization must change the shared original-source judgment and both
materialization adapters together. Adding a parser field while projecting it
back to the old single basis would silently change the requested interface.
Before changing the normative contract, implement these candidate rules:

- Retain exact domain and codomain independently through ordered formal
  substitution, provider resolution, operation construction, specialization
  identity, Meaning obligations and actual-artifact/native-request attachment.
  `Op<A>` still abbreviates precisely `A -> A`; the equal-dimensional unitor
  negative remains invalid for that endomorphic formal.
- Track the pure law separately from executable access. A general applicable
  arrow supplies an isometry law and has an Iso upper effect bound. An
  endomorphism can retain the current Unitary inference by the finite-space
  isometry law. A differing-tree arrow can have Unitary effect only with checked
  equal-dimension/two-sided laws; identical physical width is insufficient to
  convert its source trees. Abstract bodies cannot use the fortunate law or
  effect of one later concrete provider to justify other instantiations.
- Adjointable requires a full-space two-sided law and the actual reverse
  realization. Reverse the domain/codomain when constructing the adjoint.
  Controllable and repetition require an exact endomorphism interface, including
  a zero repetition count. Composition matches the exact middle tree, and
  ordered tensoring constructs both interface trees independently. Observe
  providers never enter this pure-arrow category.
- Preserve the existing Iso transport's explicit empty-readout mapping where
  it is used. An instrument-shaped transport is not an Observe effect, an
  arbitrary instrument Meaning or a general adjoint API. Every proposed new
  static-provider route still needs fresh native acceptance of its actual
  original artifact; a direct-call success supplies no cached provider receipt.
- Resolve the existing Meaning comma slot explicitly as part of the grammar
  cutover below. Do not infer category from a name or keep a second parser
  interpretation. Preserve the first rejected sources and append migrated
  clients separately after the selected grammar is implemented.

These are implementation requirements for this nonnormative candidate, not a
new binding interpretation or a claim of complete implementation. The current
common checker distinguishes general arrows from legacy endomorphic providers.
The tests
in `tests/operation_parameters.rs` retain the direct/control effect distinction
and both public source entry points' wrong-tree refusal without making desired
future syntax rejection a permanent regression requirement.

**General arrow implementation (2026-10-10):** the ordinary implementation
contract in [#83](https://github.com/MGYamada/Qleisli/issues/83#issuecomment-6096747939)
selects `Op<A -> B>` with `Op<A>` as the endomorphic abbreviation. This supersedes
the proposed comma-form arrow spelling below; the comma still introduces a
Meaning refinement. The [Reference](../reference/type-model.md#general-pure-operation-arrows)
specifies both exact ports, conservative effect bounds and capability rules.
Forward selected application of transparent ordinary providers now reaches fresh
native acceptance for preparation and a differing-tree unitor. Common checking
rejects false Unitary claims, Observe providers, wrong trees and rectangular
control/repetition even at count zero. Finite general-arrow materialization,
general composite/transform lowering and rectangular Meanings remain unsupported.
The [retained study](https://github.com/MGYamada/Qleisli/tree/codex/v0.3.0-foundation/tests/fixtures/authoring_sessions/general-arrows-v030)
keeps manifest/parser failures and pre-repair lowering failures beside the actual
subsequent checks. Independently authored exact requests check small preparations
and reject a native-valid wrong gate. Initialization-movement validation alone
does not check the gate's complete meaning. No general source-preservation,
QS/PR discharge or completion of #83/#46 is claimed.

## Recommended decisions

1. Use general pure arrows `Op<A,B>` and `Meaning<A,B>` internally and publicly.
   `Op<A>` and `Meaning<A>` abbreviate the endomorphic cases. Give refinement
   an explicitly labelled `meaning` argument; never infer whether a second
   positional argument denotes a basis or a meaning.
2. An executable pure operation is a total isometry on its declared input space.
   A unitary arrow additionally has a two-sided inverse. Preparation is an
   ordinary `Unit -> A` isometry. Observation is a separate instrument family.
3. Keep mathematical meaning, implementation identity, and executable access
   separate. `Apply`, `Adjoint`, and `Controlled` carry checked implementation
   paths, not booleans, algorithm names or matrix claims.
4. Keep quantum source functions first-order; operations and higher-order
   operation builders are static values. They never contain a live owner.
5. Implement the bounded exact meaning fragment below, including QFT2/QFT3,
   reference functions and complete bounded instrument requests, in 0.3.0.
   Unsupported equalities reject explicitly. This is a finite implementation
   contract, not a decision to defer these four Issues to 0.4.0.

All new syntax goes through the common frontend. Edition stays **2026**; it
identifies the constitutional regime, not this release's grammar migration.

## Public surface and static categories

```text
OperationKind ::= Op<A> | Op<A,B>
                | Op<A, meaning M> | Op<A,B, meaning M>
MeaningKind   ::= Meaning<A> | Meaning<A,B>
InstrumentKind ::= InstrumentMeaning<A,B,C>
```

Here `A` and `B` are exact finite basis trees; `C` is an exact finite ordinary
outcome tree. The foundation's `Unit`, `Bit`, `Bits<n>` and product distinctions
apply, including zero-width nodes. `Op<A, meaning M>` expands to
`Op<A,A, meaning M>`. `M` must have exactly `Meaning<A,B>`; identical dimensions
are insufficient. A labelled slot is always last and occurs at most once.

The desired declaration and application forms are:

```qli
meaning IdBit : Meaning<Bit> = identity[Bit];
meaning Fourier2 : Meaning<Bits<2>> = fourier[2];

unitary fn use_once[static A: Basis, static U: Op<A>](q: Q<A>) -> Q<A>
requires Apply(U) { U(q) }

unitary fn use_backwards[static A: Basis, static U: Op<A>](q: Q<A>) -> Q<A>
requires Adjoint(U) { inverse(U)(q) }

unitary fn use_controlled[static A: Basis, static U: Op<A>]
(q: Q<(Bit,A)>) -> Q<(Bit,A)>
requires Controlled(U) { controlled(U)(q) }
```

`then(U,V)`, `tensor(U,V)`, `inverse(U)`, `controlled(U)` and `power(U,n)` are
static builders. `checked_op(implementation, expectedMeaning)` constructs a refined
static operation after checking the binding; it is not a general monadic bind.
The proposed extended implementation argument of `checked_op` is a closed, explicitly specialized
operation expression (including a resolved source provider or a constructed
operation), with a materializable artifact. An unresolved abstract parameter
cannot acquire a refinement by this form; it must already carry the required
refinement evidence in its generic interface.

An ordinary closed, explicitly specialized pure source function may also appear
as a static operation argument without a named expected meaning. That case
checks implementation validity and applicable access paths, but does not claim
an independent expected algorithm. Primitive provider names resolve to the same
sealed identities as ordinary calls, without synthetic wrapper functions.

Meanings are static terms and may appear as refinement indices. A name resolves
to a declaration identity, not to a string interpreted by a backend. Ordinary
basis predicates used in a meaning must be closed, total, statically evaluable
and explicitly specialized. No runtime value, including an ordinary runtime
bit, is captured by a static description.

| Callable category | 0.3.0 rule |
| --- | --- |
| Ordinary pure/observing source function | First-order calls with explicit static arguments and live arguments; no runtime function object. |
| `Op<A,B>` | Copyable static description; application consumes one `Q<A>` and returns one `Q<B>` when `Apply` is available. |
| Named static builder | May receive/return static operations and meanings, use bounded static control and capture only explicit immutable static parameters. Check all branches and bodies before specialization. |
| Ordinary classical helper | First-order, or a separately admitted ordinary callable form; this packet adds no lambda/closure syntax. |
| Runtime quantum-capturing closure | Reject, including an owner hidden in a tuple/environment or `Q<Unit>`. No unrestricted or one-shot quantum closure type is enabled here. |

Cross-module/qrate operations are allowed through ordinary visibility and the
resolved dependency graph. An exported operation retains its exact signatures,
static substitutions, meaning identity and checked access paths. Importing an
operation cannot enlarge its capabilities. General meta-programming and linear
closures are the existing explicit non-goals of #89, not deferred obligations
of the selected 0.3.0 callable model.

## Arrow meaning, effects and ownership

For ordered bases `A` and `B`, a pure meaning denotes a matrix
`M : C^A -> C^B`, with output rows and input columns. Application requires
`M† M = I_A`; unitarity additionally requires `M M† = I_B`. The equations hold
on the entire declared input space and after tensoring an arbitrary reference.
They do not assume that separate logical owners are separable.

`unitary` permits different exact input/output trees only when their finite
dimensions agree and the two-sided laws hold. Equal width never supplies the
source conversion or implementation. `iso` permits dimension increase with the
one-sided law. A declaration/effect label alone proves neither equation.
Applying a pure arrow has its checked pure effect; it cannot perform measurement,
implicit discard or unresolved allocation/cleanup. Preparation has Iso effect.
Explicit measurement/discard has Observe effect and cannot inhabit `Op`.

A pure operation consumes its input owner and produces its output owner once.
Static copying of `U` does not copy `q`. `Op<Unit,A>` is called with `Q<Unit>`;
it is not a coercion from ordinary `()` or a rule to erase an empty owner.
The existing source `init0()` primitive can lower to the same preparation
meaning while its wrapper explicitly accounts for the empty input port. This
requires a checked wrapper/interface mapping, not a new implicit source cast.

For an isometry `V : A -> B`, the matrix `V† : B -> A` exists mathematically,
but generally is not a total isometry on all of `B`. For example, the adjoint
of `|0> : Unit -> Bit` annihilates `|1>`. Therefore `inverse(V)` and an
`Adjoint(V)` access path require independently checked two-sided laws and a
usable inverse implementation. A promise that an input is in the image does
not satisfy that full-space rule. Existing encoded/subspace contracts and
clean-uncompute obligations remain explicit interfaces with their own evidence;
they do not silently turn a partial inverse into `Op<B,A>`.

## Capability judgments and construction rules

Write `A(U)`, `D(U)` and `C(U)` for `Apply`, `Adjoint` and `Controlled` evidence.
Each evidence object binds the original implementation, its complete dependency
closure, ordered interface, phase-fixed denotation and executable realization.
A semantic proof of unitarity or a declared meaning never supplies access alone.
An exhausted checker, an unsupported backend or a failed proof supplies no
capability and no accepted handle.

The initial 0.3.0 evidence format admits reifiable circuit/structured IR paths.
A certified external provider may be opaque at source level, but its admitted
capability must expose a representation that the selected Lean checker can
validate. An arbitrary device/host callback is unsupported. In particular a
`Controlled` witness used by the rules below includes a replayable controlled
implementation and checked phase-preserving inversion/recontrol transforms.
A mere black-box API promising one controlled invocation does not meet it.
This explicit premise explains why constructing `controlled(U)` can expose
more access than the source-level object `U` itself.

| Constructor | Type and formation requirement | Exposed capabilities and implementation |
| --- | --- | --- |
| `identity[A]` as an operation | `Op<A>`; valid finite basis | A, D, C from independently checked identity paths. It is an explicit object, not a capability inferred for another provider. |
| `then(U,V)` | `U:Op<A,B>`, `V:Op<B,C>`; exact middle tree | A iff both A; D iff both D, using inverse order. C follows from both C only when both factors are endomorphisms of the same exact tree. Other cases need a checked whole-composite controlled realization. |
| `tensor(U,V)` | `U:Op<A,B>`, `V:Op<C,D>` -> `Op<(A,C),(B,D)>` | A iff both A; D iff both D. C from both C when both factors are endomorphisms; use one shared control and disjoint ordered target axes, never two controls. |
| `inverse(U)` | `U:Op<A,B>` with full-space unitary laws and D(U); result `Op<B,A>` | A from D(U); D from A(U); C from C(U) only for an endomorphism, by verified inversion of its controlled path. No inverse is formed from a one-sided isometry law. |
| `controlled(U)` | `U:Op<A>` with C(U); result `Op<(Bit,A)>` | A, D, C from the replayable controlled witness and its checked transformations. Direct A(U) is still unavailable if not granted. |
| `power(U,n)` | `U:Op<A>`, canonical bounded static count `n` | Retain A/D/C requirements of U for each requested access, including `n=0`. Replay the respective path `n` times; do not unroll beyond the selected capacity. |
| `checked_op(f,M)` | Exact input/output/effect match and successful independent actual-artifact/expected-meaning check | Preserve only capabilities backed by f's implementation paths and the requested transforms. Adding a refinement does not create access. |

Every realization and transformation remains subject to its explicit work,
interface and representation bounds. Logical access never overrides a selected
backend capacity; report that failure as a limit rather than pretending an
exact equation was disproved.

The table gives the compositional derivations, not a promise that every
mathematically possible capability is inferred. A concrete transparent composite
may obtain an additional capability only by materializing and independently
checking the corresponding whole implementation. Generic checking can use only
the paths declared in its premises; a fortunate concrete specialization cannot
repair an invalid generic body.

For transparent source circuits and sealed gates, check their actual gate paths
and admitted transformations before granting capabilities. Pure unitary paths
normally support all three; dimension-changing preparation normally supports
Apply only. For source-opaque certified providers, grant exactly the admitted
paths. There is no Boolean capability flag accepted from an external producer.
A future provider format without replayable transforms would need different
rules; it is not silently covered by the 0.3.0 Controlled witness above.

`controlled(U)` accepts a **single** `Q<(Bit,A)>`; the control is the first,
least-significant flattened leaf. It returns that exact tree. It does not infer
packing from `(Q<Bit>,Q<A>)` or accept a two-argument call. Inactive controls
retain the identity action and every owner. Repeated control retains the exact
nested tree `(Bit,(Bit,A))`; it does not flatten or reorder it. For target
indices x,y and control bits c,d, the coefficient at row `d+2*y`, column
`c+2*x` is zero when c differs from d, `delta(y,x)` when c=d=0, and
`U[y,x]` when c=d=1. Tensor coefficients are
`tensor(U,V)[(b,d),(a,c)] = U[b,a]*V[d,c]`, with the first field in the low
axes. These equations fix the indexing independently of a circuit builder.

Counts use the common static Nat evaluator and the foundation's explicit
power-of-two form `2^(n)`. Negative values, overflow, noncanonical numerals and
unsupported static expressions reject before materialization. A symbolic count
has a checked finite bound; a count cannot allocate unbounded host integers,
matrices or expanded steps. Count zero denotes identity but still resolves and
checks U, its static premises and the requested capability. It does not hide
invalid declarations, stale evidence, wrong types or owner misuse. It consumes
and returns the caller's owner normally. For `U:Op<Unit>`, nonzero powers retain
its scalar phase; controlling a scalar `-1` yields an observable phase on the
control. `Unit` is a one-dimensional space, not a zero-dimensional matrix.

## A closed exact Meaning fragment

Use the following finite specification constructors in 0.3.0. The interpretation
is defined independently in Lean reference modules; compiler evaluation only
proposes a request. Meaning constructors never issue operation capabilities.

| Form | Meaning and admission condition |
| --- | --- |
| `identity[A]` | Identity `Meaning<A>`. |
| `permutation_by(f)` | `Meaning<A,B>` for a closed total bijection `f:A->B`; preserve both exact trees and canonical basis enumeration. Existing endomorphic uses are a special case. |
| `phase_by(phi)` | `Meaning<A>` with diagonal `zeta_8^phi(x)`. Initially `phi:A->(Bit,(Bit,Bit))` is closed and total; `(b0,(b1,b2))` encodes `b0+2*b1+4*b2`. No implicit conversion to `Bits<3>` is inserted. Wider exact phase values enter through their separately specified phase interface, without floating conversion. |
| `zero[A]` | `Meaning<Unit,A>` for a concrete tree of Unit, Bit, Bits and products; its sole column is the all-zero basis vector. Includes `A=Unit` and zero-width trees without identifying their source types. An opaque Basis parameter or a finite ADT without an explicitly specified zero constructor does not satisfy this formation rule. |
| `hadamard` | `Meaning<Bit>` with `(1/sqrt(2))*[[1,1],[1,-1]]`. This is a reference constructor, not a trusted executable gate. |
| `compose(M,N)` | `Meaning<A,C>` from `M:A->B`, `N:B->C`; denotation `N M`, with exact middle tree. |
| `tensor(M,N)` | `Meaning<(A,C),(B,D)>`; first component occupies low axes. The denotation is the corresponding ordered tensor action. |
| `inverse(M)` | `Meaning<B,A>` only after full-space unitary laws; denotation `M†`. There is no executable inverse merely because this mathematical term exists. |
| `controlled(M)` | Endomorphisms only, denotation `|0><0| tensor I + |1><1| tensor M` under the declared low-control indexing. Preserve global phase of M. |
| `power(M,n)` | Endomorphism repetition; zero is identity. Formation still validates M and the count. |
| `fourier[n]` | Exact positive-sign Fourier meaning on `Bits<n>`, with the basis order and supported checking profiles below. |
| `reference(f)` | Denotation of a separately selected closed pure reference artifact, retaining f's source/dependencies, interface, substitutions and checker identity. It is not the candidate artifact copied into the request. |

Each admitted pure meaning constructor carries its isometry law; the
unitary-only cases additionally check both inverse laws. These are mathematical
formation obligations, not execution access. `reference(f)` must obtain them
from the checked reference artifact rather than its source declaration.

There are no arbitrary matrix literals, algorithm-name annotations, general
projector solvers or user-supplied executable equality functions. A reflection
about a total finite predicate is derived by `phase_by`: use label 4 on the
selected basis states and 0 elsewhere. A reflection about a prepared state is
an explicit checked unitary conjugation of such a meaning. Its sign is retained.
The old `conjugate_op(U,V)` ordering is `U V U†`; the canonical operation spelling
is `then(inverse(U),then(V,U))`, with all required paths checked.

`identity`, `tensor`, `inverse`, `controlled` and `power` have static category
signatures. Category resolution determines whether their operands are meanings
or operations; mixed operands reject. Expected category and resolved argument
kinds must give one result, with no backend-dependent overload or retry. In a
`meaning` declaration the expected category is explicit; an operation argument
position similarly fixes the operation category.

Meaning equality has two layers. Structural equality after bounded static
substitution and type normalization can identify the same specification term.
Semantic equality between different terms requires the selected independent
checker. In the finite profile, evaluate to canonical exact rectangular matrices
and compare every coefficient, with phase and axis order intact. Do not quotient
by global phase, flatten tuple types, or rely on a Rust cache/matrix comparison
as acceptance. Symbolic/hierarchy equality requires an actual-artifact theorem
for its supported constructors; unmatched syntax reports unsupported equality.
Capacity exhaustion reports a limit, not inequality. Approximation belongs to a
separately typed/error-bounded contract; it cannot satisfy exact Meaning equality.

### QFT2 and QFT3 without prose-only specifications

For `N=2^n`, enumerate `Bits<n>` by `x=sum_j 2^j*x_j`. Define the output-row,
input-column coefficient as

```text
fourier[n][y,x] = 2^(-n/2) * exp(2*pi*i*x*y / 2^n).
```

No implicit output reversal is included. A circuit whose public output order is
reversed must include an explicit checked permutation in the requested meaning
or repair its implementation. For the first exact dense implementation:

```text
fourier[2][y,x] = (1/2) * i^(x*y),            0 <= x,y < 4
fourier[3][y,x] = (sqrt(2)/4) * zeta_8^(x*y), 0 <= x,y < 8
```

These 4-by-4 and 8-by-8 matrices are in the existing
`Z[1/2,sqrt(2),i]` coefficient ring. Generate the target from these equations,
not by evaluating the candidate QFT circuit. The reference proof connects that
exact generator to the complex formula and both unitary laws. The runtime
checker then binds the actual artifact to that independent target. QFT0 is
identity on `Bits<0>`, which remains distinct from `Unit`; QFT1 has the Hadamard
coefficients on `Bits<1>`, distinct from the primitive `Bit` signature.

For n above 3, this dense coefficient ring cannot in general express the needed
roots. The separate existing dyadic-phase/QFT hierarchy has a modulus-256,
width-at-most-eight mathematical profile; it must use its own exact request and
actual-graph binding, not approximate a matrix into R8. Selecting a supported
profile is explicit and cannot follow a failed finite verification. Do not
claim its temporary projection theorems already prove full-artifact acceptance.
This packet requires the QFT2/QFT3 source/refinement route and its proofs within
0.3.0; it neither raises existing capacities nor requires new maximum-width
experiments to demonstrate that bounded route.

## Instruments are a separate complete scope

`InstrumentMeaning<A,B,C>` specifies all ordered outcomes `c:C` and the residual
quantum interface B for an observing function `Q<A> -> (Q<B>,C)`. A source form
with no quantum result uses an explicit empty-output mapping, not an implicit
`Q<Unit>` discard or creation. Classical inputs are explicit finite parameters
or a separately indexed family; they are not hidden closure state.

The declaration surface is, for example:

```qli
meaning ReadZ : InstrumentMeaning<Bit,Unit,Bit> = instrument_reference(read_z_spec);
```

Here `read_z_spec` is a separately selected closed `observe` function with an
explicitly recorded empty quantum output and one ordinary Bit outcome. The
`Unit` in this instrument index describes that empty residual Hilbert space;
it does not synthesize a returned live owner. A request for a function that
actually returns `Q<Unit>` must instead retain that output owner in its interface.

The bounded 0.3.0 family consists of `instrument_reference(f)` and composition
of independently specified initialization, pure evolution and ordered readout.
The reference fixes the unnormalized outcome/residual maps, their completeness,
classical label encoding, output order and arbitrary-reference action. Checking
only probabilities or a sampled result is insufficient. Current coefficient
branch semantics can establish the stronger equality of each canonical branch
map; this is sufficient for the corresponding instrument equality. It is not a
claim that every equivalent Kraus presentation has a decidable normal form.

Instrument meanings never enter `Op`, acquire Adjoint/Controlled, or undergo
coherent control as if measurement were a unitary. Pure Meaning remains
phase-fixed even when later composed into an observing program. A complete
independently supplied instrument request must be bound to the original
observing artifact and every branch, including zero-probability outcomes and
residual/reference behavior. Implement this selected bounded family in 0.3.0;
reject unsupported instrument equality with its exact scope. A self-produced
request or a pure-leaf theorem does not complete this obligation.

## Expected meaning and artifact identity

A refined operation records at least:

- Resolved implementation and expected-meaning identities, exact retained source
  bytes and transitive dependency graph, explicit static substitutions and
  qrate/edition identities.
- Exact input/output trees, ordered physical/logical port mappings, effect and
  requested access operation; zero-width nodes and full phase conventions.
- The complete canonical actual artifact and independent expected request,
  including reference artifacts and their source/dependency identities.
- The selected compatible checker/schema, capability realization, successful
  native receipt and its actual executable-checker correspondence.

Compare structured data/full canonical encodings for attachment; a name or hash
alone is not semantic evidence. Changed source, changed request, reordered ports,
changed dependency or changed actual artifact invalidates that binding. Do not
reuse an Apply receipt as an Adjoint/Controlled receipt without checking the
corresponding transform. Cache identity includes all these distinctions.

For `reference(f)`, the guaranteed mathematical target is the checked reference
artifact's denotation under the stated assumptions. Retaining f's source binds
provenance, but does not itself prove source-to-artifact preservation. Likewise,
checking candidate/reference IR equality does not prove that the reference is
an adequate specification of the author's intended algorithm. The existing
scoped guarantees keep their exact boundaries; new theorems and any later
admission follow their ordinary procedures.

Failure before acceptance must leave no executable handle, partial result or
sample. Diagnostics identify the smallest type-tree mismatch, missing capability
and constructor path, stale binding, unsupported equality/profile, false exact
equation, or exhausted capacity. Include original module/UTF-8 span and static
instantiation chain. Rust may explain a native rejection but cannot reverse it.

## Current code and the required implementation delta

| Current implementation | Consequence for this candidate |
| --- | --- |
| `src/frontend/compile/operations.rs`: `Operation` has one basis, three access flags and an optional square matrix; `provider` requires a closed unary `unitary` with identical input/output type. | Replace the single basis with exact domain/codomain and checked law/access-path data in the common representation. Add no parallel general-arrow implementation to the sized frontend. |
| `construct` swaps inverse access, grants three capabilities for controlled access, intersects binary capabilities and retains access for zero repeats. `materialize` explicitly reverses sequences and remaps control/tensor axes. | Preserve their valid bounded behavior under the explicit witness premises above; prove each actual constructor. Do not generalize these formulas to arbitrary opaque callbacks or rectangular isometries. |
| `src/contract/meaning.rs`: `FiniteMeaning` represents endomorphic permutations and eighth-root phases; `MeaningEvidence` retains a `FunctionEvidence` receipt. | Introduce the small typed Meaning AST and independent native interpretation; include nonmonomial H/Fourier and rectangular preparation, without trusting a producer matrix. |
| `src/contract/function.rs` and `src/frontend/compile/lower/function_contract.rs`: original implementation/specification IR and source snapshots are retained; native checking is authoritative. | Generalize the boundary to exact A/B and reference/meaning requests. Preserve stale-source/artifact rejection and distinguish reference IR equality from source preservation. |
| `src/contract/exact.rs`, `src/contract/mod.rs`: dimensions at most 64, six contract bits, 1024 circuit steps, i128/dyadic coefficient limits and explicit work budget. | Preserve bounded dense admission. The generic type checker must not confuse these capacities with the grammar or the separate hierarchy profile. |
| `lean/Qleisli/SemanticContract.lean`: mathematical rectangular encoded/isometry/unitary, composition, tensor, reference and control laws. | Reuse mathematics, but add correspondence from the actual new request/constructor definitions. An abstract law is not a parser/native binding theorem. |
| `lean-kernel/QleisliKernel/Semantics/Preparation.lean`, `lean/Qleisli/Semantics/Exact.lean`, `Finite.lean`, `Instrument.lean`: independent zero-factor, scalar, circuit and branch meanings. | Keep reference definitions independent of acceptance; extend them only with explicit equations and scoped evidence. |
| `lean-kernel/Protocol/NativeContract.lean` and `lean/Qleisli/NativeContract.lean`: original bytes/request binding and bounded unitary leaf meaning/reference laws. | The leaf branch has equal-basis, closed unitary premises. It does not already establish this candidate's rectangular/isometric or complete observing-request contract. The encoded branch's root meaning also does not identify its wrapper with the original operator automatically. |
| `lean/Qleisli/Qft.lean`, `QftUnitary.lean`: exact Fourier mathematics with explicitly temporary projection interfaces. | Connect the new independent Fourier request to actual checked artifact/axes; do not relabel a projection theorem as whole-program source preservation. |

## Migration, counterexamples and completion

The one 0.3.0 cutover maps old `Op<A,M>` to `Op<A, meaning M>`, old endomorphic
`meaning M : A = ...` to `meaning M : Meaning<A> = ...`. The separate naming
decision maps `bind_op` to `checked_op`; it adopts none of these other proposed
migrations or the extended argument contract.
Map `inverse_op`, `then_op`, `tensor_op`, `controlled_op` and `repeat_op(n,U)`
to `inverse`, `then`, `tensor`, `controlled` and `power(U,n)`. Map
`adjoint(U,q)`/`repeat_static(n,U,q)` to constructed applications. Preserve the
old phase-label bit order explicitly when migrating helper result types.
A second positional basis in `Op<A,B>` is always a codomain; an old meaning
identifier in that slot gets a located migration diagnostic, not a second
parser interpretation. Do not retain the old grammar as a runtime fallback.

| Positive/negative pair | Required observation |
| --- | --- |
| `then(U:A->B,V:B->C)` / equal-width but different middle tree | Accept the exact interface; reject the substitute without implicit coherence. |
| `zero[Bit]` / `inverse(zero[Bit])` | Check preparation isometry; reject total inverse on arbitrary Bit, including the `|1>` counterexample. |
| `controlled(U)` with only C(U) / direct `U(q)` | The first has a checked controlled implementation; direct Apply is unavailable. |
| `inverse(U)` with D(U) / unitarity evidence alone | Check inverse path and two-sided law; reject missing executable access. |
| `power(U,0)` with valid required paths / missing name, invalid body, false static premise or stale provider | Identity behavior still consumes/returns the owner; every invalid operand is diagnosed even at zero. |
| `Op<Unit>` scalar -1 / scalar +1 under a superposed control | Distinguish the observable relative phase; reject any erased empty owner or phase. |
| `tensor(U,V)` / swapped operands, flattened tree or aliased targets | Preserve ordered type trees, axes and disjoint live owners. |
| QFT2/QFT3 exact target / wrong sign, missing reversal, swapped output order or extra global -1 | Check all small exact coefficients plus an entangled reference; every changed meaning rejects. |
| `checked_op(then(H,H),identity[Bit])` / `checked_op(H,identity[Bit])` | Proposed extended inputs: accept exact identity composition; reject the single H. No request derived from the candidate itself. |
| Retained refinement / modified source, dependency, request, artifact or capability realization | Reject stale attachment without a new independent check. |
| Complete observing reference / same histogram with wrong residual state or outcome ordering | Compare the full instrument, not a sample or marginal. |
| Named static builder / environment capturing q or a spent/empty quantum owner | Allow bounded static composition; reject hidden live ownership before specialization. |

The existing regressions in `tests/static_operations.rs`,
`tests/meaning_evidence.rs`, `tests/function_contracts.rs` and the sized source
and native rejection suites are starting evidence to migrate, not tests of this
unimplemented surface. Preserve their original sources and append translated
examples; do not rewrite historical failures into successes.

Implementation is complete only after the common AST/type/effect/owner checker,
static constructors, exact requested-meaning evaluator, actual native binding,
relevant executable-definition proofs and the small positive/negative packet
all agree. Keep capacity/unsupported failures explicit while implementing;
the selected rectangular, QFT2/QFT3 and bounded instrument routes remain 0.3.0
acceptance work. No new maximum-size quantum experiments are needed. This
candidate was reviewed against source and current Issue text only; no new
Rust/Lean execution, proof result, release readiness or guarantee discharge is
claimed here.
