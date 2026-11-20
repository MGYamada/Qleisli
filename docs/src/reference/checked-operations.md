# Checked operations

A **checked operation** is the static constructor
`checked_op(implementation, Meaning)`. A program writes one where it passes an
operation to a function that asks for an operation with a stated meaning. The
constructor requests a check that a source operation has a declared exact
meaning.

A **Meaning** is a declaration `meaning M: A -> B = ...;`. It specifies the
exact action of an operation from basis tree `A` to basis tree `B`.

A program writes `checked_op` inside the existing explicit operation
arguments. It is not a monadic bind, a runtime function value or a
constitutional certification.

## The `checked_op` constructor

```text
CheckedOperation ::= checked_op ( Identifier , Identifier )
```

The constructor takes two names. The first identifier names an existing
operation. The second resolves to an existing finite Meaning declaration.

Rules:

- Visibility, lexical shadowing, static premises and the checks of the basis
  trees apply to both identifiers.
- Neither argument may be a runtime value, a constructed operation expression
  or an explicitly specialized provider expression.
- An outer static constructor may contain a checked operation. Its own rules
  do not change.
- For a general formal `Op<A -> B, M>`, the checker checks both ports against
  the declared domain and codomain of `M`. An endomorphic Meaning has one
  basis tree for its input and its output. It requires both ports to equal
  that single basis tree. The
  [type model](type-model.md#general-pure-operation-arrows) specifies how
  general pure arrows are typed and the limits on materializing them.
- Attaching a Meaning name does not discharge the equality. Equal
  probabilities, equal bit width or equality up to global phase must not
  replace the check.
- Capability requirements are separate. An abstract parameter acquires no
  inverse access and no controlled access from a Meaning name.

The checker accepts this fragment. It uses an endomorphic Meaning and the
grammar of operation parameters:

```qli
use std::gate::z;

classical fn z_phase(b: Bit) -> (Bit, (Bit, Bit)) { (0, (0, b)) }
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn direct(q: Q<Bit>) -> Q<Bit> { z(q) }

unitary fn apply_z[const U: Op<Bit, ZMeaning>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) { U(q) }

unitary fn client(q: Q<Bit>) -> Q<Bit> {
    apply_z[checked_op(direct, ZMeaning)](q)
}
```

> **Implementation note.** The common original-source judgment resolves the
> operation and the Meaning, checks their interface bases and records a pending
> Meaning-equality obligation. It can resolve an in-scope abstract operation
> formal and record the obligation for it. Finite materialization requires
> closed pure source declarations, so it rejects an abstract formal as the
> provider of this constructor. Attaching a Meaning in the common judgment
> creates no evidence that bypasses that refusal. Finite materialization
> retains the implementation and its source dependencies. It checks their
> phase-fixed meaning through the selected native checker before it produces
> executable evidence.

> **Implementation note.** The parser reads each argument of `checked_op`, and
> each operand of a Meaning body, as a reference name. A reference name may be
> a qualified path. No conformance test covers a qualified name in these
> positions.

## Owners and capabilities

A static description contains no live quantum owner.

Rules:

- Applying an operation consumes and returns the specified owners.
- A runtime local, a spent value or a captured owner must not be the provider
  of an operation.
- Separate owners do not imply separable states.
- A zero-width owner retains its phase and its ownership rules.

<a id="bounded-exact-meaning-composition"></a>

## Meaning declarations

A Meaning declaration names a specification: the exact action of an operation
from one basis tree to another. A finite Meaning declares
`meaning M: A -> B = ...;`. The form `meaning M: A = ...;` is short for a
Meaning whose input and output trees are equal. A Meaning has one of these
bodies:

```text
MeaningBody ::= permutation_by ( Identifier )
              | phase_by ( Identifier )
              | reference ( Identifier )
              | compose ( Identifier , Identifier )
              | tensor ( Identifier , Identifier )
```

Rules:

- `reference`, `compose` and `tensor` are contextual identifiers in this
  position. They are not reserved words.
- The operands of `compose` and `tensor` resolve to declared Meanings through
  the ordinary visibility rules. `reference` resolves its function as
  [Reference programs](#reference-programs) describes.
- A runtime value or the name of a classical function is not a Meaning
  operand.
- A Meaning may refer to a Meaning that the module declares later. A
  dependency cycle is an error.
- The checker checks every declared Meaning, including an unused one.

### Composition

A `compose` body specifies one Meaning followed by another. For
`First: A -> B` and `Second: B -> C`, `compose(First, Second)` has type
`A -> C`. It applies `First` and then `Second`.

Rules:

- The codomain of `First` and the domain of `Second` must be the same tree
  `B`. The checker makes no implicit conversion between trees of equal
  physical dimension.
- In the endomorphic monomial case, where `First` and `Second` both have the
  basis tree `A`, `meaning M: A = compose(First, Second);` applies `First` and
  then `Second`. Write the actions as `First|x> = zeta_8^a[x] |p[x]>` and
  `Second|y> = zeta_8^b[y] |q[y]>`. The result sends `x` to `q[p[x]]` with
  phase `(a[x] + b[p[x]]) mod 8`.

### Tensor

A `tensor` body specifies two Meanings side by side, one on each field of a
pair. For `Left: A -> B` and `Right: C -> D`, `tensor(Left, Right)` has type
`(A,C) -> (B,D)`. It assigns the left operand to the low-order axes.

Rules:

- In the endomorphic monomial case, `Left` has basis `A` and `Right` has
  basis `C`. The declaration `meaning T: (A, C) = tensor(Left, Right);` then
  requires that ordered pair.
- The first field occupies the low-order axes. For dimensions `dA` and `dC`,
  column `x + dA*y` goes to `p[x] + dA*q[y]` with phase `(a[x] + b[y]) mod 8`.
- Nested products and zero-width fields retain their type identity. In
  particular, a scalar phase on `Unit` is not discarded.

### Equality of Meanings

A check against a Meaning is a check of exact equality. The rules below say
what that equality observes. The checker accepts these declarations:

```qli
classical fn flip(b: Bit) -> Bit { not b }
classical fn z_phase(b: Bit) -> (Bit, (Bit, Bit)) { (0, (0, b)) }
meaning X: Bit = permutation_by(flip);
meaning Z: Bit = phase_by(z_phase);
meaning ZX: Bit = compose(Z, X);
meaning Ordered: (Bit, Bit) = tensor(Z, X);
```

Rules:

- Equality retains every column, the exact phase and the axis order. It is not
  probability equality, and it is not equality up to global phase. For
  example, `compose(X, Z)` differs from `ZX` by a minus sign.
- Either operand of `compose` or `tensor` may contain references or monomial
  targets. Equality observes the exact complex phase and the ordered basis
  trees. It also observes the scalar action on `Q<Unit>`, which has zero
  axes.
- Forming a target does not prove a provider correct. `checked_op` and refined
  parameters require a fresh native comparison against the independently
  formed request. That comparison retains the original identities of the
  source, of the dependencies and of the provider.
- Forming a Meaning creates no live owner and no inverse or control
  capability. The capability checks and the source-control checks govern
  those uses.

> **Implementation note.** For monomial operands, `compose` and `tensor`
> normalize their targets within the six-bit finite bound and the work limits.
> A reference graph is retained even when its denotation is monomial, such as
> a reference to the identity or `compose(H, H)`. The public monomial-only
> `FiniteMeaning` accessor rejects every graph that contains a reference.

### Reference programs

A `reference` body uses a program as the specification. A program writes one
when an ordinary function already states the action that it wants. For
example, `meaning H: Bit = reference(reference_h);` names one closed ordinary
function as the specification.

Rules:

- For the equal-tree form `meaning M: A = reference(f);`, `f` must have the
  interface `Q<A> -> Q<A>`. The checked effect that callers of `f` see must be
  Unitary. In the example, the interface is `Q<Bit> -> Q<Bit>`.
- For the rectangular form `meaning M: A -> B = reference(f);`, `f` must have
  the interface `Q<A> -> Q<B>`. The checked effect that callers of `f` see
  must be at most Isometry.
- The argument must be a single resolved function identifier. Static
  arguments, constructed operations, classical or static functions and other
  Meaning names are not accepted.
- Visibility checks apply. The dependency-cycle check covers all declarations,
  including cycles through `apply_contract` and `checked_op`.
- A declared effect assertion must not replace independent checking of the
  complete body and its dependencies.
- The [public-effect rule](source-text.md#ordinary-function-effects-and-assertions)
  applies. Outside the original module of the provider, it uses the checked
  public effect. Inside that module, it uses internal inference. Reference
  selection, specialization and cached evidence must not recover a sharper
  external eligibility from the body.

The checker accepts these declarations:

```qli
fn reference_h(q: Q<Bit>) -> Q<Bit> { h(q) }
meaning H: Bit = reference(reference_h);
meaning HH: Bit = compose(H, H);
```

> **Implementation note.** A reference contributes its independently checked
> original Raw artifact and its dependencies. A fresh native equation compares
> the implementation with that request. For endomorphic functions, the emitted
> contract receipts retain both artifacts, their dependencies and the original
> source snapshot. Rectangular provider bodies and reference bodies receive
> separate native equations, and the Raw call intervals are rechecked against
> the requested matrix. A matching matrix, function name or source annotation
> cannot substitute another receipt. Unused targets, unused generic equality
> obligations and zero-repeat child requests are checked before emission.

### Fixed Fourier specifications

The following closed reference functions specify the positive Fourier matrices
on two and three qubits in the existing exact carrier. They are fixed
examples. They are not a generic QFT implementation, and they add no `Fourier`
constructor.

```qli
use std::gate::s;
use std::gate::t;

fn quarter(q: Q<Bit>) -> Q<Bit> { s(q) }
fn eighth(q: Q<Bit>) -> Q<Bit> { t(q) }
fn fourier2(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b)=split(q);
    let b=h(b);
    let (a,b)=controlled(quarter)(a,b);
    let a=h(a);
    join(b,a)
}
fn fourier3(q: Q<((Bit,Bit),Bit)>) -> Q<((Bit,Bit),Bit)> {
    let (ab,c)=split(q);
    let (a,b)=split(ab);
    let c=h(c);
    let (b,c)=controlled(quarter)(b,c);
    let (a,c)=controlled(eighth)(a,c);
    let b=h(b);
    let (a,b)=controlled(quarter)(a,b);
    let a=h(a);
    join(join(c,b),a)
}
meaning F4: (Bit,Bit) = reference(fourier2);
meaning F8: ((Bit,Bit),Bit) = reference(fourier3);
```

With low-order axes first, the independent equation for the fixed dimensions
`N = 4` and `N = 8` is

\\[
F_N[y,x] = \frac{\exp(2\pi ixy/N)}{\sqrt{N}}.
\\]

The fixed reference regressions check every coefficient on both concrete
adapters, including the output reversal and the exact phase. A consumer can
use these targets in `apply_contract` or `Op<A,M>` under the same evidence rules.

## Migration from `bind_op`

`bind_op` is the retired spelling of the constructor. To migrate a source,
replace `bind_op(implementation, Meaning)` with the identical arguments to
`checked_op(implementation, Meaning)`.

Rules:

- `bind_op` is reserved only for a located retirement error. It is never
  accepted as an alias, including in nested constructors.
- The [lexical boundary](source-text.md) specifies reserved identifier
  collisions, comments, byte spans and the order of diagnostics.
- Retained evidence includes exact source snapshots. A change of this spelling
  may therefore change a receipt or a QIRF source identity, even when the
  requested mathematical meaning and the ordered interface are unchanged.
- Reconstruct the evidence for the migrated source and check it
  independently. Do not reuse stale receipts, and do not remove source
  bindings to force byte equality.

## Status and limits

Limits:

| Limit | Value |
| --- | --- |
| Finite Meaning equations | The six-bit bound of the exact carrier, with its arithmetic and work limits |
| Cells of a reference expression graph | 4,096 |
| Depth of a reference expression graph | 64 |
| Aggregate materialized artifact bytes of a reference expression graph | 100,000 |

- The selected adapter also applies limits of its own: on call depth and
  dependency depth, on operations, on source snapshots and on aggregate
  providers. An expression within the limits above is not a promise that
  every concrete profile can materialize it.
- Exhaustion or an unsupported equality is rejected without approximation.
- The native acceptance profiles are unchanged.

Profiles:

- The finite source route supports its closed observing entry.
- The selected hierarchy route supports its pure input/output entry for these
  refined operations. A readout entry outside that profile is rejected.
  Meaning composition broadens no readout or instrument rule.
- For general arrows and rectangular Meanings, the ordinary project adapter
  and the selected Raw adapter validate original pure bodies and their
  dependencies against two-port `pure-leaf` requests. Native checking
  reconstructs the matrix, checks `V†V = I`, and retains the exact phase and
  the ordered ports. Raw alpha-renaming and composition produce untrusted
  candidates that need fresh checking.
- The hierarchy finite-leaf profile is square.
- Observing contracts use the separately adopted
  [function instrument overload](type-model.md#direct-runtime-transforms-and-opaque-operations),
  not a pure Meaning constructor.
- Two things are outside this bounded profile: general symbolic equality, and
  arbitrary hierarchy requests that compare a matrix with a composite. An
  unsupported comparison is rejected.
- A provider outside its concrete profile is rejected. It does not lose its
  Meaning request. Other static constructors retain their explicit projection
  restrictions.

The selected concrete projection retains the `checked_op` constructor and its
original Meaning request. Within the profile of supported closed providers,
it checks Meanings as follows:

- `ElaboratedProgram::check_operation_meanings` checks the original binding
  requests and the annotated constructor descendants through the native finite
  gate, on their materialized Raw bodies. Only then can the checked collection
  produce a hierarchy proposal. That proposal needs fresh hierarchy
  acceptance.
- Direct unchecked hierarchy lowering or Raw lowering is rejected while
  original Meaning obligations are open.
- The checked collection can emit Raw for direct application, sequential
  composition, tensor composition, adjoints and controlled access. An
  independent source replay checks the instruction interval, the owner
  boundary and the ordered axes against each original finite request through
  a fresh native decision.
- Unexecuted child requests and zero-repeat child requests are checked before
  emission.
- For inverse access and controlled access, the independent source traversal
  retains the substep range and the axis boundary of each original subtree,
  including requests hidden inside called definitions. Inversion reverses that
  range and its boundary. Coherent control retains the inactive identity
  sector and the exact active-sector matrix.
- Coordinate reconstruction follows the same surrounding controls. It
  preserves metadata-only axis changes and the Unit phase.
- These finite equations use the six-bit bound, the shared work budget and the
  final whole-artifact acceptance. All finite equations and the sector replay
  consume the same caller budget.
- Refined Raw source `ctrl` uses the exact sector gate as well as the Meaning
  gate.
- Closed audit roots are re-elaborated, and all their original Meaning
  requests are checked in that expanded graph. Earlier leaf keys are not
  transplanted.
- Every original control obligation requires a retained concrete call
  interval, including unused bodies and specializations. Unclosed generic
  intervals and erased intervals are rejected.
- A body can contain source `ctrl`. Symbolic inverse transformation or
  symbolic control transformation of such a body is unsupported. The failure
  selects no other profile.
- The complete emitted artifact requires fresh native validity and source
  replay before execution.

Proof status:

- These checks are bounded implementation checks and artifact-attachment
  checks. They are not a proof that source elaboration preserves its intended
  meaning, or that a reference program is an adequate specification.
- These checks do not establish general source-to-request preservation.
- The adopted QS, PR, RS and EXACT interpretations, both scoped QLV1
  guarantees and their open proof duties retain their recorded status. This
  chapter reports no guarantee and no source-preservation theorem.

## History

- The name `checked_op` is the ordinary naming decision recorded in
  [#82](https://github.com/MGYamada/Qleisli/issues/82). The rename changed no
  syntax-tree meaning, primitive, protocol, schema, checker or constitutional
  edition. The later bounded implementation retains the independent evidence
  gates.
- General arrows and rectangular Meanings were resumed for 0.3.0-beta under
  [#83](https://github.com/MGYamada/Qleisli/issues/83).
- The retired [operations design packet](../design/operations.md) proposed
  broader arrow and Meaning forms and constructed provider inputs. The naming
  decision does not adopt them.
- Historical first sources and diagnostics are unchanged. They sit beside
  explicit derivatives for the renamed spelling.
