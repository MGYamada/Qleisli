# Type foundation and common frontend decision candidate

**Status: nonnormative design analysis with selected target rules.** This packet
proposes the common frontend and the minimum explicit 0.3.0 type surface. The
selected type rules are recorded in the Reference linked below; the remaining
choices are candidates. This packet does not implement a feature, issue a
Guardian ruling, or discharge a guarantee. Examples below are desired
0.3.0 source unless explicitly labelled current behavior. They are not reported
as compiled. The [authority hierarchy](../reference/authority.md) and
[production boundary](../reference/production-boundary.md) govern the work.

The [target type contract](../reference/type-model.md) now selects the ordinary
Bit literals, exact tree distinctions and explicit generic boundary as ordinary
implementation choices under the approved plan. It does not record a new human
Guardian ruling. Other recommendations in this packet, including the operator
and capability details, remain candidates until their grouped decision is made.

The approved implementation order is one source AST, module/name resolver,
static elaboration and type/ownership checking, followed by separate finite and
hierarchy lowerings. New language features must use that common frontend.
The release performs one 0.3.0 source cutover with a migration mapping; it does
not support two competing source dialects. Edition remains **2026**, identifying
the constitutional regime. Release compatibility carries this syntax change.

## Decision basis and scope

| Basis | Status used by this packet |
| --- | --- |
| [#22](https://github.com/MGYamada/Qleisli/issues/22), [#27](https://github.com/MGYamada/Qleisli/issues/27), [#43](https://github.com/MGYamada/Qleisli/issues/43) | Adopted conceptual direction: ordinary finite types are unmarked, `Q<T>` is linear ownership, there is no `C<T>` universe, and `Q<Unit>` retains its owner and scalar phase. The implementation does not yet meet that surface. |
| [#84](https://github.com/MGYamada/Qleisli/issues/84), [#100](https://github.com/MGYamada/Qleisli/issues/100) | Recorded 0.3.0 boundary: distinguish definitional equality, canonical coherence and physical maps; infer only unique static structure, never quantum meaning. |
| Approved implementation plan | A common frontend precedes new features; use one 0.3.0 source cutover and retain edition 2026. |
| Selected conservative type contract | Preserve the existing exact type distinctions: `Bit` / `Bits<1>`, `Unit` / `Bits<0>`, immediate tuple arity and nesting. Insert no implicit coherence or physical conversion in this foundation. The target Reference records these ordinary implementation choices under the approved plan, not separate human rulings. |
| [#44](https://github.com/MGYamada/Qleisli/issues/44), [#45](https://github.com/MGYamada/Qleisli/issues/45), [#46](https://github.com/MGYamada/Qleisli/issues/46), [#83](https://github.com/MGYamada/Qleisli/issues/83), [#89](https://github.com/MGYamada/Qleisli/issues/89) | Open design details: basis kinds, operator input/output interfaces, meaning and capability judgments, specialization/evidence responsibility and callable categories. The concrete rules below are recommendations for maintainer judgment. |
| [#32](https://github.com/MGYamada/Qleisli/issues/32), [#33](https://github.com/MGYamada/Qleisli/issues/33), [#35](https://github.com/MGYamada/Qleisli/issues/35), [#37](https://github.com/MGYamada/Qleisli/issues/37), [#196](https://github.com/MGYamada/Qleisli/issues/196) | Surface normalization and its child choices. Issue examples do not individually adopt grammar. The three-level `q***` / `Q<T>` / ordinary distinction is incorporated by adopted #27. |
| [#197](https://github.com/MGYamada/Qleisli/issues/197) | Explicitly later, 0.4.0 convenience work: automatic coherence, richer patterns, omitted static arguments and general cross-stage reuse policy. This packet does not pull those conveniences forward. |
| [#63](https://github.com/MGYamada/Qleisli/issues/63) | Bounded constant/static computation remains 0.3.0 work. It must use the common evaluator; it is not deferred with the general 0.4.0 meta-language. |

This is a foundation packet within the full 0.3.0 plan. It does not close the
later 0.3.0 work on `qfor`, `qmatch`, views, operations/capabilities, semantic
refinement, effects, traits or finite ADTs. Their shared representations and
entry points belong here; their additional rules require their own decisions
and tests. Deferring a convenience under #197 does not defer its 0.3.0 safety
law or the whole parent Issue.

## Current implementation and the required convergence

The following observations come from the current repository, not from a
proposed public contract. Paths refer to the
[repository](https://github.com/MGYamada/Qleisli).

| Area | Current finite frontend | Current sized frontend | Required common result |
| --- | --- | --- | --- |
| Syntax | `ast.rs`, `lexer.rs`, `parser.rs`; one shared grammar produces the recursive module AST with declarations and imports. A finite-profile preflight rejects unsupported forms before lowering. | Uses the same parsed module and spans; `sized/parser.rs` projects that AST into the existing sized checker. Its current profile still permits one function per module. | Common parsing and declaration identities are implemented; converge lexical bindings and profile checking next. Backend choice cannot select a grammar. |
| Types | Uses the shared internal `types::Type<N>` with explicit `Q`, exact tuple shape and a separate basis/runtime stage. Current source-level ordinary `Bit` still rejects. | Symbolic and concrete types use the same internal tree with symbolic or closed sizes; existing source spellings and public accessors remain profile adapters. | Shared structural equality and linear classification are implemented. Converge the source typing judgments and canonical ordinary `Bit` / `Bits<n>` surface next. |
| Ordinary finite expressions | Separate `BasisExpr` and ordinary expression variants; `0/1` are basis literals and `true/false` are ordinary `CBit` literals. | Sized expressions focus on providers, static conditions and folds. | One expression/pattern tree; staging is a checked judgment, not a second parser. |
| Modules and names | `project.rs` loads source trees; the shared `resolve.rs` declaration table supplies imports, visibility, canonical names and graph traversal to compilation. | Explicit module maps use that same table for checking, host/provider selection and concrete elaboration. Existing profile policies remain explicit. | Collection-local definition identities and global lookup are implemented. Converge lexical binding identities, multi-declaration checking and cycle/profile rules next; preserve canonical source/evidence identity rather than serializing these internal IDs. |
| Generic checking | Finite static operation parameters and abstract capability checks. | Symbolic natural constraints, explicit providers, decreasing self-recursion and bounded concrete elaboration. | One generic judgment and one specialization engine, with explicit constraints and source provenance. |
| Owners and effects | Checked during finite lowering; lexical projection and complete branch frames are explicit. | Separate symbolic and concrete ownership checks; tuple shape, moved binding identities and static carries are explicit. | One source ownership/effect judgment before lowering, plus independent downstream IR checking. |
| Lowering | Finite raw/QIRF proposals reach `native::Kernel`. | `ElaboratedProgram::lower` emits an untrusted hierarchy proposal, then dedicated native checks apply. | Two backend adapters consume the same typed source representation. Neither adapter redefines source typing or grants acceptance. |

The current sized elaborator distinguishes width-one registers from bits;
finite products retain immediate arity and nesting. These distinctions must
survive convergence. Existing capacities differ: finite basis checking permits
up to 12 bits, concrete sized registers up to eight, and elaboration has separate
call/fold/depth/storage limits. Common parsing does not silently raise any
capacity, impose a dense finite limit on every hierarchy, or turn an unsupported
lowering profile into a source typing error.

## Proposed judgments and type identity

Use three contexts in the implementation of the adopted `Γ ; Δ` discipline:

```text
Σ                      static kinds, substitutions, requirements and providers
Γ                      ordinary values with their permitted copy/drop behavior
Δ                      live quantum owners, identities, exact types and frame
Σ ⊢ T type             well-kinded source type
Σ ⊢ s : K              static expression of kind K
Σ ; Γ ; Δ ⊢ e : T ! ε ⊣ Δ′
                       expression type/effect and remaining ownership
```

Separating `Σ` is an elaboration detail, not a new classical modality. Names
identify declarations or bindings; names, lifetimes and equal widths are not
semantic evidence. Mixed ordinary/quantum tuples are unrestricted only when
every field is unrestricted. A value containing any `Q` field carries those
linear obligations even when its total physical width is zero.

The initial finite grammar is:

```text
A ::= Unit | Bit | Bits<n> | basis-parameter | (A, A, ...)
T ::= A | Q<A> | (T, T, ...)
K ::= Nat | Basis | Op<A> | Op<A,B> | Meaning<A> | Meaning<A,B>
```

`Nat` is a static kind in this foundation; this does not introduce unrestricted
runtime natural numbers. `Basis` ranges over finite ordinary type trees, not
live quantum data. Here `A` and `B` independently range over basis trees.
Recommend an internal domain/codomain representation for #83, with `Op<A>` and
`Meaning<A>` the endomorphic abbreviations. This is a proposed resolution of
the operator-interface fork, not an existing general-arrow API.
`Meaning<A,B>` denotes a static mathematical description; using it as a
refinement requires evidence binding the actual implementation. Effects and
capabilities determine which such arrows are admissible and executable.
Finite ADTs enter the same ordinary universe when their separate rules are
implemented. They are not admitted merely by an ellipsis in a type grammar.

Type identity is structural after permitted static natural evaluation:

- Constructor tags, immediate product arity, nesting and left-to-right leaf
  order must match. A binary product and a nested product are not flattened.
- `Bit` differs from `Bits<1>`; `Bits<0>` differs from `Unit`.
- `Q<(A,B)>` differs from `(Q<A>,Q<B>)`. Packaging is explicit, and separate
  owners never assert separability of their joint state.
- `((A,B),C)`, `(A,(B,C))` and `(A,B,C)` are distinct trees.
- Equal widths, cardinalities or Hilbert-space dimensions do not identify
  types, interfaces, evidence or specialization keys.
- The ordinary singleton value `()` has type `Unit`. It never stands for a
  live `Q<Unit>` or `Q<Bits<0>>` owner.

For symbolic `Bits<n>`, equality requires the two-way natural equality
obligation under the same explicit premises. A bounded solver may reject when
it cannot establish that obligation; lack of a counterexample is not evidence.
No solver substitutes a quantum map to make types agree.

Coherence and physical operations remain explicit. Split/join and future
reassociation/unit maps must carry their specified ordered, phase-`+1`
structure and be checked independently. Removing an empty owner must not erase
a scalar operation on it. In particular, controlling `[-1] : H(Unit) → H(Unit)`
must retain its nontrivial relative phase. Pure zero-width introduction and
elimination require their explicit checked maps; this packet adopts no public
spelling for them and no generic conversion `Q<A> → A`.

## Proposed source grammar and callable boundary

The following grammar gives the concrete binder and application fragment for
the foundation, with the literal/refinement choices called out below. Existing
declaration and special-expression productions must be ported into the same
grammar; this fragment is not the complete 0.3.0 grammar or authority to admit
an unspecified production. It specifies no legacy aliases. `Path` and identifiers
use the shared lexer; semantic category resolution follows parsing.

```text
Module       ::= Use* Declaration*
Function     ::= [pub] Effect fn Ident [StaticParams] (Params) -> Type
                 [requires Requirements] Block
Effect       ::= unitary | iso | observe
StaticParams ::= [ static Ident : Kind (, static Ident : Kind)* [,] ]
Params       ::= empty | Pattern : Type (, Pattern : Type)* [,]
Pattern      ::= Ident | _ | () | (Pattern, Pattern (, Pattern)* [,])
Block        ::= { Statement* Expr }
Statement    ::= let Pattern [: Type] = Expr ; | Expr ;
Call         ::= Callee [StaticArguments] (Arguments)
StaticArguments ::= [ StaticExpr (, StaticExpr)* [,] ]
Arguments    ::= empty | Expr (, Expr)* [,]
StaticNat    ::= numeral | static-name | (StaticNat)
               | StaticNat + StaticNat | StaticNat - StaticNat
               | StaticNat * StaticNat
StaticTest   ::= StaticNat (== | != | < | <= | > | >=) StaticNat
PowerCount   ::= StaticNat | 2 ^ (StaticNat)
```

Square brackets in `StaticParams` and `StaticArguments` are literal tokens;
other brackets in this display mark optional syntax. Empty static lists are
omitted. Multiplication binds more tightly than addition/subtraction; these
binary operations associate left. Calls bind more tightly than Boolean
operators; `!` binds before `&`, which binds before `^`. `()` is an ordinary
unit expression; `(e)` groups an expression; tuples have at least two fields.
Singleton tuples are outside this candidate. Trailing commas do not create a
different type or argument count. Existing special constructs must have explicit
AST cases; they must not be recognized by source-text heuristics after parsing.

Specializing `f` with `[s]` and then applying `(e)` first substitutes explicit
static parameters with `s`, then applies the resolved callable to `e`.
Parentheses alone do not select an evaluation stage.
For a resolved quantum function or applicable operation they supply runtime
arguments; for a resolved static builder they supply only static arguments.
Thus `inverse(U)` constructs a static description, and the following `(q)` in
`inverse(U)(q)` applies that description to a live owner. There is no runtime
closure intermediate, and a runtime value in a static builder rejects. Brackets
never mean runtime indexing in this fragment. Resolution must identify one
category before argument checking; parser retries or contextual guesses cannot
choose a callable category.

Preserve the sized frontend's explicit power-of-two repetition description when
mapping `repeat_op` to `power(U, count)`. `PowerCount` is a static count category;
its exponent form does not change ordinary Bit XOR precedence. Keep a bounded
counted representation until the selected backend requires expansion, and check
its capacity before expanding. This does not grant arbitrary symbolic nonlinear
arithmetic for sizes or bypass a backend's count limit.

Build an immutable module declaration table before resolving imports. Reject an
import that collides with a local declaration or another imported binding;
apply identical visibility and identity rules to project-loaded and explicit-map
modules. Lexical binders resolve to stable identities, while static and runtime
category checks remain explicit. Retain qualified definition identities through
specialization; equal unqualified names never bind provider evidence.

This uses the current three quantum effect spellings while keeping callable
category separate. It does not settle the later effect-class packet or make
every ordinary finite function a unitary quantum operation. `basis fn` and
`meaning` declarations need shared declaration/expression nodes with explicit
stage/category tags; their existing meaning is not removed by replacing the
two ASTs. A category tag does not grant inverse/control access.

Recommended callable rules for the foundation are:

| Category | Allowed role | Required rejection |
| --- | --- | --- |
| Named quantum function | First-order source call with explicit parameters, effect and one result interface | Runtime function values or hidden quantum captures |
| Ordinary finite function | One finite body with its explicit admissible evaluation/lifting uses | Reading a `Q<A>` through ordinary application; silently inferring coherent lift |
| Static `Op<A,B>`; `Op<A>` abbreviates `Op<A,A>` | A static description over exact input/output bases; application needs declared `Apply` access | Treating the description as a live owner, semantic existence as executable access, or an ambiguous callable category |
| Static operation builder | Bounded construction such as `inverse(U)` or `power(U, n)`; no live owner is an argument to static evaluation | General host evaluation, unrestricted recursion or capturing `Q<A>` |
| Meaning/refinement description | Static target data, independently checked against the actual artifact | Accepting a claimed meaning because its declaration exists or its name matches |
| Closure/lambda | No new closure surface in this foundation | In particular, unrestricted values hiding quantum owners; linear closures remain future work |

Under the proposed arrow representation, `then(U,V)` requires the exact output
tree of `U : Op<A,B>` to match the input of `V : Op<B,C>` and produces
`Op<A,C>`. Tensoring `Op<A,B>` and `Op<C,D>` produces
`Op<(A,C),(B,D)>` in that explicit order. No implicit reassociation repairs
composition. `Meaning` composition uses the same interfaces but never grants
implementation capabilities. The #45/#46/#83 decision must define which pure
arrows are unitary or isometric, preparation's `Unit → A` interface, and the
supported capability derivations. A general arrow does not obtain a callable
adjoint or control operation merely from its type; an isometry's mathematical
adjoint need not be an executable total inverse. Observation instruments must
have their separately decided effect/meaning rule. These are 0.3.0 obligations,
not features silently deferred by choosing an endomorphic example here.

The resolved callable stores **parameter-list arity separately from product
types**, its exact owner packaging, result tree, effect, capabilities and static
dependencies. Thus `f(a,b)` and `f((a,b))` remain different calls. A constructed
`controlled(U)` must declare its control/target calling convention explicitly;
the compiler must not infer packing to repair its application. `inverse(U)(q)`
and `power(U, n)(q)` parse as a static construction followed by application;
they do not imply runtime first-class callables.

Use one pattern parser and one shape judgment in ordinary parameters, finite
parameters, `let`, and already admitted structural binders. Pattern matching
deconstructs a tuple value; it does not implicitly split a `Q<tuple>`. Duplicate
names reject. `_` and discarded expression statements require an unrestricted
value. A quantum-containing field, including an empty owner, cannot disappear
through `_`, shadowing or a future rest pattern. Rest patterns are not part of
this foundation. `qfor` carry and `qmatch` partition rules remain their own
0.3.0 work; sharing a parser node does not admit richer #197 patterns.

Recommend expression-oriented quantum blocks with a mandatory final expression
and one structured result interface. Reject `return`, `?`, `panic!`, runtime
assertion/unreachable forms, unwinding and destructor-driven owner cleanup in
the quantum core. Do not inherit host error-exit semantics by syntax similarity.
A final explicit `()` is required for an ordinary Unit result. Compilation and
checking failures are external failures; they are not runtime exits licensed to
abandon owners in an otherwise accepted program.

## Static elaboration and generic responsibilities

Static parameters are explicit and positional in declaration order. A later
parameter kind may depend only on earlier parameters: for example `n : Nat`
before `U : Op<Bits<n>>`, or `A : Basis` before `U : Op<A>`. Duplicate names,
forward dependencies and static/runtime category ambiguity reject. Runtime
values never flow into static sizes, provider selection, conditions or loop
bounds. Omitted generic argument inference is not enabled by this packet.

An abstract `A : Basis` is opaque. A generic body may pass `Q<A>`, return it,
use an explicit operation provider on it, or compose permitted structure; it
cannot inspect `A` as a tuple, assume a width, synthesize a Hadamard, prepare a
state of `A`, or obtain a controlled/inverse implementation without the required
operations and constraints. Type reflection, arbitrary `bits(A)` computation,
higher-kinded parameters and dependent type pattern matching are not introduced.

The generic definition is checked even when unused. The shared checker covers
kind correctness, category/name resolution, ownership, declared effect bounds,
capability requirements and both arms of static syntax. Concrete specialization
then checks actual natural substitutions, exact type trees, provider identities,
side conditions and aggregate capacities. Passing generic checks is not native
acceptance; passing some instances is not a theorem for the whole family.

Retain the current bounded natural fragment initially: checked natural arithmetic,
guarded subtraction, multiplication by a known constant, explicit comparisons
and incomplete exact linear implication. Symbolic multiplication of two unknown
sizes rejects. Natural overflow, exhausted implication work, excessive depth
or allocation estimates reject before expansion. Decreasing self-recursion
must have its declared natural decrease; mutual recursion and unproved
termination reject. A zero-iteration fold or statically unreachable arm still
undergoes the prescribed name, type, owner and capability checks; it is not a
way to hide an invalid declaration.

The subsequent #63 constant/static surface must use this same evaluator and
normalized values. Its 0.3.0 acceptance includes a computed static size and
exact QFT phase-table generation, with deterministic bounded helper evaluation.
Do not treat that work as #197's deferred general meta-language. Static helpers
have no I/O, clock, randomness, runtime/quantum dependency, raw IR injection or
authority to construct trusted evidence; exact positions admit no hidden
floating-point approximation.

Use one specialization identity containing the qualified definition, retained
source/dependency context, ordered static naturals, full instantiated type trees,
provider identities, required capabilities and semantic target bindings.
Never key only by width, source spelling, nominal provider name or a digest with
unchecked collision/equality assumptions. Shared code/evidence reuse must
preserve all those dependencies and charge its actual bounded construction.

One desired generic body is:

```qli
unitary fn apply_once[static A: Basis, static U: Op<A>](q: Q<A>) -> Q<A>
requires Apply(U) {
    U(q)
}
```

Acceptance must include explicit instantiations at `Bit`, `Bits<1>`, and a nested
product, with distinct matching providers. Substituting a same-width provider
of the wrong tree must fail. A second body using `inverse(U)` without `Adjoint(U)`
must fail at definition checking, before any favorable specialization is tried.

The one-finite-universe migration must not duplicate a predicate solely to serve
classical and basis uses. #22 requires an explicit bounded reuse demonstration;
renaming `CBit` does not satisfy that criterion. The staging packet must state
the permitted explicit uses of that same body and check coherent lifting's
totality/injectivity/meaning obligations. General automatic cross-stage reuse,
omitted stage markers and implicit lifting remain #197 work. If that explicit
demonstration needs a rule beyond currently admitted uses, decide it before
claiming #22 complete; do not infer it from the shared AST.

## Effects, owners and failure behavior

Ownership and effects are checked separately. The current implementation has
`Unitary`, `Iso`, `Observe` with composition by the corresponding effect join;
the common representation must retain the declared annotation and computed body
effect rather than deriving one from the presence of `Q`. An annotation cannot
downgrade a body. Changes to the effect classes themselves belong to the effect
decision packet and must update both lowering profiles together.

| Construct | Foundation rule |
| --- | --- |
| `let`, calls, tuples, lexical blocks | Ordinary syntax; `Q` leaves move exactly once. Evaluate ordinary call arguments in source order and retain pending-argument owners in the caller frame. |
| Ordinary `if` | Requires an ordinary `Bit`. Both arms have matching result trees and complete compatible ownership frames. No implicit measurement of the condition. |
| `if static` | Requires a static predicate; validates both arms under the specified constraints before concrete branch selection. |
| `qif` | Explicit coherent semantics, with the existing required branch/capability/effect obligations. It cannot be replaced with classical branching. |
| `qfor` / `qmatch` | Explicit quantum constructs in the 0.3.0 feature plan; their iteration/partition obligations are not inferred from ordinary `for` / `match`. |
| Preparation/observation | Explicit operations only; `measure_z : Q<Bit> → Bit` has Observe semantics. Renaming the result does not create a coercion. |
| Scope exit | Every local linear owner is returned or explicitly consumed by an admitted operation. Lexical identities prevent shadowing from reviving an old owner. |
| Zero-width owners | Same move/use/return rules as other owners; zero physical width grants no discard, copy or phase-erasure rule. |

Two local proof components support the access work in
[#303](https://github.com/MGYamada/Qleisli/issues/303). The protected-phase
theorem exchanges adjacent literal phases in their original physical action.
`Qleisli.SharedControlCommutation` additionally proves exact matrix equality
for common control sectors acting on disjoint ordered target factors. Its
single-control bridge concerns the actual hierarchy tensor, control and
sequence definitions, including unchanged surrounding operations and arbitrary
external-reference amplitudes. Zero-width factors retain their scalar phases.
These results do not yet derive a source footprint from `ctrl`/`&mut`, prove
arbitrary owner/axis routing, or authorize source reordering. Width premises
do not discharge `Q<Unit>` ownership, and neither helper proof is an additional
constitutional guarantee. The bounded examples and proof records are retained
in `tests/fixtures/constitution_v030/shared-control-commutation/`.

Diagnostics must distinguish syntax, unresolved/ambiguous name, kind or stage,
type/tree/size mismatch, missing capability, ownership, effect, unsupported
lowering profile, capacity limit and native rejection. Show the original UTF-8
byte span, module and relevant binder/instantiation chain. Report the smallest
tree difference, including `Bit` versus `Bits<1>`. Failure must not leave a
partially accepted artifact, sampled output or usable handle. Diagnostic Rust
computation after native rejection cannot reverse that rejection.

## One frontend, two explicit lowerings

The proposed pipeline is:

```text
retained source + schema-2 qrate/source-tree configuration
  → one lexer/parser and source AST
  → one module graph, visibility and category resolution
  → one generic kind/type/ownership/effect judgment
  → one bounded static specialization and typed source program
  → explicit backend-profile selection
      → finite raw/QIRF proposal → ordinary native acceptance
      → hierarchy proposal → dedicated native checks
```

The typed source program retains exact source type trees, owner identities and
ordered interfaces, static substitutions, structured branches/carries, declared
and computed effects, callable/capability identities and source spans. The
lowerers may choose different representations but may not reinterpret a type,
re-resolve a name, infer an operation, or accept a source rejected by the common
checker. Shared primitive signatures replace the current separate finite and
sized catalogs; each backend has a separate, explicit supported-lowering table.

A backend choice is a supported-profile decision, not overload resolution and
not a response to a failed verification. No fallback changes quantum meaning.
Where both backends support a source, a bounded experiment compares them against
the same independently stated meaning and interfaces. Success of both checkers
alone is not source preservation.

If a downstream format represents only widths where the source distinguishes
trees or `Bit` / `Bits<1>`, keep an explicit source-to-artifact interface mapping
with its stated validation limits. Never promote width equality into evidence
identity. A claim that the native checker proves the full source interface
requires the corresponding independently checked binding; otherwise state the
gap or reject that claimed profile. The common frontend itself remains
untrusted and cannot mint a native accepted handle.

Delete the second lexer/AST/resolver/static checker after its mapped behavior is
covered by common tests. Temporary internal adapters may assist the migration,
but no new feature receives two source implementations, no public fallback
parses the old dialect, and no backend retains a private source grammar.

## Migration and review gates

| Previous form or behavior | Candidate 0.3.0 mapping |
| --- | --- |
| `CBit`, `CBits<n>` | `Bit`, `Bits<n>`; migrate readout signatures, ordinary operators, diagnostics, examples and source-facing APIs. Do not introduce `C<T>`. |
| Finite `Bit` only in basis positions | The same finite type is ordinary or used under `Q`; admissible evaluation depends on stage/category rules. |
| Sized one-function module and explicit module map | Common module declarations/resolution; the explicit-map API supplies the same source graph rather than selecting a grammar. |
| Sized `()` result-type spelling | Canonical ordinary `Unit`; the value remains `()`. Empty quantum registers remain explicitly `Q<Bits<0>>`. |
| `adjoint(U,q)`, `repeat_static(n,U,q)`, sized `repeat_op(n,U)` | Candidate constructed static applications `inverse(U)(q)`, `power(U,n)(q)`, or a static `power(U,n)` provider, subject to capability, counted-power and exact-interface checks. |
| Sized `for static ... carry` | `qfor static ... carry` when carrying quantum owners, under its separately adopted 0.3.0 rule. Ordinary static loops do not acquire hidden quantum threading. |
| Separate primitive signature catalogs | One source signature and identity per primitive; backend support is separate from typing. |
| Old parser acceptance through a hidden compatibility branch | A located migration diagnostic; historical source executes only with the fixed 0.2.9 oracle/toolchain. |

Preserve original authoring attempts, counterexamples, notices and the published
0.2.9 validation artifacts. Append migrated sources and mappings; do not rewrite
historical failures into successes. All current fixtures that are intended to
remain executable need explicit migration or a justified negative-test role.
Changes to source-facing Rust APIs and transport schemas require their own
reviewed compatibility mapping; internal quantum/classical ports may remain
distinct without restoring a second source type universe.

Implementation gates, in dependency order:

1. Resolve the maintainer choices below and record the concrete grammar/mapping
   in the relevant Issues. Preserve desired first sources before checking them.
2. Introduce common syntax, type identity and resolved names with no native
   authority; port both existing profiles' syntax/name/pattern counterexamples.
3. Port generic constraints, ownership/effects and bounded specialization into
   one checker. A backend cannot duplicate or override those rules.
4. Feed both lowerers from that checked source representation; preserve original
   bytes, explicit interface mappings and request scope. Remove the duplicated
   source paths after the replacement checks pass.
5. Implement the selected foundation surface changes atomically with source,
   public API, diagnostic and fixture migration. Add later 0.3.0 features only
   through these common nodes and judgments.
6. Run the bounded acceptance/counterexample packet, relevant native rejection
   tests and changed-proof builds/audits. Publish only the claims actually
   established; native acceptance does not finish QS source preservation.

Minimum counterexamples and positive experiments are:

| Case | Required observation |
| --- | --- |
| One generic body at two structurally different bases | Both matching explicit instances succeed within their selected profile; same-width provider substitution rejects. |
| `Bit` / `Bits<1>`, `Unit` / `Bits<0>`, nested tuple variants | Type, binding and specialization identities remain distinct; a missing explicit conversion rejects. |
| `Q<Unit>` move, duplicate, drop, shadow and controlled scalar | Valid moves survive; every invalid owner action rejects; controlled `[-1]` retains its observable relative phase. |
| Tuple parameter pattern versus argument list | `f((a,b))` does not become `f(a,b)`; shape mismatches and duplicate binders are located. |
| Ordinary condition receives `Q<Bit>` | Reject without measurement; an explicit measurement changes the effect and consumes the owner. |
| Static parameter receives runtime data or the wrong callable category | Reject before specialization; no parser retry, overload preference or inference of physics. |
| Missing inverse/control access, including in unused or zero-iteration syntax | Reject under the common generic judgment. A favorable concrete provider cannot repair an invalid generic contract. |
| Static subtraction, nonlinear multiplication, decreasing recursion and work exhaustion | Only the admitted guarded/terminating cases proceed; overflow and exhausted work reject before expansion. |
| Both branches with returned owners and a live caller/reference frame | Preserve the complete ordered interface and classical phi scope; mismatched consumption rejects. |
| Hidden return/error/unwind or wildcard over a linear field | Reject without implicit cleanup, including zero-width fields. |
| Same resolved source sent to finite and hierarchy lowerers | Same frontend judgments and located failures; supported small cases agree with an independent exact/reference oracle, with lowering limitations reported separately. |
| Missing, mismatched or rejecting native checker | No accepted handle or host fallback on any newly routed public entry. |

Use small widths and bounded reference states only; do not newly generate or
check maximum-size cases. Follow the repository authoring-session procedure for
untouched first source, actual command/diagnostic records and labelled curated
counterexamples. The observations below are existing bounded checks; they do
not substitute for the unimplemented acceptance packet.

## Preserved authoring experiment

The informed session at
`tests/fixtures/authoring_sessions/type-foundation-v030/session.json` in the
[repository](https://github.com/MGYamada/Qleisli) preserves complete first sources,
source hashes, command arguments and actual JSON diagnostics. It is an informed
design study, not a blind model benchmark or adoption of its generic syntax.
The recorded tool version is `0.3.0-alpha`; all four observations used `qleisli
check --format=json` with an explicit local native checker path.

| Preserved source / observation | Recorded result | Consequence |
| --- | --- | --- |
| `attempt-01/ordinary-bit`, `ordinary-bit-initial.json` | Exit 1, `type_mismatch`: `Bit is a basis type; ordinary functions use CBit or Q<basis type>` | The adopted unmarked ordinary finite type boundary is not implemented. |
| `attempt-01/generic`, `generic-initial.json` | Exit 1, `parse`: ``parse error: expected `Op`, found identifier`` at the proposed `Basis` parameter | The common basis-polymorphic grammar is a desired source, not an existing feature. The two uses never reached checking. |
| `attempt-01/unit`, `unit-initial.json` | Exit 1, `invalid_entry`: `main must be observe fn main() with a classical result` | The initial entry convention was invalid; this observation says nothing against `Q<Unit>`. |
| `attempt-02/unit`, `unit-entry-repair.json` | Only the entry effect changes from `unitary` to `observe`; exit 0, `verified: true` | The retained `keep_empty : Q<Unit> → Q<Unit>` case checks with the current frontend/native path after that repair. |

The successful Unit check does not exercise controlled scalar phase, prove
source preservation, establish generic typing, or discharge the counterexamples
listed above. Original failures remain preserved; the repair is a new attempt.

## Constitutional impact and claims

| Obligation | Impact and required evidence |
| --- | --- |
| QS | Shared judgments must preserve linear owners, exact trees, ordered axes, phase, classical scope, effects and independently requested meanings. New lowering correspondence cannot be inferred from validity of its output. Existing scoped QLV1 guarantees retain their exact predicate/artifact boundary; source-level strengthening requires its own evidence and admission. |
| PR | A common source frontend grants no target realization or exported-artifact correctness. Lowering must expose the chosen representation and preserve the contract needed by subsequent realization checks; target synthesis and its workspace remain separate. |
| RS | Bound parser/type/specialization work and storage before construction, including empty owners and zero-iteration syntax. These engineering limits are not the quantitative program/target Resource Safety theorem. Record changes to counted program resources and preservation obligations rather than treating code sharing as a proof. |

This packet implements no new constitutional interpretation. Ordinary design
choices within the adopted QS/PR/RS obligations are maintainer decisions. A
claim of formal discharge or a genuine change to the interpreted boundary needs
the established human adequacy/admission process; implementation approval or
the shared checker cannot supply it.

## Selected type choices and remaining grammar decisions

1. **One Bit literal spelling: selected target.** The current finite grammar uses
   `0/1` for basis values and `true/false` for ordinary `CBit`; retaining that split
   would keep a second value-language distinction after #22. The target Reference
   selects `0/1` for ordinary and basis `Bit`, reserves numerals in static-Nat
   positions for naturals, and requires explicit migration of `false/true`.
   Other Bit numerals reject; no literal creates a quantum owner. The source
   implementation and conformance tests remain required.
2. **Explicit exits.** #196 illustrates ordinary `return` over `Q<T>`, while #37
   proposes structured quantum bodies without early return or hidden exits.
   The surface classification does not itself authorize the example. Recommend
   the mandatory-tail-expression rule above and state that `return` is unavailable
   in quantum core source. A host language, if later admitted, has its own exits.
3. **Operator interfaces and refinement.** #83 explicitly leaves endomorphisms
   versus general arrows undecided. Current finite syntax permits `Op<A,M>`
   with a meaning in the second slot; #89 illustrates `Op<A,B>` with a codomain
   there. Recommend a shared domain/codomain representation, `Op<A,B>` as the
   general type and `Op<A>` as its endomorphic abbreviation. Give refinement
   an explicitly labelled slot, for example `Op<A,B, meaning M>` and the
   endomorphic `Op<A, meaning M>`, rather than guessing the category of a second
   identifier. Migrate existing finite refinements explicitly. Settle this
   ordinary design choice together with #45/#46's typing, access and meaning
   rules before implementing the common static type representation or claiming
   #33/#44/#83/#89 complete. Nothing in #27 adopts the ambiguous comma syntax,
   and nothing here grants capabilities to every mathematical arrow.
4. **Binder positions and empty blocks.** Existing finite parameters allow
   destructuring only for basis functions; sized parameters are names and its
   parser accepts an implicit empty Unit result. Recommend one explicit pattern
   judgment for all parameter binders and mandatory `()` for Unit results, as
   above. This changes admitted source and needs the stated migration tests;
   it is not merely moving implementation files.

The target Reference's strict 0.3.0 treatment of `Bits<0>`, tuple structure and
owner packaging preserves current distinctions while satisfying the need for an
explicit policy. The ordinary design decision belongs in #43/#84/#100; the
implementation and validation criteria remain open. This packet does not present
the choice as a human ruling. Any future implicit convenience remains
subject to the separately reviewed 0.4.0 policy in #197.
Likewise, #196's illustrative `CBit` occurrence is superseded by adopted #22/#27.
Neither stale example warrants reopening the unmarked ordinary type boundary.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
