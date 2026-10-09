# Surface-to-core elaboration

This chapter specifies permitted convenience elaborations in `0.3.0-alpha`,
edition 2026, under the [authority hierarchy](authority.md). It consolidates
adopted source contracts tracked by
[#34](https://github.com/MGYamada/Qleisli/issues/34). It introduces no syntax,
primitive, implicit conversion, evidence authority or supported emitter.

An elaboration may insert only the uniquely determined operations described
below. Preserve evaluation order, complete type trees, logical owners, exact
phase and original source attribution. It cannot infer arbitrary isomorphisms,
permutations, cleanup, operator equality or unavailable capabilities.

## Source and acceptance boundary

The complete original AST first receives the
[common source judgment](source-text.md). All declarations, both arms and
zero-iteration bodies are checked. Static bindings and immutable facts are
inputs to concrete elaboration, not native accepted handles.

Concrete targets remain distinct: finite Raw/QIRF proposals, selected-source
Raw proposals, and selected hierarchy/finite-leaf proposals. **Target** below
identifies an existing representation; it does not claim that one canonical
typed Core or converged emitter has replaced them. A supported source form can
have an unsupported projection or target. Failure cannot select a weaker checker.

Every resulting artifact, dependency and independent request must pass its
actual [production gate](production-boundary.md). Handwritten and generated IR
have the same independent acceptance requirements. Rust normalization, source
checking, source-step comparisons and proposal generation confer no acceptance.
Valid output alone does not prove source preservation.

The scoped QLV1 ownership and classical-scope guarantees retain their original
decoded-root premises. Broader source/semantic QS, forward PR, quantitative RS
and EXACT obligations remain pending. Remaining obligations below are
requirements, not newly discharged guarantees or new ledger entries.

## Whitelist

Literal values, sealed operations and explicit structural maps retain their
separate [type](type-model.md) and [primitive](primitive-boundary.md) contracts.
An implementation detail or Issue candidate does not enlarge this list.

| Surface construction | Permitted expansion |
| --- | --- |
| Runtime products, patterns and ordinary calls | Exact value-tree binding and checked call-body expansion |
| Whole-owner `excl` calls | One checked consuming call and retention of returned values on the same lexical binders |
| Ordinary Boolean expressions and `classical fn` calls | Eager ordinary-value operations |
| Runtime classical `if` | Classical branches with complete result/frame joins |
| Static naturals, aliases and bounded helpers | Exact checked substitution; no runtime instruction |
| Bracket specialization and `if static` | Closed checked instances and selected arm |
| `for static` and `qfor static` | Explicit carry threading over a closed finite range |
| Static operation descriptions and application | Provider-bound operations and checked transformation proposals |
| `controlled(U)(c,q)` and two-arm `qif` | Exact controlled action retaining inactive identity action |
| `basis q as p { e }` | The specified coefficient-`+1` coherent lift |
| Existing `with_computed` forms | Checked compute/use/uncompute construction |

Each entry supplies the eight contract fields. Linked Reference rules specify
the detailed grammar, capabilities and profile limits.

### Runtime products, patterns and calls

| Field | Contract |
| --- | --- |
| Source | Ordered runtime products, `let`/parameter patterns, resolved ordinary function calls |
| Target | Exact value-tree bindings and checked callee body; Raw operations or supported selected source steps |
| Evaluation order | Evaluate each RHS/argument completely once, left to right, before binding. An argument list is not one automatically packed tuple. |
| Owners | Move each quantum leaf once. Destructuring `(Q<A>,Q<B>)` never splits `Q<(A,B)>`. Preserve pending arguments and suspended caller owners; ordinary leaves may be copied or ignored. |
| Exact phase | Binding, grouping and call expansion insert no gate or phase; preserve callee action and ordered interface. |
| Source spans | Keep original parameter/RHS/call spans. Argument failures identify the actual argument or call; emitted callee operations retain original body origins. |
| Refusal | Exact arity/tree mismatch, duplicate names within one pattern/parameter list, live quantum wildcard/implicit drop/reuse, unresolved callee, invalid body or unsupported projection rejects. Ordinary runtime shadowing retains its existing lexical rules. |
| Remaining obligations | Independently check emitted ownership/scope/effect rules and dependencies. Call expansion still needs original-body correspondence; fresh IR validity alone does not supply it. |

See [exact trees](type-model.md#structural-equality-coherence-and-physical-maps)
and [functional abstraction](functional-boundary.md).

### Whole-owner exclusive calls

| Field | Contract |
| --- | --- |
| Source | `U(excl q)` or a call whose arguments all mark distinct whole lexical `Q<A>` owners; finite project compilation and native-checked selected Raw lowering admit retained concrete `ctrl` calls after fresh native sector checking |
| Target | The existing consuming call, followed by replacement of each argument binder's value by its exact ordered returned owner; the access expression returns ordinary Unit |
| Evaluation order | Resolve original source occurrences; supply owners once in argument order and execute the callee once. No copied AST occurrence acquires a second lexical identity. |
| Owners | Keep the same lexical owner identities with returned values. Require actual inferred Unitary effect and the exact original owner interface. Subsequent consuming calls still make their binders spent; shadows cannot restore them. |
| Exact phase | Preserve the complete callee action, including entanglement, ordered axes and zero-width phase. Insert no inverse or cleanup. |
| Source spans | Retain original callee and argument identifiers, byte spans and callee-body origins. Contextual marker spans do not replace owner-identifier spans. |
| Refusal | Overlap, spent/hidden/nonquantum argument, changed owner partition/tree, nonunitary body, indexed/mixed/escaping access, failed native control-sector check or unavailable concrete projection rejects. Checker-free Raw and hierarchical `ctrl` remain unsupported. Native-checked Raw also checks unused closed functions leading to control obligations; it invents no static bindings and refuses original obligations without a concrete interval in each retained specialization. |
| Remaining obligations | Check emitted artifacts and requests independently. The lookup-level scope-update model has finite-map, type-embedding and update-provenance premises; it is not a source-preservation proof or quantitative resource certificate. General footprints, lifetimes and access declarations remain pending. |

See [whole-owner exclusive calls](rust-boundary.md#whole-owner-exclusive-calls).

### Ordinary expressions and classical functions

| Field | Contract |
| --- | --- |
| Source | Ordinary Unit/Bit/product expressions, eager `not`/`and`/`xor`, supported `classical fn` calls |
| Target | Ordinary evaluation and Raw classical operations, including selected Raw register transport where supported; no runtime truth-table substitution |
| Evaluation order | Evaluate operands and complete actuals once in source order. `and` is eager, including its right operand. |
| Owners | Ordinary results have no quantum owner. Input expressions retain effects and quantum consumption; ignoring a result cannot omit its measurement. |
| Exact phase | Ordinary Boolean evaluation inserts no quantum action; input expressions retain their complete action/instrument. |
| Source spans | Keep original operand, call, parameter and definition byte spans. |
| Refusal | Wrong exact types/arity, forbidden capture, invalid classical body/dependency or unavailable transport rejects. A live `Q<A>` is not an ordinary A argument. |
| Remaining obligations | Check lexical use, complete phi inputs and value operations; preserve original computation and surrounding instrument. Coherent use additionally needs the separate lift obligation. |

See [classical declarations](source-text.md#total-classical-declarations)
and [ordinary Bits transport](type-model.md).

### Runtime classical branches

| Field | Contract |
| --- | --- |
| Source | `if condition { ... } else { ... }` with an ordinary Bit condition |
| Target | Raw `ClassicalBranch`, both operation lists and simultaneous classical/quantum phis, or supported selected branch representation |
| Evaluation order | Evaluate condition once. Runtime executes its selected arm; source checking visits both arms. |
| Owners | Both arms agree on exact returned trees and outer consumption. Merge returned leaves and the complete surviving caller/pending-argument frame. IDs remain globally fresh across arms; phi renaming prepares no state and loses no reference correlation. |
| Exact phase | Preserve each arm's action and unnormalized outcome weight; insert no coherent superposition or branch normalization. |
| Source spans | Arm operations retain original spans and nested branch-index paths; inserted joins use the branch span. |
| Refusal | Quantum condition, different types/owner frames, lost branch-local owners, invalid phis/body or unsupported target rejects. |
| Remaining obligations | Native-check both arms, scope, ownership and simultaneous phis. Preserve the complete source instrument with external references and caller-frame correlations. |

Runtime selection is distinct from coherent control and static selection.

### Static natural computation

| Field | Contract |
| --- | --- |
| Source | Supported natural expressions, `static let`, provisional bounded acyclic Nat helpers |
| Target | Exact affine templates/substitution and closed checked naturals; checked unused aliases insert no runtime instruction |
| Evaluation order | Resolve ordered static binders and helper actuals in their static context. Substitute simultaneously; callee names cannot rewrite caller binders. |
| Owners | None: the static environment contains no live quantum owner or runtime input. |
| Exact phase | Normalization inserts no phase. A result used by an explicit phase operation is its exact specified parameter. |
| Source spans | Keep original arithmetic, actual, premise and binder spans, never generated replacement text. |
| Refusal | Runtime-dependent values, forward kind dependencies, duplicate/shadowing bindings, nonlinear arithmetic, unproved subtraction/premises, cycles, overflow or work exhaustion rejects. Acyclic forward helper references retain normal declaration resolution. |
| Remaining obligations | Check closed values and uses under exact constraints. Compiler work counters do not certify program resources. |

See [static arithmetic and helpers](static-language.md).

### Specialization and static selection

| Field | Contract |
| --- | --- |
| Source | Ordered `const` parameters, complete bracket actuals, `if static comparison` |
| Target | Supported closed instance and selected static arm after complete original-source checking |
| Evaluation order | Resolve explicit static bindings/provider identities before runtime application. Static selection evaluates no runtime condition. |
| Owners | Preserve the runtime instance's exact interface and owners; a dead source arm remains checked. |
| Exact phase | Substitute parameters without quotienting phase or changing axis order; retain the selected action. |
| Source spans | Keep definition, actual, comparison and arm spans. |
| Refusal | Incomplete/wrong bindings, unproved constraints/access, invalid dead arms, non-decreasing dependencies or unsupported instance rejects. No width-based inference or fallback. |
| Remaining obligations | Native-check actual closed artifact and provider evidence. General specialization preservation and family resource bounds remain separate. |

The [static rules](static-language.md) specify termination and capacities;
helper spellings remain provisional where those rules say so.

### Finite folds

| Field | Contract |
| --- | --- |
| Source | Ordinary `for static` or quantum-owner `qfor static`, with explicit range, carry pattern, initializer and `yield` |
| Target | Closed finite iteration of existing fold/source steps, then supported Raw/hierarchy proposal |
| Evaluation order | Evaluate initializer once; thread carry in increasing index order over `[start,end)`. Zero iterations return that evaluated initial value. |
| Owners | Preserve exact carry tree. `qfor` carries a quantum owner, including empty-width owners. Non-carried owners cannot be hidden captures; insert no exit discard or reassembly. |
| Exact phase | Serial composition retains every iteration's phase; empty iteration sequence is identity on retained carry. |
| Source spans | Keep bound, carry, body and yield spans in every instance. |
| Refusal | Invalid range/runtime bound, wrong fold category, carry-tree mismatch, missing yield, hidden capture or invalid zero-count body rejects. Limits retain their category. |
| Remaining obligations | Check complete composition, owners and dependencies; finite unrolling proves neither a general family theorem nor a quantitative bound. |

See [fold rules](static-language.md#static-branches-folds-and-termination).

### Operation descriptions and application

| Field | Contract |
| --- | --- |
| Source | `adjoint`, `power`, `then_op`, `tensor_op`, `conjugate_op`, `controlled`, `checked_op` in specified static-description/application positions |
| Target | Provider-bound descriptions and existing untrusted circuit, finite-contract or hierarchy transformation proposals; no runtime closure |
| Evaluation order | Check complete description before application; runtime actuals evaluate once in source order, including power zero. Adjoint reverses operation order and conjugates action. |
| Owners | Retain exact basis tree and runtime group. Tensor descriptions use their packed basis; they do not implicitly join separate owners. |
| Exact phase | Adjoint conjugates phase; power repeats complete action; serial/tensor/conjugate retain ordered action. Meaning is a separate obligation, never an access grant. |
| Source spans | Keep original constructor, operand, count, Meaning and input spans through nested descriptions. |
| Refusal | Missing access, wrong basis/interface/Meaning, unsupported provider/transform/count, unresolved obligation or capacity failure rejects, including unused/zero contexts. Constructing `adjoint(U)` itself requires `Adjointable(U)`. |
| Remaining obligations | Independently bind providers, retained bodies, exact transformations and requested Meanings to emitted artifacts; a valid unbound circuit is insufficient. |

See [access derivations](functional-boundary.md),
[repetition](static-language.md#operation-repetition-and-access) and
[checked operations](checked-operations.md).

The same eight fields apply to each constructor below. These are the existing
endomorphic description actions, not a general isometry-adjoint admission.
Runtime-order arrows describe execution; matrix products act right to left.

| Description | Exact expansion/action |
| --- | --- |
| Resolved provider/specialization | Retain the actual closed body, bindings and dependency evidence; no operation-name substitution. |
| `adjoint(U)` | U's justified adjoint action; reverse/conjugate the retained steps on the supported circuit path. |
| `power(U,n)` | n serial copies of U, with identity at zero and all original provider/access obligations retained. |
| `then_op(U,V)` | Execute U then V on the same exact basis; matrix action `V U`. |
| `tensor_op(U,V)` | Apply U to the first basis block, V to the second ordered block; retain one shared outer control when controlled. |
| `controlled(U)` | Retain control, identity on zero and exact U on one, including U's scalar phase. |
| `conjugate_op(C,U)` | Existing ordering `C† → U → C`, matrix action `C U C†`; do not silently substitute `C† U C`. |
| `checked_op(U,M)` | Retain U's implementation and attach the independent exact M obligation; this inserts no runtime gate or capability. |

Description composition does not automatically transport an attached
`Op<A,M>` refinement. The common judgment's existing refinement/obligation
rules and the concrete independent checks remain as specified in
[functional abstraction](functional-boundary.md#admitted-operation-construction).

### Coherent control

| Field | Contract |
| --- | --- |
| Source | `controlled(U)(c,q)` or `qif(c,q) { 0 => F, 1 => G }` with both named arms |
| Target | Finite `Join → ApplyUnitary → Split` over ordered `(Bit,A)`, with the bound controlled circuit/evidence; otherwise the supported hierarchy construction. Controlled U retains inactive identity; qif retains its specified zero/one actions. |
| Evaluation order | Evaluate control then target completely once; do not measure control or use it as a classical condition. |
| Owners | Consume two inputs, temporarily package them for the finite controlled action, then return `(Q<Bit>,Q<A>)` in order, even for zero-width A. Retain complete target tree and reference frame; packaging prepares no state. |
| Exact phase | Control is the first low axis. Inactive identity has coefficient +1; retain active phase, including scalar Unit phase and kickback. |
| Source spans | Keep control/target actuals and provider/arm names; generated control structure retains the expression origin. |
| Refusal | Missing Controllable access, wrong owners/arity, aliases, invalid or omitted/reordered named arms, unsupported interface rejects. Unitarity grants no control access. |
| Remaining obligations | Independently check provider/body identity, exact action, axes and owners. Probabilities or known-input tests do not discharge coherent/reference correspondence. |

Inactive identity belongs to the specified controlled meaning. There is no
admitted omitted-arm `qif` rewrite.

### Coherent basis maps

| Field | Contract |
| --- | --- |
| Source | `basis q as pattern { expression }` |
| Target | Finite `LiftBasis` with complete supported label map; selected CoherentLift projection remains unsupported |
| Evaluation order | Evaluate q once before binding labels; evaluate restricted total expression in separate basis scope. |
| Owners | Consume one `Q<A>`, return one `Q<B>`. Label patterns do not split runtime owners; separate inputs are not implicitly joined. |
| Exact phase | Each transition has coefficient +1, linearly with identity on arbitrary external reference. Retain amplitudes and ordered output labels. |
| Source spans | Keep original input, label pattern and body spans. |
| Refusal | Wrong owner/tree, outer capture, unsupported body/callee, noninjective complete map, reuse or unavailable profile rejects. |
| Remaining obligations | Independently check complete lift, injectivity and effects; source-to-table correspondence is separate from table validity. |

See [coherent basis maps](coherent-basis.md), including Unit and the
difference between label copying and state copying.

### Computed workspace

| Field | Contract |
| --- | --- |
| Source | Existing two-argument `with_computed(source,predicate)` or three-argument logical-contract form |
| Target | Existing Raw `ComputeUseUncompute` or certified retained-body construction and finite evidence, within each supported profile |
| Evaluation order | Evaluate source once; compute specified ancilla, execute checked scoped body, then uncompute. |
| Owners | Predicate takes one ordinary parameter of source's exact tree. Two-argument body returns ancilla; three-argument body returns data and ancilla. Capture/protection rules remain explicit; no standalone Release0 is inserted. |
| Exact phase | Preserve complete use/logical action and require exact all-input clean return; known-input/marginal tests or approximate cleanup are insufficient. |
| Source spans | Keep source, predicate, body, returned owner and logical-contract origins. |
| Refusal | Wrong predicate arity/tree, unsupported body, Observe effect, lost/aliased/protected owners, failed equality/cleanup or capacity exhaustion rejects. Two-argument path retains identity/expanded-Z/T restriction. |
| Remaining obligations | Independently check actual retained compute/use/uncompute and exact logical/cleanup contract with references; syntax and Unitary annotations supply no clean evidence. |

See [scoped bodies](functional-boundary.md#scoped-bodies-finite-elaboration-and-effects)
and [predicate trees](type-model.md#structural-equality-coherence-and-physical-maps).

## Explicit maps and unsupported candidates

`split`/`join`, Unit insertion/removal and existing register primitives remain
explicit [specified maps](primitive-boundary.md), with original ordered
interfaces and coefficient +1. Do not insert them to repair an argument tree.
`Bit`, `Bits<1>`, `Unit`, `Bits<0>`, tuple arity/nesting and packed versus separate
owners remain distinct. Canonical reassociation is not definitional equality
and is not an admitted implicit elaboration.

Ordinary literals do not prepare quantum states. `init0` retains its explicit
Iso primitive contract; `basis` is a coherent map, not arbitrary state-preparation
sugar. No implicit view partition/reassembly, borrow/ctrl insertion, arbitrary
wire permutation or cleanup is admitted here. Add conveniences only after their
complete contract and checking evidence; an Issue's candidate list is insufficient.

## Original locations and failure

Spans remain half-open UTF-8 byte intervals in unnormalized original source.
Emitted operations retain original expression/body origins; finite nested
branches retain operation/arm-index paths. Child/callee origins are not
overwritten by enclosing expressions. An inserted operation without a more
specific origin uses that expression's span.

After finite native rejection, diagnostic mapping selects the longest retained
operation-path prefix, otherwise the original caller/declaration. This is
post-rejection metadata only: it cannot change acceptance, manufacture evidence
or hide failure. Unsupported profiles and work limits keep distinct diagnostics;
exhaustion is not mathematical invalidity. Migration errors name original tokens.

## Migration correspondence

Production rejects retired forms; it does not retry a legacy grammar or apply
an accepting compatibility rewrite. A migration derivative is a separate
source with its own bytes/provenance. Preserve original source, diagnostics and
artifacts, then validate the complete new source. Do not weaken owners, access,
effects or Meaning to make a rewrite succeed.

| Preserved old form | Current explicit form | Preserved contract |
| --- | --- | --- |
| `[static n: Nat, ...]` | `[const n: Nat, ...]` | Ordered explicit kinds/actuals; no inferred specialization |
| `adjoint(U,q)` / earlier `inverse(U)(q)` | `adjoint(U)(q)` | Adjoint action and actual access premise |
| `repeat_op(k,U)` / `repeat_static(k,U,q)` | `power(U,k)` / `power(U,k)(q)` | Count, exact provider/group, once-only input evaluation |
| `inverse_op(U)` / `controlled_op(U)` | `adjoint(U)` / `controlled(U)` | Bound description identity and access |
| `Apply` / `Adjoint` / `Controlled` predicates | `Applicable` / `Adjointable` / `Controllable` | Actual provider access; no annotation grant |
| `do p <- q; pure e` | `basis q as p { e }` | Same CoherentLift, coefficient +1 and injectivity |
| `bind_op(U,M)` | `checked_op(U,M)` | Exact interface/Meaning and original provider evidence |

This table is not a general automatic rewriter. Unimplemented drafts acquire
no historical equivalence claim. [Types](type-model.md) and [stdlib](stdlib.md)
retain their separate migration contracts.

The preserved [operation-application comparison](https://github.com/MGYamada/Qleisli/blob/0a86fe5456bf92553459ffd5ad45d20180b23494/tests/fixtures/frontend_v030/retired-operation-spellings/migration-comparison.json)
checks complete two-qubit old/new source on separately identified binaries.
Both receive fresh source checks; proposed bytes agree, SHA-256
`32adb61c4a2b24c77dd89f83d0761b427d7509b85b0c4a3b4f93b313d50b9bd4`.
Emission is not acceptance; those separate checks remain necessary.
The later [capability-name comparison](https://github.com/MGYamada/Qleisli/blob/0a86fe5456bf92553459ffd5ad45d20180b23494/tests/fixtures/frontend_v030/capability-naming/precommit-validation.json)
retains 34 equal checked artifacts and one measurement-adjoint refusal.
The selector verifies exact predecessors/derivatives without rewriting first
sources or independent oracles.

Source-bearing artifacts can change bytes after a source edit even with equal
operator/interface meaning. Never erase identity to force byte equality.
[Coherent-basis](coherent-basis.md) and [checked-operation](checked-operations.md)
regressions instead retain exact interfaces and independent small complex
action/instrument, phase, axis, provider and reference tests. These bounded
comparisons are migration evidence, not universal source preservation, complete
QS/PR/RS, generic QFT implementation or release approval.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
