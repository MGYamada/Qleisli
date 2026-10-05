# Mandatory checking of the complete original source AST

**Status: candidate ordinary before-code implementation/migration contract for
root review and recording in existing Issue #32.** This file does not adopt a
constitutional interpretation, change a guarantee or report implemented behavior.
It also concerns #317's shared-library checking prerequisite; it completes none
of that Issue's 24 criteria. Edition remains 2026 and release remains
0.3.0-alpha. The candidate and dataflow notes cited below retain their original
non-adopted status.

## Basis and actual starting point

The adopted QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 apply. Their
broader proof/enforcement obligations remain pending. Both ordinary QLV1
decoded-root ownership/classical-scope guarantees retain their exact premises
and exclusions; neither proves this source checker or source preservation.
The constitutional startup guard passed with reviewed base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. This is identity/continuity checking,
not fresh Lean replay, a Guardian act, full CI or release approval.

The preserved [first study](../../authoring_sessions/common-original-ast-v030/results-first.md)
contains 18 complete schema-2/edition-2026 projects and **72 actual checks:
18 success, 54 source/profile refusals, 304 pre-execv forwarding rows**.
All 72 event/raw-stream hashes were independently read and matched; no recorded
commands were executed during this contract review. The actual checkout marker
was `7e04f20f0c908fd56720a50655bc56c072c80ceb`, not compiled-HEAD attestation.
Forwarding rows are not independently attested native starts/exits. Preserve
FIRST41, predictions, first diagnostics and the existing finite/selected
differences unchanged. New outputs must be recorded separately.

Reviewed input identities:

| Original | SHA-256 |
| --- | --- |
| `../common-frontend-next-unit-01/original-ast-checking-candidate-01.md` | `096bff87770b84d867973b522238dfaa20f11a3fa36e038b39856128530792c9` |
| `../common-frontend-next-unit-01/original-ast-checking-dataflow-01.md` | `e7f9c9b09165e4c59af1074d3c5270332f2893789b4da33947fc9b4bda9d0847` |
| First study `first-files.json` | `753edf0e0fe01b6b3a2f597250b237cd8a0574e07ac0f67da3d483e77d1ea2db` |
| First study `before/summary.json` | `0dcda5d65b9616146adf376a9e0812cde461dc6fe136beabc62b4502d988850f` |
| First study `results-first.md` | `b05f29a4338edc04fd8ca1be7213551eb3c19811f7f71b3ebfead23a54838756` |

## One mandatory judgment and real consuming facts

Both production source paths must use this flow:

```text
complete original SourceCollection -> fresh Resolution + original lexical Index
  -> all-declaration interfaces -> all original bodies
  -> checked dependency/decrease graph + principal effects + located obligations
  -> finite eligibility OR selected concrete Raw/hierarchy eligibility
  -> actual evidence/proposal generation -> unchanged fresh native checking
```

Introduce one private common judgment over original `Decl`, `Type`, `Natural`,
`BasisExpr`, `StaticOp`, `Block`, `Expr` and `Pattern`. It must inspect every
declaration and every body, including private/unused definitions, both static
and runtime arms, zero-count fold bodies and all bundled sources. A reachability
slice, filtered `Function` AST, effect annotation, algorithm name, placeholder
IR verification or retry through another source checker cannot supply success.

Return immutable, actually consumed facts: `DefId`/module/original `ast_index`,
complete ordered parameter categories and BinderKeys, normalized symbolic
runtime/result types, checked premises, owned checked operation bases/access,
resolved Meaning identities, lexical-use/type/owner facts, dependencies,
principal/asserted effects and explicit located concrete evidence obligations.
Borrow the original syntax for checking; do not manufacture another body AST.
Use the existing common type tree, Formals, pattern, Boolean and BodyEffects
rules. Collection-local IDs are not durable artifact/evidence identities.
Lexical keys remain distinct from fresh dynamic owners at repeated calls/folds.

Finite signature/formal lookup must consume these interfaces and convert them
to the existing closed finite types only at eligibility. Refined Meaning
formals retain the resolved identity; their later finite binding must consume
the real checked matrix with matching exact basis and work/depth metadata.
No dummy matrix, abstract emitted IR or bare pass flag substitutes for a fact.
Remove the finite `check_generic` placeholder-lowering source oracle once all
its actual source rules have moved. Keep concrete Lowerer ownership checks,
exact Basis/Meaning tables, retained contracts, actual IR validation and native
checking as independent concrete obligations.

Selected parsing must retain the complete originals without the current
semantic `parser::project` refusal before common checking. Migrate generic
declaration/body/effect policy, instantiation and elaboration lookup to original
`Decl` references and shared interfaces, using `DefId`/`ast_index`, not spelling
or span recovery. Concrete substitutions, fresh dynamic owners, source-step
checks and evidence remain rechecked. The existing projection may temporarily
exist only as a post-judgment lowering representation: it must keep association
with every original declaration and report located eligibility failure when
that body is requested. Dropping unsupported siblings, building a second
canonical source policy or treating projection as source approval is forbidden.
Retiring the projection remains outstanding #32/#317 work.

For the mutable public `Project` compatibility view, reconstruct resolution and
checking facts from its current supplied originals on every operation; never
reuse a prior collection/pass beside subsequently mutable fields. Do not claim
AST/text or source/artifact correspondence merely from these local facts.

## Collection, resolution and ordinary migration choices

Use the fixed `BundledRegistry` as the sole bundled provenance constructor.
Both loaders retain and check its four unchanged ordinary sources:
`std::arithmetic`, `std::basis`, `std::routines`, `std::transforms`, and validate
its schema-2 edition-2026 manifest. Charge bundle bytes and module slots before
copying/parsing/inserting. The selected 64-module ceiling counts the four
bundles, so at most 60 supplied modules remain; reject an empty supplied map.
Preserve 64 KiB/module and 1 MiB aggregate selected byte limits including these
sources. Finite bounded/explicit legacy loading policies remain explicit;
adding this checker does not make the legacy byte loader bounded.
No caller replacement, ambient std path or origin-based exemption is permitted.
Local `std`/`std::` names remain reserved. Existing module/path grammar and
source-root/edition identity checks remain in force.

Register all declaration interfaces before resolving body dependencies. Visit
modules deterministically and declarations in their original source order;
canonical DefId sorting does not reorder first declaration diagnostics. Resolve
imports in source order. Reject a duplicate import or any imported-name/local
declaration collision, including every self-import of a public or private
declaration. Same-module direct private sibling lookup remains valid; a
cross-module import and a host-selected entry require public visibility.
Unknown names in compiler-owned primitive modules never fall back to ordinary
source. Missing member/private/collision/unknown-primitive diagnostics point
to the final path token; missing module points to the whole `use` span.

**Permit unused import-only cycles**, since imports have no runtime action and
all interfaces are registered first. Reject genuine dependency mutual cycles
over runtime calls, static providers, Basis and Meaning bodies, including
dependencies in private/dead/zero bodies. Only an ordinary runtime self-call
to the identical DefId with the existing successfully proved natural decrease
is permitted. Basis/Meaning cycles and recursive provider references still
reject; name equality, an effect fixed point or an unsuccessful solver cannot
authorize them. Retain a located closing-edge diagnostic and bounded iterative
graph work.

These are explicit ordinary migrations from documented profile differences:
finite currently rejects import-only cycles; selected currently permits a
same-DefId self-import, including private visibility, and highlights several
whole-use spans. Update those regressions and Reference rules deliberately.
Do not rewrite historical results or hide the differences behind profile flags.

Runtime parameter/let/fold-carry bindings must not shadow an active static
Nat, Basis, Op or fold-index binder. Runtime-value lookup must not fall back to
a global declaration after a move or wrong-category error. Static formals may
shadow global declarations. Rebinding a consumed owner after fully evaluating
its RHS remains legal; hiding a live owner, including a zero-axis owner or one
nested inside a product, rejects. This adopts the existing selected static-name
restriction for common source checking and changes the observed finite Op-shadow
case; it does not prohibit ordinary consumed-owner rebinding.

## Types, all bodies, dependencies and effects

Preserve the staged declaration sequence: complete static-name/category claim;
Nat premise normalization and feasibility; ordered kind checking with preceding
Nat/Basis prefixes; individual same-declaration Op access grants; runtime
parameters in order, each complete pattern-name scan then its type check;
return type; whole body. Preindexing does not make a forward kind legal.
For each source type, scan all Basis-parameter occurrences before normalizing
Naturals, then retain recursive left-to-right Natural error/overflow/nonlinearity
order. Preserve exact tuple tree, parameter argument count, stage distinction
and symbolic equality/nonnegativity obligations; equal width never coerces a
type, `Bit` into `Bits<1>`, or Unit into `Bits<0>`.

Every existing expression/static constructor needs a real rule. Check ordinary
calls/Boolean operations/tuples/lets, classical `if`, static `if`, carry folds,
coherent Basis lift, both computed forms, `qif`, adjoint/control/repetition,
contract application and all current static operator constructors. A known
unsupported *concrete realization* may follow successful complete source
checking; an unimplemented source rule cannot be silently omitted or passed.

Evaluate runtime arguments/RHS completely and once, left to right, before
binding. Quantum pattern wildcards and unused expression statements cannot
discard an owner. Preserve complete live frames, globally fresh dynamic
identities, branch-local visibility and exact owner/result reconciliation in
both runtime/static arms. Check zero folds under their index/carry context,
without permitting a captured outer quantum owner to disappear or be reused;
only the explicit carry transports such owners across iterations. Separate
owners can be entangled; `measure_z` consumes its logical owner. `Q<Unit>` and
`Q<Bits<0>>` retain ownership and phase with zero physical axes.

Ordinary Basis functions are total maps with their exact parameter/result tree
and actual arity; Boolean expressions, ordinary Basis calls and all bodies must
check. Two-argument `xor2`/`and2` are valid noninjective predicates. Injectivity
of a whole coherent lift is a separate real finite evidence obligation, not a
global admission condition for every Basis function. Meaning declarations check
their actual referenced ordinary Basis declaration, exact domain/result and
phase/permutation kind; finite materialization/contract evidence stays real.
Basis labels are not runtime quantum owners; Basis and Meaning declarations
are not ordinary runtime callees.

Op formals start without access. Apply/Adjoint/Controlled requirements grant
only the individually named same-declaration formal; duplicate/wrong-category
requirements reject. A Meaning refinement or Unitary assertion grants no
access. Static operations/transparent providers must have the actual checked
unary quantum endomorphism interface and required access; preserve exact
composition/tensor/control/conjugation/repetition bases and phase. Register
all dependencies and principal-Unitary obligations from these operations.
For `qif`, check control then target and both providers against the exact target
basis and Controlled access; both must have principal Unitary effect. No named
function, external claim or annotation substitutes for that derived effect.

Computed/coherent forms retain exact predicate arity, captures, protected
owners, local binder visibility, result frame and body effect rules. Keep the
existing two-argument protected `with_computed` restrictions distinct from its
explicit logical/certified form. Generic typing does not establish all-input
injectivity, full-state clean return, dirty restoration, provider correspondence
or Meaning equality. Store those obligations with original identities and
enforce them at their existing actual concrete gates; unresolved evidence must
refuse, including for bundled definitions. No unchecked clean-release path is
introduced.

Infer effects from the complete checked graph with the existing
`Unitary <= Iso <= Observe` lattice and least BodyEffects solution. Validate
assertions and every principal-Unitary use only after dependencies/decrease have
checked; assertions are upper bounds, never inference seeds. Retain the semantic
error explanation that `"externally unitary"` is unsupported, without an Issue
link. Source checking must finish for every declaration before a public effect
fact or preparation result is returned.

## One typed sealed catalog; concrete eligibility remains separate

Replace profile-selected source signature lookup with one typed catalog of the
existing **27 distinct fully qualified names**, not string signature parsing
or new semantic primitives. Preserve these interfaces and exact intended
meanings from `core.rs`, `sized/primitive.rs` and the primitive Reference:

| Names | Static/runtime contract; quantum effect |
| --- | --- |
| `std::quantum::{h,x,z,t,s,sdg,tdg}` | No static arguments; `Q<Bit> -> Q<Bit>`; Unitary. Keep their exact existing phases, including aliases' T powers. |
| `std::quantum::{id,phase_eighth}` | No static arguments; **one** `Q<A> -> Q<A>`; Unitary. `id` is identity and `phase_eighth` is scalar `exp(i*pi/4) I`. |
| `std::quantum::init0` | No static/runtime arguments; `Q<Bit>` result; Iso, fresh zero owner. |
| `std::quantum::cnot` | No static arguments; two `Q<Bit>` arguments and ordered `(Q<Bit>,Q<Bit>)` result; Unitary. |
| `std::quantum::toffoli` | No static arguments; three `Q<Bit>` arguments, `((Q<Bit>,Q<Bit>),Q<Bit>)` result; Unitary. |
| `std::quantum::{split,join}` | No static arguments; unary `Q<(A,B)> -> (Q<A>,Q<B>)`, binary `(Q<A>,Q<B>) -> Q<(A,B)>`; Unitary, coefficient +1, exact binary tree/axis order. |
| `std::observe::{measure_z,reset,discard}` | No static arguments; respectively `Q<Bit> -> Bit`, `Q<Bit> -> Q<Bit>`, `Q<A> -> Unit`; Observe, with existing destructive measurement/reset/discard meanings. |
| `std::quantum::{phase,controlled_phase}` | Two Nat arguments `[j,k]`; unary `Q<Bit>` endomorphism or two ordered `Q<Bit>` inputs/results; Unitary. Preserve the exact existing dyadic/controlled phase meaning. |
| `std::registers::{take_bit,put_bit}` | `[n,k]`, requiring `k < n`; unary `Q<Bits<n>> -> (Q<Bit>,Q<Bits<n-1>>)`, binary inverse interface; Unitary, ordered extraction/insertion at k. |
| `std::registers::{empty,consume_empty}` | No static arguments; nullary `Q<Bits<0>>` result / unary `Q<Bits<0>> -> Unit`; Unitary, explicit zero-owner introduction/elimination. |
| `std::classical::{empty_bits,prepend_bit}` | Nullary `Bits<0>` result; or `[n]`, `(Bit,Bits<n>) -> Bits<n+1>`; Unitary quantum action, ordinary values only. |
| `std::quantum::{unit,finish}` | No static arguments; unary `Unit -> Q<Unit>` and `Q<Unit> -> Unit`; Unitary, coefficient +1, complete argument evaluation and explicit owner transition. |

Here A/B are exact common Basis trees, not implicit conversions or new public
notation. The common **source** `phase_eighth` rule preserves the existing
finite contract on any single `Q<A>`, including a packaged tuple. Ordinary
values and tuples of separate quantum owners still reject. This deliberately
removes the current selected atom-only *source* restriction. Its existing
concrete scalar preparation supports only Unit/Bit/Bits atoms; keep that
restriction as a located eligibility failure until actual tuple preparation
has independently reviewed support. Do not equate scalar phase with T or
`phase[1,3]`, erase it at Unit, or invent native support from catalog membership.

Retain every actual emitter/profile restriction. In particular selected
concrete phase still requires `k <= 8, j < 2^k`, registers `k < n <= 8`,
prepend `n < 8`; finite/Raw unsupported registers/Unit maps remain unsupported.
Catalog membership supplies types/effects, not a leaf, retained contract,
provider body, native rule or accepted handle. Check all four real ordinary
bundles through the same judgment, including private `nonzero2`, qif, toffoli,
exact nested split/join, computed reflection and retained-meter Observe bodies.
This unit neither renames std namespaces nor exposes canonical generic QFT.

## Accounting, order and public diagnostics

One `SourceLimits` capacity argument configures the **same judgment algorithm**;
it cannot choose alternate semantic rules. Add an explicit project-wide
**1,000,000 common source-work cap**. Charge each original-AST visit and new
checked/interface/index/dependency/owner/type storage cell, copied tree and
solver-context copy **before** visiting/allocating/cloning it. Checked integer
arithmetic must reject overflow; use bounded iterative traversal and preflight
cardinality/tree size rather than build-and-count allocation. Shared retained
objects are charged once, actual copies each time. No body clone or uncharged
second lexical table is allowed. This new generic-work rejection is a stated
engineering migration, not constitutional quantitative RS evidence.

Uniform per-value/type limits remain 4,096 cells/depth64. Preserve selected
16,384 retained live-scope type cells as an explicit capacity option; do not
silently impose that new scope ceiling on finite source. Preserve existing
finite aggregate/source-snapshot/type capacities and its **separate** 1,000,000
lowering/evidence work budget; common checking does not reset, lend or replace
that budget. Retain finite Basis12-bit capacity, exact arithmetic/matrix budgets,
1 MiB/128-source retained evidence limits, and existing depth/repetition limits.
Retain selected closed Basis8-bit, 100,000 concrete cells, 1,024 calls and
aggregate fold iterations, depth16 and 10,000 concrete steps. Preserve bounded
linear arithmetic, 32-variable/64-alternative/4,096-constraint and 50,000-work
solver limits with recursive error order. No incomplete search becomes proof.

Existing loader byte/edition/parser rules precede common checking: original
complete parsing precedes resolution/interfaces/bodies. Preserve common syntax
depth64, tuple64, natural-depth128 and existing bounded import-prefix limits;
selected token10,000/comment-depth64 policy remains explicit. Removal of its
per-module projection means a later parse failure can now precede an earlier
profile refusal. After complete parsing, original source semantic errors must
precede finite/Raw/hierarchy eligibility. No missing/failing native checker can
trigger a source-policy retry or acceptance fallback. Text/JSON must distinguish
source semantic errors, source capacity, concrete eligibility, evidence and
native failure, with original byte spans and no false rewrite suggestion.

## Bounded validation and mechanical completion

Before code, record this exact candidate as an ordinary #32 contract and its
source/library prerequisite relationship to #317. After code, retain actual
raw results for the same 72 authored forms and identities. **Do not demand
byte parity:** expected changes include real private zero-fold ownership,
Basis result/arity, qif capability/effect/tree and static-shadow errors before
old unsupported gates; mixed valid source can still fail finite eligibility.
All four bundles must be source checked even when the selected concrete entry
uses none. Preserve unmodified first diagnostics/native journals, explicitly
classify actual changes and never equate fewer/more journal rows with proof.

Use existing meaningful tests plus tiny controls for import-only cycles vs
actual dependency cycles, public/private self-imports, final-token locations,
static/global shadow vs live/moved runtime owners, forward kinds/premise/type
error priorities, copied/context/type budget boundaries, exact Basis arity,
every constructor and every genuine source consumer. Add a packaged-tuple
scalar source control with an honest selected eligibility outcome, zero owners,
branch/fold/private negatives and unchanged supported small concrete output
controls. Test controls may use at most three source qubits; do not newly
generate/check maximum-size inputs or 3,000-file stress trees.

Completion requires both actual production entry paths to consume the same
full-original judgment/facts before eligibility; all current forms and all four
unchanged bundles fully checked; obsolete duplicate generic source loops/oracle
removed or confined to actual output checking; all changed diagnostics and
capacity rules documented; independent actual-code review and relevant latest/
MSRV Rust, policy/inventory/coverage/edition/book/constitutional checks recorded
on the final inputs. Keep performed, failed/retried, skipped and pending checks
separate. A supported source form may still have unsupported concrete lowering;
publish that limit without claiming common emitter completeness.

QS source/IR/native/runtime preservation, PR actual-output correspondence and
quantitative RS remain pending at their stated scopes. Exactness, cleanup,
provider binding and native artifact/request identity are not weakened. Existing
conditional analytic Fourier results retain their actual premises; this checker
does not supply their missing decoder/native/source/general-family links.
No theorem, certificate, guarantee/adoption or full CI/release completion is
created by this contract or a successful bounded implementation. #32 remains
open until its full criteria are met; #317 retains all 24 criteria. This unit
assigns no Issue completion credit or change to the selected 111 denominator.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
