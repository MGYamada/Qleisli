# Phased formal-kind and access candidate

Status: non-normative before-code design for #32/#317. No implementation,
adoption, native acceptance or Issue completion. The sources beside this note
are unexecuted first candidates; this author has not parsed them, run a CLI,
test, build, native checker or Git command. Predictions below are not captured
diagnostics or stdout oracles. Existing published APIs and source grammar remain.

## Concrete shared unit

Use a private `frontend::formals` module for a declaration-local ordered state
over the retained common `ast::Decl`, actual `BinderKey`s and existing
`types::Type<N>`. It should own preceding Nat/Basis availability, insertion of
the checked exact ordinary basis of every Op, and access-target/capability
judgments. It is not a second AST or a persistent success cache.

Suggested private operations are `visit_natural(key)`,
`visit_basis(key, checked_opaque_basis)`,
`check_operation(source_parameter, key, classify_basis, refine_meaning)` and
`grant_access(source_constraint, resolved_target)`. Names describe interfaces,
not an adopted API. The common state advances exactly once per original static
ordinal and owns the available key sets. `classify_basis` receives those sets;
its result is the exact existing ordinary `Type<N>`, retained in the common Op
fact and used by the actual consumer. The refinement callback runs immediately
after that basis's existing contract-width checks, before the next parameter.
Access is a fixed three-capability mask derived in original requirement order;
target lookup must return an actual local StaticOperation in this declaration,
never a `UseInfo.global` or `static_parameter` compatibility candidate.

Finite `Compiler::abstract_bindings` (operations.rs:208) must consume the shared
checked basis/mask in its actual `Operation`, retaining finite Meaning matrices,
width/work charges and `Node::Abstract` identity construction. Sized
`check::declaration` (check.rs:188) must consume those same ordinary basis facts,
wrap them in the existing single Q owner for `Scope.operations`, and convert the
mask to its current string set once if body/callee access storage is unchanged.
No independent access insertion/repeated-capability branch should remain in
either declaration consumer. Running a common preflight but rebuilding formal
types or access unchecked afterward fails this unit's completion condition.

Type construction remains `types::classify_source` with `Stage::Basis` and the
current profile accounting. The sized projected tree was already constructed
through that classifier; it may be a temporary representation supplied to the
existing normalization callback, paired by source ordinal with the original
parameter. Preserve Basis binder identity, complete tuple trees, Q owner
boundaries, Unit/Bits0 and Bit/Bits1. Do not reconstruct an original AST from a
projected name, span or width. Private static/runtime cardinality assertions
remain; pair every original requirement with its projected requirement by
ordinal and complete count if the access adapter needs both representations.

## Required staging and the discovered priority seam

Finite keeps profile checking, lexical/dependency resolution, signature name and
runtime/result type checks, then each Op basis/Meaning and access. Its profile
still rejects Nat, Basis, Bits, Named types and predicates before common generic
checking could exercise them. Do not widen that path as part of this factor.

Sized keeps whole-module projection before later modules, indexed projection,
static uniqueness/all-Nat insertion, premises/feasibility, then ordered kinds,
access, runtime names/types/binding, result and complete bodies/effect checks.
Its context may include a later Nat premise; that does not grant the later
binder availability in an earlier Op kind.

There are **two type phases** in current sized `ty` (check.rs:89–162): the
iterative full-tree Parameter availability/substitution-capacity scan precedes
`map_parts`, which then normalizes Natural expressions. Thus
`Op<(Bits<n*n>,B)>`, with preceding n and later B, can reject B availability
before the earlier nonlinear size. A single mixed left-to-right prewalk changes
this ordering. Preserve the scan and its capacity errors first. Within an
individual Natural expression, preserve `linear::natural_inner`'s left-to-right
evaluation, subtraction proofs and nonlinear/overflow failure before any later
unavailable name. Both controls are provided as unexecuted sources.

Indexed projection already rejects a Named type whose actual local target is
not StaticBasis (parser.rs:377–399), before declaration premises/access. Preserve
that early rejection; it is distinct from later ordered availability. Likewise
preserve finite Meaning resolution/equality/matrix charges and sized projection's
unsupported Meaning-refined Op. Do not erase refinement or infer capability,
provider unitarity, inverse, controlled semantics or phase from an annotation.

## Lexical association that must be resolved before implementation

`resolve::locals::Index` borrows one immovable original Decl and records binder,
Ident-use and Natural-use occurrences by address, with deterministic structural
IDs. The finite `Forest` retains binder/Ident-use tables but currently drops
Natural-use address maps when consuming Index. Sized retains `Function.lexical`
and projected UseSiteIds/BinderKeys, while the original Index is dropped after
projection. A complete common-original-Decl judgment cannot pretend either has
an existing full borrowed Index at declaration time.

Use the same resolved DefId → module → ast_index association. The smallest
explicit bridge is a fresh declaration-local borrowed Index at the existing
checking point, compared against projected keys/IDs, or retaining the necessary
original occurrence map in a borrow that truly outlives both consumers. The
former entails an additional whole-declaration indexing allocation and requires
bounded-work review; the latter must avoid a self-referential collection or
cached facts over publicly mutable finite Project fields. Neither may search by
name/span or substitute global/static candidates for a local target. Alternatively
factor access first using existing actual Ident/local-key lookup and defer the
original-Natural-kind bridge explicitly; that is smaller but cannot claim the
whole ordered-kind unit complete. This is an implementation choice still open.

Potential production ownership after a concrete contract: new formals.rs and
module declaration; compile/operations.rs and sized/check.rs for real consumers;
only the explicitly chosen lexical bridge in locals.rs/sized.rs/parser.rs if
required. No native schema, primitive, std source, dependency or public API change.

## First sources and subsequent mechanical conditions

Each `sources/*.qli` is one independent prospective `main.qli`; the single
Qargo.toml is the exact existing schema-2 edition2026 manifest spelling. They
must not be loaded together as one successful project. A later authorized
collector must freeze its explicit per-case mappings and actual commands before
running. There is no driver or selected command metadata in this packet.

| Source | Observation purpose, not a promised result |
|---|---|
| valid-operation | Closed Bit Op with explicit Apply, common actual consumers |
| valid-dependent-basis | Preceding Nat/Basis and exact tuple Op; finite profile barrier remains |
| forward-natural | Later Nat cannot justify an earlier Op kind |
| forward-basis | Later Basis cannot justify an earlier Op kind |
| duplicate-access | First repeated Apply; finite name span versus sized whole-constraint span |
| wrong-kind-access | Local Nat named like a global function; no fallback to that global target |
| static-runtime-collision | Runtime static-name collision plus unknown access; finite signature versus sized access priority |
| unused-missing-access | Invalid generic body remains checked despite a valid closed main |
| natural-priority | Nonlinear left size before a later unavailable Nat |
| basis-scan-priority | Unavailable later Basis scan before nonlinear size normalization |

After a real baseline, compare raw status/text/JSON/proposals and actual native
argv/counts on both current toolchain and MSRV. Preserve unsupported earlier
barriers as barriers; they do not test downstream kind, capability or ownership.
Review that actual Op type/access facts are consumed, and existing unused/private
declarations, static branches and zero-fold bodies still undergo complete checks.
Do not predict zero native calls from an ultimate whole-project rejection.
Preserve 4096-node/depth64/type-shape/linear-work accounting and finite limits;
never trust public Natural.depth or parser-only bounds for mutable-AST traversal.
No maximum case is needed.

QS/PR/RS/EXACT remain pending as previously recorded; only the two admitted
ordinary decoded QLV1 guarantees remain. This ordinary Rust factor grants no
accepted handle, source/provider/artifact correspondence, quantity theorem or
approximation fallback. It does not finish common generic bodies, finite profile
convergence, Basis/Meaning support, canonical std/QFT exposure, analytic family
proofs or release gates. The original next-unit.md and its input map are untouched.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
