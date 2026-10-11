# Independent implementation review: common parameter names

Status: read-only review of the stable **actual three-file implementation**
against `7e2bf08cb2a9367e1d5fefe8ced451c3e6f57149` and the concrete before-code
contract. Reviewer: `/root/isometry_cli_tests`, who did not author this
implementation. This agent authored the earlier candidate; its author follow-up
is not independent candidate review. Independence here is from the assigned
production code author, not from the candidate's authorship.

## Result

No actionable implementation defect was found in the reviewed diff. This is a
technical source review, not a compilation, test/replay result, mathematical
proof, source-preservation theorem, policy adoption or Issue completion.
Root performs validation separately.

The reviewed stable current source hashes are:

| Source | SHA-256 |
| --- | --- |
| src/frontend/pattern.rs | 16fa6f4c4a6598c53680dc353d7dc4115f9bc137f7ebac4c723269a1d05ee27a |
| src/frontend/compile/mod.rs | bca57dab7010e7dd75597ff805c5707a7cfd7b66febce04fe8fa827faa5aa5d1 |
| src/frontend/sized/check.rs | b21f7c1623e553336854a2343fab8ce8ac602307f9171536d5fbc3830a0a40c1 |

They were observed after root announced the stable barrier and observed again
after source inspection. The final input map rechecks these same exact bytes.
The retained implementation-before snapshots match the read-only Git baseline.
The retained first edit's sized hash `2f7e0062...` differs from the stable
`b21f7c16...` only in the observed formatting of assertions, claim closure and
original-declaration lookup; the two other files match their first edit.
That first-edit record remains unchanged.

## Actual consumption, association and ordering

- `claim` owns the existing BTreeSet insertion/repeat decision and invokes its
  FnOnce error formatter only for a repeat. `claim_pattern_names` consumes
  original common Patterns with an explicit source/name-set lifetime, retains
  the former iterative pending stack, reverses immediate Tuple children for
  left-to-right visits and ignores Wildcards. It constructs no copied pattern,
  value, owner, certificate or accepted handle.
- Finite `Compiler::signature` calls claim for each static original Ident and
  the shared pattern visitor for each original runtime/basis argument. The
  combined borrowed-String set stays local to that signature; its error
  category, original repeated-name span and messages are unchanged. Each
  argument's type and existing non-name Basis shape/label check follow its
  name scan, and return typing stays last. This is actual signature
  consumption, not an unused preflight.
- Sized `check::program` retains its source-order Function loop and its
  existing resolution lookup. It obtains that actual DefId's Declaration,
  reads the retained syntax of `resolved.name.0`, and indexes
  `decls[resolved.ast_index]`. It does not search the original AST by name or
  span, use DefId allocation ordinal, pair sorted lists or cache a header.
  Resolution's DefIds are name-sorted while ast_index remains source order.
  The unchanged private projection maps every declaration and parameter in
  source order and replaces the indexed Function at that same ast_index.
- Sized declaration unconditionally asserts both static and runtime paired
  cardinalities before indexing, then enumerates the current projected
  parameters/arguments and reads each original at its actual source ordinal.
  There is no truncating zip. These assertions enforce private constructor
  invariants; they are not new source diagnostics or proof of projection
  preservation. ParsedProgram's source/projection fields remain private and
  its public syntax access remains immutable.
- Sized static names retain one owned String clone per insertion; Natural
  BinderKey/Linear installation remains interleaved as before. Premises,
  feasibility, preceding-kind construction and Access checks are unchanged.
  Its initially empty runtime-only borrowed set scans original patterns
  directly before each projected type and actual binding. The original
  repeated Ident span matches the unchanged projection's copied Name span.
  A static/runtime collision still reaches actual bind_name after
  type/capacity checking; finite still rejects it through its pre-seeded set.
- Borrowed strings originate in the same retained declaration, stay in local
  sets and do not enter Scope or outlive source retention. Existing semantic
  scopes still use projected BinderKeys and owned types. No cloned source
  Ident is substituted into the address-based lexical Index/Forest.
- The pre-existing runtime binder tail in pattern.rs is byte-identical to
  the Git baseline from `pub(super) enum Node` onward. Sized bind_name's
  boundedness, retained-cell capacity, static/index shadow, live-owner
  shadow and fresh dynamic identity order are unchanged. Finite public
  mutable Project is still freshly resolved and borrowed for checking; the
  new parameter visitor adds no recursive parser-depth assumption.
- Complete finite profile/lexical/dependency and Basis/Meaning/generic/
  concrete stages remain outside and before/around signature as before.
  Complete sized projection, declaration/body, zero-fold/both-branch,
  effect and dependency checks retain their positions. No private/unused
  declaration filter, new capacity, changed native call site or fallback is
  introduced. Earlier finite native checks before a later sibling failure
  remain possible; failure still exposes no successful full preparation.

## Existing bounded evidence read, not re-executed

The contract bytes match SHA-256
`558ec3f68f6c7f84a248ed30039eb8655625a08fe61a48d3c32f975100bd1ad1`;
the separate author's design matches
`78179937c1e00fa342bb874c050e5ac4041692cca5e94e00029cd2deaa8f3621`.

All ten first sources/manifests and the actual twenty before JSON observations
were read. Each record's raw stdout/stderr digest matches its retained bytes,
its parsed stdout matches actual raw JSON, and each native argv log count
matches the recorded count. This read subset has two successes, eighteen
rejections and twenty-two native calls. Root's full text/JSON forty-command
result remains four successes, thirty-six rejections and forty-four native
calls; those are root's executions, not this reviewer's reruns.

The observed symbolic first-argument `n - 1` failure under `n == 0` reaches
the size/nonnegative-guard check before a later runtime duplicate. Earlier
finite register/Nat/named-Basis and selected projection rejections are kept
distinct from downstream name judgments. The invalid-unused sibling records
one earlier finite native call and zero selected calls. The successful selected
record explicitly states producer-consistency, request_origin producer and
source_meaning_verified false. Success is not an independent algorithm oracle,
general family proof or source-preservation result.

## Scope and performed work

The earlier authorized constitutional guard in this continuous review session
passed against trusted
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2` after originals were reread.
This implementation changes no Constitution, ledger, adoption, Lean/native,
stdlib, dependency or edition record. Adopted QS/PR/RS/EXACT duties remain
pending broadly; the two scoped ordinary QLV1 ownership/scope guarantees retain
their exact protected meanings, premises and current evidence obligations.
The guard is identity/continuity checking, not fresh Lean replay or release
approval; no new guard run is claimed for the final source review.

Performed work: read-only scoped Git diff/show, code/Reference/contract/source
and actual prior record inspection, SHA-256/byte comparisons, and these new
review/input-map files only. Compilation and the fixed after replay were not
performed by this reviewer. No Rust/Lean build, tests, qleisli/native calls,
production source edit, old packet rewrite, Git/Issue mutation, new source
experiment, policy interpretation or guarantee admission occurred. No
maximum-size input was constructed.

This bounded unit does not complete common kind/type/declaration/body policy,
Basis/Meaning convergence, finite/Raw/hierarchy eligibility, canonical std/QFT
exposure, source/runtime preservation, #32/#317 or release gates. Root's later
actual compiler/test results must remain distinct from this source review.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

