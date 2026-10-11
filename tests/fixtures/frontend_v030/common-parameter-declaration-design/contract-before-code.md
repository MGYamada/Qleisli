# Ordered common parameter-name checking

Ordinary implementation contract for #32, within the existing Reference rules.
This file grants no constitutional interpretation, guarantee, public API or
Issue completion. Root has read the frozen candidate, its author follow-up,
the separate review and the actual source constructors/callers. Desired first
sources and their actual observations are recorded separately before code.

## Target, reason and public contract

Replace duplicated spelling insertion and iterative runtime pattern-name
scanning with one private helper consumed by the two actual declaration paths.
The existing source grammar, types, owner/effect rules and diagnostics remain.
Static and runtime parameter names are unique and distinct as required by the
Reference. Each typed pattern remains one argument; exact tuple/Unit/Q-owner
shape is checked by the existing type/value rules. This name helper introduces
no value, owner, capability or evidence and performs no physical operation.

The alternative of scanning all header names before type/kind checking is
rejected: it changes first-failure ordering. A recursive visitor is rejected:
finite public mutable AST inputs must retain their existing iterative handling.
An all-leaf buffer, new projected AST/header, cached success or span/name search
for source identity is unnecessary and would introduce new assumptions.

## Actual caller order and structural association

Finite Compiler::signature claims each static Ident.text in its existing
borrowed-string set, then visits one original common argument pattern before
its type and existing Basis-pattern checks. Its set remains pre-seeded with
static names. Preserve Ownership, repeated-name spans and exact messages.
Return type stays last; outer complete profile/dependency/native stages remain.

Sized check::declaration receives the same retained original Decl identified
by its already resolved DefId, resolved module and ast_index. The private
projection maps every declaration/static/runtime parameter one for one and
rejects unsupported forms instead of filtering. Check both parameter counts
unconditionally, then use their actual source ordinal; no zip truncation or
secondary original-name/span search. These are private construction invariants,
not a new source error or a proof of projection preservation.

Sized static names keep owned strings and the existing interleaved Natural
BinderKey/Linear insertion. Natural premises/feasibility, preceding-kind and
access checks keep their exact current sequence. Then scan one original runtime
pattern in the runtime-only borrowed set before its projected type and actual
binding. Preserve name, original repeated Name span and current messages.
Static/runtime collisions still reach bind_name after symbolic type/capacity;
finite still rejects them in its pre-seeded name set. Local static-shadow policy
and whole-project diagnostic order are not silently harmonized by this factor.

The common visitor uses the original iterative pending stack, pushes Tuple
children in reverse, ignores Wildcard and lazily creates a located error on
the first repeated Name. No new limits, copies, all-header pass or owner IDs.
Complete private/unused declarations, both branches and zero-fold bodies keep
their existing checks. Earlier per-entry native calls may occur before a later
invalid sibling rejects complete preparation; no failed preparation is exposed.

## Migration and mechanical acceptance

Only pattern.rs, compile/mod.rs and sized/check.rs need production changes.
There is no public spelling/API migration or changed version/dependency/train.
Preserve all first sources and real failure/repair records. Compare every
fixed finite/selected text/JSON observation without normalizing raw output,
status, native argv/count or proposal bytes. Earlier profile/projection errors
must not be presented as evidence of a downstream declaration judgment.

Use existing bounded parameter/type/effect/unused-declaration/native tests on
actual Rust1.98.1 and MSRV1.85.0, formatting, all-target compile and Clippy with
denied warnings. Keep three existing sized ignores and explicit unrelated
3000-file import stress skips disclosed. No new maximum case or mirrored
helper-only test is needed. Review actual helper consumption and exact private
association independently; metadata identity review is separate from tests.

## QS, PR, RS, EXACT and remaining duties

QS keeps exact source type trees, names/lexical/dynamic identities, linear use,
effects, phase and reference obligations. PR keeps actual independent native
requests and source/provider/artifact correspondence requirements. This name
factor authorizes no accepted handle or realization. Quantitative RS remains
pending; source/type/checker capacities are not a program resource theorem.
EXACT supplies no tolerance replacement. Both admitted ordinary QLV1 guarantees
retain their exact scope, premises, meanings and current evidence. Protected
records, native/Lean/std bytes and edition2026 remain unchanged.

Passing this unit does not finish common generic declarations/bodies,
Basis/Meaning/control/workspace support, finite/Raw/hierarchy eligibility,
canonical generic QFT/std namespaces, source/runtime preservation, a general
family proof, all #32/#317 criteria or same-commit release gates. All111 selected
Issues and all24 #317 criteria remain; completion is still14/111 (12.61%).

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
