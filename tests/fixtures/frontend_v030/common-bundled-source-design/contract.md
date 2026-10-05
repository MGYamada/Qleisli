# Candidate ordinary common bundled-source prerequisite

**Status: local candidate for independent technical review; non-normative and
not yet recorded in Issues #32/#317.** This is a proposed before-code
implementation contract, not an adopted Reference rule, constitutional
interpretation, guarantee, proof, completed feature or release approval.

## Purpose and preceding contracts

The next bounded unit may converge source ownership and bundled-source
provenance before the common generic checker and canonical library exposure
are ready. It implements a prerequisite of the one-language requirement in
[#32](https://github.com/MGYamada/Qleisli/issues/32) and the reviewed ordinary
[#317](https://github.com/MGYamada/Qleisli/issues/317) sequence. It must not
create profile-specific bundled ASTs, skip incompatible declarations or turn a
resolved library name into semantic authority.

The eventual canonical identity remains `std::transform::qft<N>`, with the
reviewed positive Fourier meaning for static N >= 0, including exact identity
on the same `Q<Bits<0>>` owner at N=0. That identity is not exposed by this
prerequisite. All 24 #317 criteria and all remaining #32 criteria stay required.

## Proposed first implementation unit

Add private `frontend/source.rs` with an immutable `SourceCollection`, a
private construction boundary and a fixed `BundledRegistry`.

1. Each collection entry retains its complete original UTF-8 source, the
   complete common `ast::Module`, module identity, diagnostic source path and
   source origin. Preserve comments, byte spans, declaration order, visibility,
   static premises, every body and exact type trees. Syntax is parsed once for
   that load through the existing common parser under the caller's current
   capacity policy. Profile projections are downstream private views; they
   may not reparse or substitute different source.
2. The fixed registry contains exactly the current four sources
   (`std::arithmetic`, `std::basis`, `std::routines`, `std::transforms`) and
   their actual embedded `stdlib/Qargo.toml`. Preserve their bytes, ordinary
   source status, existing `<bundled>/std/...` diagnostic paths, licences and
   notices. The registry grants no primitive, trusted effect, Meaning, inverse,
   control or native acceptance authority.
3. Construction is internal. Provide no public caller-supplied registry,
   replacement source, `allow_std` escape hatch, ambient search/download or
   root-Qargo manifest. Local/in-memory callers cannot impersonate the
   `std` namespace or designate their own text as a bundled source. This
   requirement does not silently redefine the existing publicly mutable
   `Project` compatibility API.
4. The finite loader constructs the collection, then consumes its entries
   into the existing owned public `Project` fields. Do not retain a second
   immutable collection beside those mutable compatibility fields. Compilation
   continues to rebuild Resolution and complete declaration checks from the
   current Project; do not cache an earlier AST, resolution, inferred effect
   or accepted handle across mutation.
5. Sized `ParsedProgram` retains the collection instead of independent
   source and common-syntax maps. Its existing private checking projection,
   Resolution, source-order `ast_index` links and body-derived effects must
   continue to refer to that same collection. Preserve its source/syntax/
   documentation/module-name public views. File loading retains the actual
   selected path; direct in-memory parsing has no invented file or manifest
   provenance and remains explicitly the current in-memory edition-2026 API.
6. Continue finite loading of all four bundles. **Do not implicitly inject
   them into the sized path in this unit.** Existing bundled basis/qif bodies
   are not supported by its current projection, while finite lowering lacks
   sized Nat/fold support. Registry availability alone repairs neither gap.
   No entry-based filtering, declaration removal or privileged QFT resolution
   may hide that incomplete integration.

## Capacity, edition and checking invariants

Preserve current finite SourcePolicy defaults (1 MiB per source, 16 MiB total),
its explicit Legacy adapter, positive-limit/checked accounting, bounded reads
before UTF-8 allocation, anchored non-symlink discovery and separate directory
entry limit. All actually loaded bundled source bytes still count once toward
the same aggregate and per-source limits; static embedding is not a budget
exemption. Manifest reading retains its independent 65,536-byte cap.

Preserve sized 1..64 modules, 64 KiB per module, 1 MiB aggregate, its bounded
common scanner/parser limits (10,000 tokens and comment nesting depth 64), nesting/type/work
limits and located diagnostics. Do not raise limits, parse an oversized source
before checking it or bypass a failed capacity check through another profile.

Filesystem loads still validate the actual closest/nested schema-2
`[qrate].edition = "2026"` manifest, including malformed nearer manifests,
selected-root identity and unsupported-edition rejection. Validate the exact
embedded std manifest when its sources are loaded. Edition is constitutional
identity, separately from package version and grammar/target compatibility.
A source hash identifies bytes; it neither establishes AST correspondence for
a caller-mutated Project nor authenticates authorship or proves preservation.

The collection is not a type/effect/ownership checker. Existing complete
profile checks remain unchanged: every supplied/loaded declaration, unused
function/import, static alternative and zero-fold body retains its prescribed
checks. An unsupported declaration rejects honestly; it is not omitted to make
a selected entry pass. Current profile differences remain explicit temporary
limits. The later shared generic/type/effect checker must examine the complete
common collection before finite/Raw/hierarchy eligibility is selected, as
required by #32 and #317; that integration is not completed by this unit.

## Bounded completion evidence

Before implementation, retain the current input map and genuine first-source
diagnostics. For the implemented unit, compare complete finite and explicit
sized source/AST views and paths; test duplicate/reserved module rejection,
unused invalid declaration rejection, exact budget boundaries including
bundled bytes, invalid edition/nearer-manifest behavior, and rebuilding after
public Project mutation. Compare existing bounded executable callers' real
outcomes and native request/artifact bytes where claimed. Tests must not simply
copy the registry's implementation as their oracle. Preserve real failures.

This unit may be reported complete only as **shared source ownership and fixed
bundled provenance**, after its relevant checks pass. It completes neither
canonical generic QFT availability nor complete common checking, semantic
namespace migration, #32, #317, #152's later consumer contract, general source
preservation, same-commit full CI or release readiness. Small N=0..3 QFT
experiments and independent exact phase/axis/specialization checks remain
subsequent work under #317; do not generate new maximum cases.

## Constitutional impact

This ordinary refactor applies QS-2026-01, PR-2026-01, RS-2026-01 and
EXACT-2026-01. It preserves full sources/interfaces, scope/owners, phase/axes,
source-to-request/artifact binding and honest checking limits. Host input
budgets are not quantitative program-RS certificates. Add no Lean/native
primitive, checker acceptance rule, semantic assumption, project axiom,
epsilon relaxation or fallback. Preserve both admitted ordinary QLV1
ownership/scope guarantees with their exact premises and current evidence;
they do not prove source collection, lowering or hierarchy preservation.
Broader QS/PR/RS and exactness duties remain pending. Edition and dependencies
are unchanged. A new constitutional interpretation or guarantee still needs
the responsible human's separate affirmative judgment.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
