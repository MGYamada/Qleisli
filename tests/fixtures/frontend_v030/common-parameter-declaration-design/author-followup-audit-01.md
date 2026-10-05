# Author follow-up audit of common parameter-name candidate 1

Status: additive read-only technical audit, before implementation. The observer
`/root/isometry_cli_tests` also authored `candidate-01.md`; this is **not an
independent review of its authorship**. Root arranged a separate reviewer.
No ordinary or constitutional adoption, completed common checker, Issue
completion or release approval follows from this record.

Observed HEAD: `7e2bf08cb2a9367e1d5fefe8ced451c3e6f57149`.
The fixed inspected input subset is recorded separately in
`author-followup-inputs-01.json`. Those file hashes identify inspected bytes,
not a compiled HEAD, complete runtime closure or source-preservation theorem.
The six first-packet files remain unchanged; the five member hashes and sizes
in `first-files.json` were compared with actual bytes. All 40 members of the
earlier `source-inputs.json` also still match.

## Result and concrete implementation constraints

No mismatch between the candidate and the inspected current finite/sized
declaration paths was found. The following are constraints on the prospective
implementation, not defects discovered in a new implementation.

1. **Use the actual source ordinal, not the DefId ordinal.**
   `Resolution::new` diagnoses duplicate declarations in source order, then
   assigns DefIds in module/name order. Its `Declaration.ast_index` remains
   the original source ordinal. Sized `parser::project` maps every
   `Module.decls` element, including private/unused declarations, in source
   order; `project_declaration` maps every static parameter and every runtime
   argument one for one without filtering. The second indexed projection
   replaces precisely `functions[ast_index]`. Therefore the original
   declaration for a source-order Function is obtained from that Function's
   resolved DefId and its ast_index. Enumerating `resolution.declarations()`
   and pairing its enumeration index with `functions[index]` would be wrong.

2. **Retain and review parameter cardinality.**
   The inspected projection makes `parameters.len() == static_params.len()`
   and `arguments.len() == params.len()`, preserving each original parameter
   ordinal. A refactor must keep this structural invariant. A truncating zip
   must not allow an unchecked original or projected tail. Same spelling or
   span is not a substitute for the declaration association. The opaque
   ParsedProgram exposes immutable syntax and keeps its modules/Function
   projection private; subsequent checking changes lexical global targets and
   inferred effects, not the original Decl or either parameter list.

3. **Borrow names from one retained declaration and keep sets local.**
   Finite signature currently stores borrowed original String references in
   its combined static/runtime set. Sized static uniqueness currently stores
   owned String clones; sized runtime uniqueness currently borrows projected
   pattern Strings in a separate initially empty set. Moving sized runtime
   name scanning to original common patterns can safely borrow Strings from
   the same original Decl for the duration of declaration checking. These sets
   must remain local and must not escape into Scope, whose semantics retain
   the existing BinderKeys, dynamic identities and owned types. An explicit
   helper lifetime must connect each original Pattern borrow to the borrowed
   name set; anonymous unrelated lifetimes may fail to compile. Do not
   prolong a mutable ParsedProgram borrow or retain name addresses across
   projection replacement. No compile result is claimed by this audit.

4. **Preserve exact spellings and the iterative scan.**
   The current two uniqueness walkers push tuple children in reverse and pop
   them left to right. Wildcards introduce no name. Neither walker validates
   a whole value/type tree or calls the runtime value binder. The shared scan
   must retain this iterative pending stack and first-repeat rule. Finite
   Project/AST are publicly mutable; the lexical Index intentionally uses
   iterative tasks even for an externally constructed AST beyond parser
   depth. Reusing the recursive runtime pattern binder would introduce
   recursion at an earlier currently iterative check. No deep/maximum input
   was constructed or executed in this audit. Existing type/parser/profile
   limits and existing later binding limits remain unchanged.

5. **Preserve error and checker-call order.**
   Finite signature scans all static names first, then scans one original
   runtime pattern before classifying that argument's type; basis shape
   binding and return typing retain their existing positions. Sized static
   duplicate scanning and Natural installation are interleaved, followed by
   premise/feasibility, ordered Basis/Op kinds and Access checks, then the
   per-argument runtime scan, type classification and actual binding.
   Pre-scanning all runtime parameters before any type would change which
   defect is reported. Seeding sized runtime names with static names would
   move its existing static-shadow rejection before type/capacity checks.
   That is outside this extraction. Sized duplicate-static diagnostics retain
   the complete Function span; its runtime diagnostics retain the original
   repeated Ident span as copied by projection. The different error adapters
   are deliberate existing observations, not a harmonization implemented here.

6. **Keep complete preparation and native selection separate.**
   Finite processing freshly resolves the current Project, obtains a Kernel,
   checks every declaration's profile, indexes every declaration, orders all
   dependencies, checks the entry, and performs its existing basis/Meaning/
   generic/concrete passes. Missing environment selection can reject before
   profile checks. `Kernel::selected` itself only reads the path and constructs
   the Kernel; it does not invoke a native executable or check compatibility.
   Actual independent checking occurs later through inspect/check. An earlier
   finite concrete declaration can be checked natively before an invalid
   unused sibling rejects the complete preparation. A new global signature
   preflight would change that order. Sized projection of an earlier module
   still precedes parsing a later module, and complete generic body checking
   still precedes successful preparation. No partially checked preparation,
   source proposal or accepted handle may escape any failure.

The current Reference requires unique names across the complete parameter
list, exact pattern trees, distinct static parameters, ordered static kinds
and checking of every declaration/branch/zero-fold body. The proposed unit can
factor spelling insertion and common-source name traversal while preserving
those rejections and the existing profile-specific error stages. It does not
settle local static-shadow policy, unify complete kind/type/owner/effect/body
checking, add Basis/Meaning availability, grant a primitive or expose a
canonical standard-library API.

## Constitutional reconstruction and performed work

Repository original Constitution, governance, authority, ratification, ledger,
adopted initial/exactness texts and their adoption records, admitted scoped
proposal/admission and current evidence were read. Historical candidate status
notices were interpreted with the separate actual human adoption records.

The authorized command
`python3 scripts/check_constitution.py --base-ref faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`
completed with exit 0. Its exact returned stdout and command metadata are
retained in `author-followup-guard-01.json`. Applicable adopted QS-2026-01,
PR-2026-01, RS-2026-01 and EXACT-2026-01 retain their pending broader duties.
The ordinary QLV1 decoded-root ownership/scope guarantees retain their exact
protected scopes and premises. The guard checks current source/evidence
identity and continuity against the supplied trusted base. It is not a fresh
Lean replay, human adequacy judgment, binary attestation, full constitutional
CI, source preservation or release approval.

Other work was read-only code/Reference/contract inspection, fresh read-only
GitHub #276 retrieval, `git rev-parse HEAD`, and byte/hash metadata comparison.
The fresh #276 readback reports updated_at 2026-10-03T14:37:25Z; no Issue was
modified. An initial rg probe named absent `src/frontend/lexical.rs` and
returned exit 2; the real `src/frontend/resolve/locals.rs` was subsequently
read. That probe is not successful validation. Some oversized combined
read outputs were truncated; relevant authoritative/source sections were read
again in bounded outputs.

No Cargo/Lean build, tests, qleisli/native invocation, new source experiment,
production source change, old packet edit, Git mutation, Issue mutation,
policy adoption or proof/guarantee admission was performed. The prior pattern
unit's tests/replay were reported by root and were not rerun here or counted
as #32/#317 completion.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

