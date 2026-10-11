# Shared runtime-pattern implementation

Finite lowering and sized generic checking now consume one private runtime
binding traversal. It selects linear-wildcard, duplicate-name and exact
tuple/ordinary Unit judgments at the actual old call sites. Existing adapters
retain original values, lexical/dynamic identities, error formatting, leftmost
failure order, scope/caller accounting and capacity limits. A borrowed view
bridges the existing sized projection; no new AST or checked-pattern cache is
introduced. Concrete sized elaboration, basis-pattern checking and declaration/
static-name policy remain separate.

The original candidate, additive v2 correction, inspected inputs, complete
tracked-path patch and independent read-only review remain fixed. The first
Rust 1.98.1 all-target check actually failed because `Self::Name` was ambiguous
with the sized enum variant. [compile-repair-01.json](compile-repair-01.json)
preserves the failure and the sole explicit `&BindingName` correction; the
independent review addendum verifies that correction without claiming tests.

Actual Rust 1.98.1 attempt02 and Rust 1.85.0 attempt01 both pass all eight
fixed stages: versions, formatting, all-target checking, four existing type
library tests, eleven integration targets, warnings-denied all-target Clippy
and CLI rebuild. Each reports **118 passed, zero failed, three existing ignored**.
Two unrelated 3,000-file import-depth/cycle tests are explicitly filtered;
the separate 4,000-source differential is not run. The 687-member declared
input map remains identical during both runs and is not complete fixture,
compilation or runtime closure. The first failed attempt is retained as failed.

The latest rebuilt CLI digest was
`58acd18d36849646e4d3d7819651fbb98128c3f5436f86e737b769b86c67c969`.
Only after that build, the fixed authoring after driver repeats all 40 original
check/emit commands. Every exit, raw stdout/stderr, native argv/count, proposal
presence and exact proposal bytes matches. Zero output-path substitutions were
needed. Both captures contain eight passing checks, two untrusted emissions,
thirty rejections and 86 native invocations. All 191 baseline files and 235
then-current selected inputs are guarded throughout. MSRV subsequently rebuilds
the shared CLI, digest
`4a5cc9e753268fd7b0b4972cf84dd1fd6338218bc0b104d71b8465fab89151cf`;
that later binary is not falsely attributed to the earlier comparison.

The metadata review preserves the real stale-inventory failure before refresh.
It updates four existing hashes and adds only private `pattern.rs`. Existing
parsed API surfaces, capacities, constructors, boundaries and routes are unchanged;
coverage changes only its surface identity to
`2967dfbeaac04aa49b93d58641f6001794a44348d3e6c69c58c3592a4d0ab3e4`.
Both guards and their independent regression suites pass. Documentation/policy
results are captured separately after the source/Reference barrier. The fixed
policy v2 runs 13 commands, all successful, with 66 book/authoring/edition/docs
regressions and 389 declared input identities unchanged. It binds the separate
17 inventory and 14 coverage regressions without rerunning them. Pinned
mdBook 0.5.4 builds 23 HTML pages and validates 920 local links/343 anchors,
including print output; the owned 3.85MB generated tree is removed after its
hashes and actual logs are retained. The original unexecuted policy v1 remains
unchanged. The temporary empty coordination lock is removed only after both
Rust drivers terminate; it is not an evidence file.

This is ordinary private factoring within adopted QS-2026-01, PR-2026-01,
RS-2026-01 and EXACT-2026-01. Protected constitutional text, human records,
ledger scopes/status, dependencies, native/Lean definitions and stdlib bytes
are unchanged. Current constitutional checking establishes identity/continuity;
there is no fresh local Lean build/audit/replay for this unchanged kernel.
Native output acceptance and these bounded tests do not establish source
preservation, analytic hierarchy meaning, a family/resource theorem or a new
guarantee. No interpretation/admission or release act is performed.

Complete common declaration/body checking and later lowering eligibility remain
required before canonical generic std/QFT and namespace migration. Neither
#32 nor any of #317's 24 criteria is closed by this unit. Confirmed progress
remains 14 of 111 selected Issues (12.61%); historical hosted CI checks a prior
merge, not this local implementation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
