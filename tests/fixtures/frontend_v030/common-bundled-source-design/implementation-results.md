# Retained original source collection

This ordinary implementation checkpoint follows the posted [second candidate](contract-v2.md),
the [exact Issue readbacks](posting/record.json), and the frozen
[first-source experiment](../../authoring_sessions/common-source-collection-v030/README.md).
It is a prerequisite component of #32 and #317, not completion of either Issue.
The original candidate notices and input identities remain historical records.

The private `frontend::source` collection owns complete original text, the common
AST and provenance together. A fixed registry retains the same four ordinary
stdlib bodies and their manifest. Local callers cannot construct bundled entries
or replace that registry. The finite loader consumes the collection into its
mutable public compatibility view; no parallel cache can supply checked facts.
Sized preparation retains the immutable collection and selected file paths,
while in-memory callers receive no invented file or manifest provenance.

Every existing declaration check, parser/byte policy and diagnostic order remains
in its current adapter. An earlier sized projection failure still precedes a
later parse failure. Review found that the first implementation converted the
input map before checking its module count; the guard now precedes conversion,
preserving immediate rejection without constructing another oversized map.
Two regression tests use independent simultaneous faults to check failure order.

## Actual bounded validation

- Latest Cargo 1.98.1: eight integration targets, **82 passed / 0 failed / 5 ignored**;
  formatting, warnings-denied all-target Clippy and CLI build also passed.
  [Actual commands](validation-latest/commands.json) and outputs are retained.
- MSRV Cargo 1.85.0: the same **82 / 0 / 5**, formatting and warnings-denied
  all-target Clippy passed. [Actual commands](validation-msrv/commands.json) and
  outputs are retained. This is a focused run, not `test --all-targets`.
- The first MSRV launch used Homebrew Cargo with a rustup-only `+1.85.0` argument
  and failed before tests. Its [actual stderr](validation-msrv-launch-failure/00.stderr.txt)
  and executed driver remain unchanged. The repaired fixed driver uses
  `rustup run 1.85.0 cargo`; the failed attempt is not counted as a successful run.
- Both successful validation records bind the same 130 declared source inputs
  and unchanged selected native digest before and after each command. This bounded
  map is not the complete runtime fixture closure or a compilation attestation of
  Git HEAD. Existing ignored tests and maximum-size cases were not newly run.
- All [23 before/after observations](../../authoring_sessions/common-source-collection-v030/results-after.md)
  agree exactly, including stdout, stderr, exit status, native-call count and
  proposal bytes. Replay used the rebuilt latest CLI before the MSRV run.
- The [independent technical review](independent-review.json) found no remaining
  defect after the capacity repair. It does not supply Guardian authority.
- A [second read-only audit](independent-metadata-review.json) recomputed replay
  bytes and metadata independently, and found no cached-origin privilege or
  skipped whole-declaration checking in the current adapters.
- The [reviewed inventory refresh](metadata-review/metadata-changes.json) changes
  four existing source hashes and adds the private source module. Existing
  public surfaces, capacities, 269 constructors, 20 boundaries and 21 paths remain
  unchanged. Coverage changes only its current surface digest. JSON serialization
  also renders pre-existing Unicode directly; parsed non-source metadata is equal.
- [Policy validation](policy-validation/results.json) passes all 13 fixed
  commands and 66 relevant policy regressions. Pinned mdBook 0.5.4 produces 23
  HTML files with 920 local links and 343 anchors checked. Edition, documentation,
  authoring, inventory/coverage and constitutional-continuity checks pass;
  349 declared policy inputs stay unchanged. Generated HTML was removed.

The Reference and changelog describe this actual boundary. Complete common
generic checking, finite/Raw/hierarchy eligibility, canonical std namespace/QFT
integration, source-preservation proofs and release gates remain open. Lean,
native semantics, stdlib bodies, dependency versions, protected constitutional
text, human acts and guarantee scopes are unchanged. No new guarantee or proof
discharge is recorded.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
