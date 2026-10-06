# CI scheduling and evidence

`profiles.json` selects docs-only versus executable validation conservatively.
Executable, proof, normative and unknown changes still run every selected suite.
`ci_profiles.py` separately selects proof maintenance without treating tests as
proof evidence. Required contexts aggregate all selected suites against the
exact checkout; missing/unknown lanes and failed/skipped selected jobs reject.
Dependency archive misses take the same validation path. Cargo `target`, Lean
project outputs and prior validation reports are never cached.

PRs with **1,000,000 or more added plus deleted text lines** are forbidden. The
human-authorized exception is only the existing `MGYamada/Qleisli#307`; it does
not cover later PRs, branches or repositories. `scripts/check_pr_size.py` counts
the exact event head against the unique merge base of its exact base/head,
using Git `--numstat -z --no-renames`: a move counts as deletion plus addition.
Binary records are reported separately; this is not a file-byte limit. The
first `changes` check binds repository/PR number, merge ref and both merge
parents to the workflow context, rejects missing/malformed/shallow data, and
runs before suite selection. Failure of `changes` fails the existing required
contexts. Push/manual runs explicitly report the PR rule as not applicable.
No claim is made that local JSON authenticates GitHub or that this installs
branch protection; enforcement-code changes still require review.

Before creating a later PR, run `python3 scripts/check_pr_size.py --base BASE_SHA
--head HEAD_SHA` with complete history and full commit hashes. Local preflight
has no exception and counts committed changes only; repeat it after committing
the final tree. Splitting reviewable work must retain every required check and
protected source, proof, evidence and history; deleting them to shrink a PR is
not authorized by this rule.

## Size budgets

The maintainer requested recurrence protection for generated fixtures. The
configured operational budgets in `size-budgets.json` are **150 MiB
(157,286,400 bytes)** and **18,000 files** for all fixtures, and **100,000 added
fixture text lines per PR**. Exact limits are allowed; exceeding any limit
rejects. Only canonical `MGYamada/Qleisli#307` has the existing PR-growth
exception. It never waives total bytes or files. The separate whole-PR rule
still rejects 1,000,000 or more added plus deleted text lines. Raising a budget
requires explicit human instruction; changing config, adding an ignore rule,
relocating or compressing required records to evade a budget is unauthorized.
Keep protected sources, proofs, counterexamples, notices and historical evidence.

`check_fixture_budget.py --hosted` runs in `changes` before suite selection.
Totals count the exact checkout Git tree, using uncompressed **stored blob
sizes per path**, including dotfiles and repeated content. Symlinks, gitlinks,
missing roots and malformed data reject. Canonical Git LFS pointer fixtures
reject without fetching external payloads. Stored archive bytes are counted;
expanded archive contents and external payloads are not measured. PR additions
use the event's exact base/head and unique merge base with no rename detection;
moves into a fixture path count as additions. Binary changes are reported
separately, and deletion counts cannot offset additions. Push/manual runs still
check committed totals. The existing required contexts reject gate failure.

Agents must run `python3 scripts/check_fixture_budget.py` before committing
fixture generation. This local preflight counts **every** working fixture file,
including ignored/untracked files, dotfiles, caches and hardlinked paths. It
never follows symlinks and rejects special, unreadable and missing HEAD/index
fixture files; staging a deletion cannot hide it before its reviewed deletion
is committed. Do not delete records automatically to satisfy the budget.
Local inspection is not an atomic filesystem snapshot: rerun after generation
and immediately before committing. It cannot prevent writes after inspection;
the committed CI gate checks the final immutable tree.

For already committed inputs, prefer exact immutable Git commit/path/hash
references and focused changed-file or command evidence over repeated complete
inventories or source snapshots. Preserve required first-source, failure and
counterexample records.

`--base BASE_SHA --head HEAD_SHA` gives a committed local fixture preflight,
with complete history, exact hashes and no PR-growth exception. Whole-PR
preflight remains a separate required check. Put new `--report` output outside
`tests/fixtures`; existing destinations are refused, including hardlinked files.
An internal report could invalidate its own measured totals.
Policy fields, ceilings and the single exception are validated; hosted policy
bytes must match the counted commit. No environment variable or candidate
record can raise a cap or choose a PR exception. Offline environment/JSON
can simulate the caller but cannot authenticate GitHub provenance. Reports
are small external observations, not new fixture snapshots or release approval.

Constitution, governance records, constitutional fixtures and Reference changes
select the full policy-risk lane. The always-run documentation job also checks
the adopted constitutional identity, historical candidate evidence, pending
ledger, separately adopted initial interpretations and scoped admissions. PR/push checks compare
the available event base; the separate tag/readiness gate requires complete
scoped acceptance and exact-candidate validation evidence. This is the first identity-enforcement
component of #141, not complete interpretation/proof/artifact enforcement.
Human decisions and changes to enforcement code or workflows still need review.

Edition coverage distinguishes filesystem projects from exact historical
in-memory experiments. `scripts/edition_history.json` pins the original routed
control experiment, generator, 42 sources and 14 unused manifests. The generator
passed source strings directly to `ParsedProgram`; its malformed manifests were
never filesystem-admission evidence. The checker preserves those bytes and
reports them separately. Changed or additional inputs do not inherit this
classification; ordinary projects still require a valid schema-2 manifest.

The live v5 ledger retains the v4 separation of append-only admitted identities
from current evidence bindings and adds the human-adopted, pending EXACT-2026-01
supplement across QS, PR and RS. Explicit code registrations bind reviewed human events and exact
proposal entries; fixed verifier profiles name their precise identity coverage.
Candidate JSON cannot register an approval, select executable commands or omit
an existing guarantee. Trusted-base checks preserve earlier entries across
schema migration and append, while current source/proof evidence may refresh.
`check_constitution.py --verify-lean` dispatches every selected fixed profile
against one ledger/evidence snapshot and rejects replacement during checking.
No new guarantee or full constitutional discharge follows from this migration.

The scoped QS checker validates the separately recorded human admission and
binds two declarations, independent predicates and current proof evidence to
the current Lean source closure. The always-run job checks identities and rejection regressions;
`model`/`full` also compare elaborated types, axioms and the complete Acceptance
and Artifact structure fields after building and auditing the Lean environment.
The fixed continuity extractor additionally compares the actual elaborated
definition/constructor/recursor closure with the separately rebuilt historical
baseline. This permits unchanged-meaning source formatting and theorem proof
maintenance while rejecting witness, decoder or predicate weakening. Current
checker-success types still quantify the actual input bytes and original root;
recorded extraction alone is not a live proof check. Source and evidence records
must remain unchanged throughout replay. Representation-changing transport is
not yet supported. Historical reviewed meanings remain protected
separately from current implementation evidence. These checks preserve the
recorded admission; they cannot supply the human adequacy judgment or complete
production-wide QS, PR or RS.

## Progressive test-oriented CI (#223)

| Lane | Selection | Work |
| --- | --- | --- |
| `tests` | Ordinary known implementation/test changes; explicit manual tests | Native kernel build, source/compiled policy and Audit, all native positive/negative/differential comparisons; registry source identity and policy tests. |
| `model` | Changed mathematical proofs or normative contracts | Tests plus Mathlib package build and compiled declaration audit. |
| `full` | Tags, release branches, default manual runs, policy/toolchain/registry changes, missing diff or unknown inputs | Tests plus both packages' proofs, retained reductions/equivalence, fresh kernel/Main replay and rebuilt schema-type binding. |

Both platform bundle jobs forward this same lane to `package_lean_kernel.py`.
`tests`/`model` build from a fresh copy, audit every native declaration and run
relocated acceptance/rejection tests; `full` also freshly replays both roots.
The packager defaults to `full`, rejects unknown lanes, and records the selected
lane, whether fresh replay ran, source/file hashes and per-command times in its
manifest. `model` describes only the native bundle; mathematical maintenance
still runs in the separate required Lean job. Packaging-policy changes select
`full`. No previous executable or validation output is reused.

Full macOS/Linux jobs also retain native distribution archives and SHA-256 files.
`archive_lean_kernel.py` requires a clean commit, matching source/payload hashes
and full fresh replay. It preserves licenses and records the exact source commit
inside the archive. CI artifacts are candidates: publishing GitHub Release assets
still requires all required checks on that same commit. Never relabel artifacts
from a PR merge commit as a different release commit or overwrite published assets.

| Validation obligation | Routine `tests` | Additional `model` / `full` work |
| --- | --- | --- |
| Actual native correctness theorems | Typechecked with native build | Retained; `full` replays compiled kernel/Main independently |
| Mathematical bridges | Source identity only | `model`/`full`: package build and declaration audit |
| Reduction/equivalence examples | Covered native regressions continue | `full`: retained Lean reduction/equivalence files |
| Native execution, original-input protocol and independent oracles | All retained comparison groups, relocated bundle tests | Same required comparisons in heavier lanes |
| Source/compiled policy and forbidden-declaration mutations | Required, including private/generated helpers | Retained in all lanes |
| Schema/release binding | Exact source identity; no proof claim | `full`: rebuilt theorem types and exact-source release assurance |

The native kernel's existing proofs necessarily typecheck in its ordinary
build. Their statements are retained; no theorem is downgraded to a test claim.
The deliberate first step is to remove whole-project Mathlib/reduction/fresh
replay from routine implementation CI, not to delete proofs or complete every
future harness migration. No authority, public acceptance or schema gate moves.
Tests and full validation operate on the same source/toolchain binding. A
registry update changing only `source_revision` uses the exact current-source
identity check without forcing full replay; exported types, domains, enablement
or other registry fields changing (or unavailable/invalid previous data) force
`full`. Both sides are parsed with duplicate-field rejection. This prevents
routine kernel source edits from accidentally selecting full via their required
source-hash refresh.

`validation=tests` is explicitly weaker than release proof validation. Only
`validation=full` (or the forced full tag/release route) satisfies the full
release lane. Rollback is to select `full` in `ci_profiles.py` for all executable
changes; the retained full commands require no reconstruction.

## Local MSRV tool selection

Validate the executable identities before reporting a local MSRV result.
`rustup run 1.85.0 cargo clippy` can discover an ambient `cargo-clippy` through
Cargo's external-subcommand lookup; Cargo's version alone does not establish
the compiler or Clippy version. Resolve all four executables from the selected
toolchain, inspect their `--version` output, and retain the selected identities
with the command result:

```sh
qleisli_msrv_cargo=$(rustup which --toolchain 1.85.0 cargo)
qleisli_msrv_clippy=$(rustup which --toolchain 1.85.0 cargo-clippy)
qleisli_msrv_rustc=$(rustup which --toolchain 1.85.0 rustc)
qleisli_msrv_rustdoc=$(rustup which --toolchain 1.85.0 rustdoc)
"$qleisli_msrv_cargo" --version
"$qleisli_msrv_clippy" --version
"$qleisli_msrv_rustc" --version
"$qleisli_msrv_rustdoc" --version
RUSTC="$qleisli_msrv_rustc" RUSTDOC="$qleisli_msrv_rustdoc" \
  "$qleisli_msrv_clippy" clippy --all-targets -- -D warnings
```

Use the resolved Cargo with the same explicit compiler/doc selection for tests.
Select an audited native kernel for tests that require acceptance. Keep bounded
validation targets separate by toolchain; incompatible cached compiler artifacts
are a failed invocation, not a test failure or permission to suppress a check.
Qualify earlier mistaken toolchain claims explicitly while preserving historical
records. All-target Clippy, focused tests and complete all-target tests are
different evidence and must be reported separately.

## Native comparisons (#206)

`native-comparisons.json` retains all 65 comparison groups (66 commands) from
the v0.2.6 workflow, including small independent complex/rational/source oracles
and existing capacity cases. No new maximum-size corpus benchmark is added.
The inventory regression pins the original command/environment coverage; only
the four explicit record destinations change to isolated task directories.
Direct native VM-27 request, lossless decoder and named-QPE host-fault
regressions are added (69 commands total). Full hierarchy execution also compares native-only
decisions and named-QPE residual/reference coefficients against independent
small-system oracles. These tests do not claim a universal parser/compiler proof.

The current manifest contains 67 groups and 91 commands. Local module and fold
shadowing regressions run in the sized-corpus group. Preparation/readout
transport tests require the exact product version, exercise both dynamic modes,
and distinguish version rejection from malformed or semantically invalid frames.

The native-paths group exercises the single Lean acceptance boundary through
source, raw, QIRF, foreign and Python entry points. Environment selection and
explicit kernel arguments use the same implementation; missing and incompatible
checkers cannot fall back. Runtime Rust/MSRV/installation jobs first build and
audit the matching kernel, then set an absolute `QLEISLI_KERNEL` path.

The native-acceptance group exercises immutable accepted handles, explicit
predicate domains and canonical ordinary types, and replays all
799 retained original Rust/Lean decision pairs. Those input bytes and baseline
results are immutable. It also requires the accepted-artifact round-trip suite,
including receipt-path coverage, as a distinct command. The obsolete two-verifier generator has been removed;
current Rust adapters are not described as an independent semantic verifier.
Transport failures never count as matched semantic rejection. Existing pure
component proofs, independent semantic oracles and audit jobs remain required.

## Scoped release readiness (Issue #142)

`release-readiness` runs after the eight real validation jobs for tags and for
an explicitly selected `workflow_dispatch.release_readiness`. Ordinary PRs and
manual full validation do not require completion of the 111 selected issues.
The gate requires both the full suite profile and full proof lane. The legacy
`check_constitution.py --require-release-ready` delegates to the same checker;
it rejects missing caller context instead of treating the three broader pending
QS/PR/RS obligations as an intrinsic pre-v1 release prohibition.

The human/workflow caller supplies an exact trusted base commit through the
manual `release_base` input or repository variable `QLEISLI_RELEASE_BASE` for a
tag. There is no fallback to candidate HEAD. Before using this gate for a real
release, review and commit `release/requirements.json` at that base: the exact
13 groups/111 IDs (including #311, #315 and #317), complete applicable criteria,
immutable Issue snapshot references and an explicit review record. The checker
reads these from Git blobs at the base. A candidate `release/acceptance.json` supplies evidence for
exactly those criteria. GitHub remains the only decisions/progress ledger;
these files are verification indices, not another backlog. There is currently
no real completed index. Missing reviewed requirements or acceptance evidence
is an actionable failure, not a request to auto-generate completion records.

The requirements schema is `qleisli.release-requirements`, integer version 1,
with `release_line`, `identities`, `groups`, `review`, and `issues`. Each Issue
has `id`, a `snapshot` file reference and nonempty `criteria`; each criterion
has `id`, verbatim snapshot `text`, `scope` (`required` or the already reviewed
`explicit-later-version`), and required evidence `roles`. The latter range over
implementation, reference, migration, positive, negative, jurisdictions,
production and compatibility, with all categories covered by the index. Only
the caller-reviewed requirements may mark a criterion as later-version scope.
Updating the complete criterion list or its adopted meaning requires another
explicitly reviewed base and Issue decision before release use. The gate does
not infer adoption from Issue state, reviewer names, checkboxes or hashes.

The candidate schema is `qleisli.release-acceptance`, integer version 1, with
the exact `requirements_sha256`, separate `identities`, `schema_registry`,
`proof_scope` and `issues`. Criterion entries retain their ID and disposition,
review reference and precisely the required role-to-file `evidence` map. Every
file reference is `{ "path": "repository/relative/file", "sha256": "..." }`.
The proof scope declares `scoped-pre-v1`, the exact ledger digest, sorted admitted
guarantee IDs and sorted pending obligation IDs. Edition `2026`, Qargo schema
`2`, native protocol, product version, and artifact identity remain separate.
A frontend edition check alone is not evidence that edition reaches native
acceptance; that criterion must have its own reviewed implementation evidence.

Each successful producer emits a receipt containing commit/tree, repository,
run/attempt/event, job identity and actual file digests. Its digest travels in
trusted `needs` job outputs. The final job downloads only same-run artifacts,
checks their actual bytes against those outputs, and rechecks mutable inputs
before reporting success. All producers must belong to the same run attempt;
rerunning only failed jobs cannot combine old successful receipts into a new
readiness result. The Lean producer records the result of the existing
fixed live constitutional verifier; source-only checks cannot replace it.
Distribution evidence includes the checked crate, complete source archive and
fresh installation record. Both expected macOS arm64 and Linux x86_64 native
assets retain full fresh replay, exact source and payload identities.

The CLI trusts workflow/caller-supplied hosted context; it does not authenticate
GitHub by examining a user-written environment or offline report. The supported
hosted invocation obtains context from GitHub and digests directly from `needs`,
never from candidate JSON. Local synthetic tests simulate that boundary and
cannot establish real hosted CI provenance or human adequacy. No record may
choose executable commands or validators. Successful schema/index validation
cannot substitute for human specification review or admit a new guarantee.

Generated receipts stay outside the candidate tree. The checker neither tags,
pushes nor publishes. Publication needs separate authorization and later readback
of the peeled tag, downloaded GitHub/registry assets and installed artifact
identity. A publishing workflow, if added later, must explicitly depend on the
readiness result; the existing ordinary `required` contexts remain test gates.

## Local distribution work directories

`scripts/check_distribution.py --report PATH` retains the report, command logs,
crate and source archive beside the report. Extracted sources, the temporary
installation and default Cargo targets live in a separate owned work directory
and are removed on success or failure. `--keep-work` retains that directory for
debugging; its location and cleanup status are recorded in the report. A failed
cleanup makes the validation fail and preserves the original validation error.
If Cargo emits a crate and then fails verification, the archive is retained as
unverified evidence. A failed durable copy retains the owned work with an
explicit preservation-error reason; partial copies never count as artifacts.
An explicit external `--target-dir` remains the caller's responsibility and is
never deleted by this cleanup. Historical output directories are unaffected.
