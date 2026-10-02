# Qleisli working guidelines

## Keep this file small

Keep AGENTS.md within **100 lines and 6,000 UTF-8 bytes**, enforced by
`scripts/check_docs.py`. Edit or replace existing rules rather than append.
Keep durable working rules and links here; specifications belong in their
own documents, decisions in Issues, results beside fixtures, history in Git.
Do not copy release records or maintain version/publication histories here.
Do not raise these limits without the user's explicit instruction.

## Start from the design

The user's latest instructions take precedence. Before working, read
[README](README.md), [design](docs/design-philosophy.md), [AI-era goal](docs/ai-era-goal.md),
[algorithm goal](docs/algorithm-structure-goal.md), [formal core](docs/formal-core.md),
[ROADMAP](ROADMAP.md) and [requirements](docs/quantum-language-requirements.md).
Read relevant specifications before changing behavior; English is authoritative
for production specifications, public library contracts, comments and examples.

- Start with desired `.qli` programs and a bounded contract/checking experiment.
  Preserve first sources, real diagnostics and counterexamples under the
  [session procedure](tests/fixtures/authoring_sessions/README.md). Distinguish
  ideal drafts, executable translations, informed studies and model benchmarks.
- Follow Rust for type/ownership decisions, with explicit quantum/evidence
  obligations for differences. Preserve linear ownership, tuple shape, phase,
  axis order, explicit discard and exact clean release for every input/reference.
  Separate owners do not imply separability; measure_z consumes logical owners.
  Follow [types](docs/type-system.md), [sizes](docs/size-expressions.md) and
  [finite contracts](docs/finite-contracts.md); names/lifetimes are not evidence.
- Specify forms/APIs, types, effects, owners, examples and lowering together.
  Planned notation is not an API. Unitarity grants neither inverse nor control
  access; unrestricted free-vector bind is not an execution API.

## Keep the trusted core small

Follow the fixed [trust boundary](TRUST_BOUNDARY.md). Convenience belongs in
untrusted desugaring/adapters; acceptance rules require an irreducible semantic/
evidence obligation. Human/AI source and raw IR undergo identical independent
checks. Valid output IR alone does not prove source preservation. Keep reference
meanings independent of acceptance and under specification review.

New M2 acceptance logic belongs in Mathlib-free `lean-kernel/`; Rust handles
parsing, diagnostics, transport, evidence generation and simulation. Follow the
[Lean migration](docs/lean-kernel-migration.md) at every boundary; prove actual
executable definitions. Rust remains authoritative until transfer gates pass;
external schemas remain disabled until their binding gates pass.

Keep Lean/Mathlib at 4.30.0 and development Python at 3.11+. Follow the
[test-oriented CI lanes](.github/ci/README.md): build/audit native checkers and run
independent tests; compile changed proofs; full replay for releases,
manual full runs and policy risks. Reject project axioms, unsafe/
partial definitions and runtime overrides, including private/generated helpers.
Follow [temporary-proof rules](docs/formal-core.md#temporary-proof-markers);
keep components built/audited until compatible replacement and removal.
Distinguish code, tests, proof, preservation and specification review.

## Corpus and current work

Until v0.5.0, add algorithms to `corpus` rather than generally expand `stdlib`.
Follow [corpus policy](corpus/POLICY.md): only QuantumKatas, Qualtran Bloqs and
PennyLane Demos; source changes need explicit approval. Pin commits/file hashes
and preserve licenses/notices (Katas MIT; the other two Apache-2.0).
Read [routine contracts](docs/stdlib-contracts.md); library work also follows
[STDLIB.md](STDLIB.md) and the [contract ledger](docs/stdlib-contracts.md).

Prioritize shared executable corpus source without waiting for general proofs.
Follow the [continuation](docs/v0.2.2-plan.md), [VM packets](docs/verification-migration-v0.2.md)
and [sized evidence](corpus/sized/README.md). Validate small qubit systems only;
do not newly generate/check maximum-size cases. A version or bounded component
does not complete feature/R14/H1–H5 or [theorem gates](docs/release-milestones.md).

## docs/ cleanup boundary at v0.3.0

Delete obsolete plans/reports/history now; retain active v0.2.x goals and VM plans
until v0.3.0. Then retire remaining legacy docs and write from adopted decisions,
actual code, proofs and examples. No archives, copied old trees or redirect stubs;
use Git history/tags. Repair links/checks; preserve executable source, proofs,
counterexamples, validation artifacts and required notices outside docs.
Update `docs/project-status.json` and manifests, then regenerate with
`python3 scripts/check_docs.py --write-status`; do not hand-edit generated views.

## Changes, versions and licensing

Use GitHub Issues for decisions/friction; no duplicate backlog. Breaking changes
need an Issue naming the 0.x.0 target, contracts, reason, migration and acceptance
criteria before implementation. Follow [versioning](docs/versioning.md): compatible
0.y.z work uses PATCH, breaks MINOR. Cargo.toml is authoritative; synchronize
Cargo.lock, both lakefiles, Python metadata/__version__ and std Qargo, never
dependencies. Require schema-2 `[qrate].edition = "2026"` per source tree; no root
Qargo.toml. Accumulate changes in [CHANGELOG](CHANGELOG.md), not per-task bumps.
Run relevant checks and record performed/skipped results accurately. For releases
follow the [procedure](docs/crates-io-release.md); tag the exact checked commit.
Selection, tagging, pushing and publication are distinct; published artifacts
are immutable. Documentation-only work need not rerun Rust/Lean tests.
Preserve Apache-2.0, [LICENSE](LICENSE), [NOTICE](NOTICE), third-party attribution
and Masahiko G. Yamada's copyright; public Rust packages declare Apache-2.0.
