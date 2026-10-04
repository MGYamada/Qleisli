# Qleisli working guidelines

## Keep this file small

Keep AGENTS.md and CLAUDE.md identical: **100 lines / 6,000 UTF-8 bytes** each.
`scripts/check_docs.py` checks limits and equality. Replace or shorten rules;
keep rules/links here, specifications in docs, decisions in Issues, results
beside fixtures and history in Git. No release/publication histories.
Raise limits only on explicit user instruction.

## Start from the design

User instructions take precedence. Read the [ratification](docs/src/design/ratification.md),
[README](README.md), [ROADMAP](ROADMAP.md), [trust boundary](TRUSTBOUNDARY.md),
[adopted cutover](https://github.com/MGYamada/Qleisli/issues/276) and
[algorithm drafts](docs/src/imaginary-v1/index.md).
Read specifications before behavior changes; English is authoritative
for production specifications, public library contracts, comments and examples.

- Start with desired `.qli` programs and a bounded contract/checking experiment.
  Preserve first sources, real diagnostics and counterexamples under the
  [session procedure](tests/fixtures/authoring_sessions/README.md). Distinguish
  ideal drafts, executable translations, informed studies and model benchmarks.
- Follow Rust for type/ownership decisions, with explicit quantum/evidence
  obligations for differences. Preserve linear ownership, tuple shape, phase,
  axis order, explicit discard and exact clean release for every input/reference.
  Separate owners do not imply separability; measure_z consumes logical owners.
  Preserve specified types, sizes and finite contracts; names/lifetimes are not evidence.
- Specify forms/APIs, types, effects, owners, examples and lowering together.
  Planned notation is not an API. Unitarity grants neither inverse nor control
  access; unrestricted free-vector bind is not an execution API.

## Keep the trusted core small

Follow the fixed [trust boundary](TRUSTBOUNDARY.md). Convenience belongs in
untrusted desugaring/adapters; acceptance rules require an irreducible semantic/
evidence obligation. Human/AI source and raw IR undergo identical independent
checks. Valid output IR alone does not prove source preservation. Keep reference
meanings independent of acceptance and under specification review.

New M2 acceptance logic belongs in Mathlib-free `lean-kernel/`; Rust handles
parsing, diagnostics, transport, evidence generation and simulation. Independently
check IR at every Rust/Lean boundary; prove actual executable definitions.
Follow [the adopted v0.2.9 cutover](https://github.com/MGYamada/Qleisli/issues/276):
Lean alone issues new accepted handles; remove legacy paths after replacement
checks. Full Soundness remains v0.5.0; external schemas await binding gates.

Keep Lean/Mathlib at 4.30.0 and development Python at 3.11+. Follow the
[test-oriented CI lanes](.github/ci/README.md): build/audit native checkers and run
independent tests; compile changed proofs; full replay for releases,
manual full runs and policy risks. Reject project axioms, unsafe/
partial definitions and runtime overrides, including private/generated helpers.
Label temporary proofs with TP-ID, priority P0/P1/P2 and replacement/removal
conditions; keep them built/audited until callers and obligations migrate.
Distinguish code, tests, proof, preservation and specification review.

## Corpus and current work

Until v0.5.0, add algorithms to `corpus` rather than generally expand `stdlib`.
Follow [corpus policy](corpus/POLICY.md): only QuantumKatas, Qualtran Bloqs and
PennyLane Demos; source changes need explicit approval. Pin commits/file hashes
and preserve licenses/notices (Katas MIT; the other two Apache-2.0).
Library work follows [STDLIB.md](STDLIB.md) and existing source contracts.

Prioritize shared executable corpus source without waiting for general proofs.
Follow [the adopted cutover](https://github.com/MGYamada/Qleisli/issues/276)
and [sized evidence](corpus/sized/README.md). Validate small qubit systems only;
do not newly generate/check maximum-size cases. A version or bounded component
does not complete feature/R14/H1–H5 or theorem gates.

## Documentation after the v0.3.0 cleanup

Keep book sources in `docs/src/`, including the [backend plan](docs/src/lean-backend-plan-v0.3.md).
Write new chapters from adopted decisions, actual code and proofs;
migration decisions live in Issues. The retired `docs-old/` tree is deleted.
Do not restore it, its links (including pinned web links), redirects, replacement
copies of retired prose or active build/check dependencies; use Git history.
Preserve executable source, proofs, counterexamples, validation artifacts and
notices outside retired documentation. Regenerate corpus counts with
`python3 scripts/check_docs.py --write-corpus`; do not hand-edit generated views.

## Changes, versions and licensing

Use GitHub Issues for decisions/friction; no duplicate backlog. Breaking changes
need an Issue with target, contracts, reason, migration and acceptance criteria
before implementation. Compatible changes use PATCH, breaks MINOR, except the
explicitly approved v0.2.9 verifier migration (#276). Cargo.toml is authoritative; synchronize
Cargo.lock, lakefiles, Python metadata/runtime, std Qargo and research Cargo via
`scripts/maintain_release.py`; inspect its plan and source-review requirements. Never change dependency versions as part of synchronization. Require schema-2 `[qrate].edition = "2026"` per source tree; no root
Qargo.toml. Accumulate changes in [CHANGELOG](CHANGELOG.md), not per-task bumps.
Run relevant checks and record performed/skipped results accurately. For releases
validate source, packages, installation and full CI; tag the exact checked commit.
Selection, tagging, pushing and publication are distinct; published artifacts
are immutable. Documentation-only work need not rerun Rust/Lean tests.
Preserve Apache-2.0, [LICENSE](LICENSE), [NOTICE](NOTICE), third-party attribution
and Masahiko G. Yamada's copyright; public Rust packages declare Apache-2.0.
