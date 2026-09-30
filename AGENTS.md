# Qleisli working guidelines

## Start from the design

This repository is design-first. Before working, read [README](README.md),
[design philosophy](docs/design-philosophy.md), the [AI-era goal](docs/ai-era-goal.md),
[algorithm-structure goal](docs/algorithm-structure-goal.md), [formal core](docs/formal-core.md),
[ROADMAP](ROADMAP.md), and [quantum-language requirements](docs/quantum-language-requirements.md).
Consult the relevant drafts. The user's latest instructions take precedence.

## docs/ cleanup boundary at v0.3.0

**User decision, 2026-09-30: aggressively retire pre-v0.3.0 material under
`docs/`, including all v0.2.x and earlier files, and write the v0.3.0
documentation from scratch.** Keep the active v0.2.x goals and verification
migration plan usable until that boundary. Do not empty `docs/` while those
goals are still current.

Delete obsolete plans, completed reports and historical narratives now; do not
wait for a Reference migration. At v0.3.0, remove the remaining legacy documents
and write a new account from adopted decisions, actual code, proofs and examples.
Do not archive the old tree elsewhere or copy it into the new Reference.
Historical lookup uses Git history and published tags. Repair links and CI
checks when removing files; do not retain redirect stubs.

The enduring direction is the three theorems and six v1 algorithm goals in
[README](README.md#project-goals). Keep executable source, counterexamples,
validation artifacts, proof code and required license/provenance notices outside
`docs/` intact. Earlier requirements to preserve historical documentation in
the working tree are superseded. Track cleanup in GitHub Issues; no duplicate
backlog record is required.

## Current v0.2.x working references

The [0.2.1 review response](docs/releases/v0.2.2.md) records compatible 0.2.2
repairs and the remaining v0.3 domain/tuple decisions. Keep reference semantics
independent of acceptance modules, following the
[dated specification-review policy](TRUST_BOUNDARY.md#reference-specification-review-2026-09-30).
The generated current overview and detailed rule inventory
are separate views of `docs/project-status.json`; update the source and regenerate
both. These temporary v0.2.x views also expire at the cleanup boundary.

**When uncertain about type or ownership discipline, follow Rust.** This is
the user's adopted default for design decisions, including structural type
equality, tuple shape, moves, bindings and scopes. Follow the
[Rust alignment policy](docs/design-philosophy.md#follow-rust-for-type-and-ownership-discipline)
and the [current type contract](docs/type-system.md). Any intentional difference
must state its quantum-semantic or evidence obligation and its checking rule;
in particular, retain quantum linearity, explicit discard and proven clean
release. Record differences explicitly instead of inventing an implicit rule.
Rust features become Qleisli APIs only through specified and tested extensions.

**Until v0.5.0, do not expand `stdlib` as a general rule. Add algorithms to
`corpus`.**
From v0.5.0, grow `stdlib` as a mathlib-style open-source library effort.
Follow [STDLIB.md](STDLIB.md) for contribution conventions, the short contract
template and QFT/adder/phase-oracle reference contracts. Fix composable meaning,
phase, encoding, ownership, scratch, approximation and resource scope before
comparing implementations. Keep source checking, tests, actual-IR proofs,
source preservation and specification review separate. The contract-document
linter checks form/links only; `qlippy` is a future tooling role, not a current
executable or semantic authority. General borrowing syntax remains a separate
type-system decision. Existing library APIs and proof/release gates are unchanged.

When adding algorithm components, read the [corpus](docs/algorithm-corpus.md)
and [routine contracts](docs/algorithm-routines.md). For standard-library work,
read [STDLIB.md](STDLIB.md), the [layer-3 plan](docs/stdlib-roadmap.md) and [contract ledger](docs/stdlib-contracts.md);
record each public API's contract, verification state and adoption criteria.
Follow the [adopted library goal](docs/stdlib-roadmap.md#adopted-library-goal):
a BLAS/LAPACK-like foundation for quantum computing integrating reusable
components, a quantum-information textbook and formal specifications. Readers
should be able to learn quantum information by reading the library. Connect
concepts, derivations, readable source, examples and explicit proof status;
this fixes the goal, not the comprehensive module hierarchy or generalized APIs.
Use the [static-operation contract](docs/static-operations.md) to determine the
implemented inverse/control/repetition scope. Planned notation is not an API.

`Cargo.toml` is authoritative for the current version. Consult the
[generated status and rule inventory](docs/current-status.md) and the matching
release record. Distinguish version selection, design adoption, implementation,
validation, proof, tagging and publication. Preserve the finite contract
foundation and follow the [acceptance criteria](docs/release-milestones.md),
[conformance history](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md), [language v0](docs/language-spec.md)
and [grammar](docs/syntax-v0.md). General Rust adequacy and soundness proofs are open.

**North star: make the language people use to think about quantum algorithms
coincide with the language they use to write programs.** V1 requires actual
source for Shor, QPE and Grover that preserves textbook structure and meets
V1-C1–C5. Retain fixed-size examples as regressions; names or pseudocode alone
cannot satisfy these gates.

Follow the [program-first development method](docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write):
first write quantum programs as they ought to be expressed, then develop the
language with AI to express and check them. Keep ideal-source drafts distinct
from executable translations; use concrete gaps to select abstractions without
bypassing semantic contracts, independent checking or release gates.

Prioritize executable `.qli` examples and source fixtures when evaluating
authoring ergonomics, especially for LLMs. Discover missing abstractions from
real programs, retain minimal failed attempts and semantic counterexamples,
and update the [authoring report](docs/qli-authoring-feedback.md). Keep the
[quick reference](docs/qli-quick-reference.md) copyable and its code CI-checked.
An authoring exercise is not a measured model benchmark or an algorithm proof.
For new authoring/repair studies, follow the [session record procedure](tests/fixtures/authoring_sessions/README.md):
save the first source before checking, append real diagnostics and revisions,
and distinguish informed/curated work from controlled model evaluation.
Track unresolved friction in a GitHub Issue, with concrete source/design evidence,
the obligation to remove, and a checking/acceptance experiment. **When a GitHub
Issue is created or already tracks the work, no backlog entry, backlog update
or backlog ID is required.** Use the Issue as the tracking record; do not require
duplicate records. Do not recreate the retired backlog. An Issue does not
select a release or adopt syntax. The current development version is
0.2.3, selected on 2026-09-30 for explicit Qleisli edition 2026. See the
[edition contract](docs/language-editions.md) and [development record](docs/releases/v0.2.3.md).
Require explicit schema-2 `[qrate].edition = "2026"` in each source tree's
`Qargo.toml`; keep manifests in `corpus/`, `stdlib/`, individual examples and
test trees, with no repository-root manifest. The `std` qrate in `stdlib/` has
a complete qargo-compatible manifest; other source trees will all migrate to
qrate management in the future. The user selected a narrow v0.2.3 compatibility
exception for the new manifest requirement; other PATCH obligations remain.
Follow the
[continuation plan](docs/v0.2.2-plan.md),
[development record](docs/releases/v0.2.2.md) and
[release procedure](docs/crates-io-release.md). The latest published release is
[0.2.2](docs/releases/v0.2.2.md#successful-publication-2026-09-30).
Version selection does not complete wider feature gates or perform publication.
The published foundation and its
validation remain in the [0.2.0 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md). The finite B019 closure and
0.1.9 publication history remain in its [record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.9.md).
The 2026-09-30 user decision keeps completed corpus experiments/review fixes
and bounded Rust/Python/OpenQASM/QIR connections in [0.2.1](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.1.md).
Remaining production hierarchy, sized source/shared measured QPE and
execution/proof/H1–H5 integration move to [0.2.2](docs/v0.2.2-plan.md).
The later 2026-09-30 user instruction stages verification implementation across
[0.2.2–0.2.9](docs/verification-migration-v0.2.md), superseding the K1/0.3.0 and
K2/0.4.0 schedule and the all-in-0.2.2 heavy assignment. Follow VM-22–VM-29:
inventory/boundary contracts, exact/finite evidence, pure/observing raw IR,
hierarchy/root closure and production dual integration. Shared-QPE feature work
retains its dependent source/instrument and R14/H1–H5 gates across the continuation.
0.2.9 targets complete Lean implementation and explicitly selected dual checking;
formal Lean-only authority still requires v0.5.0 S05-C1–C5. Preserve current
Rust-only installation/public APIs in PATCH, Mathlib-free acceptance and
small-system validation. The user's later 2026-09-30 instruction authorizes VM-22;
follow its [frozen inventory and comparison baseline](tests/fixtures/verification_v022/README.md).
The user's subsequent 2026-09-30 request resumes the unfinished v0.2.1 feature
track: shared measured QPE, sized source, production hierarchy verification and
execution, and classical-result clients. Complete its independent binding,
instrument/reference and small-system integration gates; VM-22 completion alone
does not complete that goal. The staged VM-23–VM-29 replacement remains distinct.
The original corpus goal is deferred, not completed. Keep those feature gates pending, existing component
proofs audited and external schemas disabled until their binding gates pass.

For the user-selected code-driven continuation from 0.2.0 onward, follow the
[preparation and work packets](docs/code-driven-development.md). Start from
actual desired `.qli` source, preserve first attempts and counterexamples, and
select a bounded implementation slice with a contract and independent checking
experiment before changing acceptance. Complete the finite B019 foundation in
0.1.x; do not mislabel later M1/M2 scaling or sampling work as already complete.
The external translation corpus remains exactly the three sources in
[its policy](corpus/POLICY.md). Local negative fixtures are not a fourth source.

The user's latest v0.2.1 ordering prioritizes corpus implementation: start from
shared executable source and resolve the concrete language/lowering/checking
gaps it exposes. Do not defer corpus source experiments until all general proof
infrastructure is finished. Follow the [sized corpus record](corpus/sized/README.md)
and retain all production authority, preservation and release gates; an
experimental source path is not production CLI integration or a completed goal.
On 2026-09-30 the user limited **remaining validation to small qubit systems**:
do not newly generate or check maximum-size corpus cases. Maximum-size success
is no longer a completion prerequisite for this continuation. Preserve earlier
results and failures as history; do not claim untested capacity. Exact evidence,
phase/reference checks, ownership, compatibility and production integration
remain required. Follow the [revised scope](docs/v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30).

Follow the adopted decisions in these guidelines and the
[version-independent M0–M5 plan](docs/v0x-roadmap.md). In 0.y.z with y > 0,
compatible fixes and features use PATCH; breaking changes use MINOR. An audit
does not itself require a release. Fixed-width M1 may use existing finite
checks. Before generalizing sizes, establish composition of meanings, encodings
and evidence without global dense matrices, together with an evidence-bound
hierarchical IR. General predicates and arithmetic require reversible circuit
synthesis rather than full-space truth tables. The bounded symbolic-kernel
continuation is an M2 design decision, not production integration or blanket
permission to bypass the feature's specification and validation gates.

Evaluate abstractions by which user obligations they remove and which checker
validates their evidence. Mathematical unitarity does not imply access to an
inverse or controlled implementation. A `Clean` name or lifetime is not evidence
of zero return. Preserve existing special-form semantics and compatibility.

## Keep the trusted core small

Follow the fixed architectural partition in [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md).
Do not change that partition during feature work. Keep `std` specifications'
intended mathematical meanings under continuing review; proving implementation
conformance does not establish that the chosen specification is the intended one.

Follow the authoritative [trusted-core principle](docs/design-philosophy.md#keep-the-trusted-core-small):
convenience belongs in untrusted desugaring/adapters, with independent checking
of the result. New checker rules must identify a semantic or evidence obligation
that the existing core cannot express; convenience alone is insufficient.

Treat verifier variants with no frontend producer as signs of compatibility
debt. Update the [producer/debt/reduction inventory](docs/interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary).
Remove public APIs only through a versioned migration. Sharing numerical
execution code or moving files is not a reduction of the trusted acceptance base.

Use the [authoritative definition of desugaring](docs/terminology.md#desugaring-layer):
meaning-preserving translation of convenient syntax/representations to already
specified core operations with explicit ownership and effects. It introduces
no primitive meaning or acceptance rule. Proposed IR/evidence remains untrusted.
Parsing, source checking, approximate synthesis and post-verification execution
adapters are separate responsibilities. Verified output IR alone does not prove
preservation of the original input's meaning.

The [coefficient-domain note](docs/coefficient-domains.md) records future
parameterization and separation of exact and approximate contracts. It changes
neither the current `Z[ζ8,1/2]` implementation nor M2's selected angle profile.
Before adding a domain, specify its arithmetic, equality, complex interpretation,
limits and evidence binding. Arbitrary trait implementations or floating-point
tolerances cannot issue evidence. Keep ideal semantics, approximation error,
device noise and exact auxiliary zero return distinct.

Use the [M1 specification](docs/next-minor-spec.md), [machine interfaces](docs/machine-interface-spec.md)
and [M2 IR/checker profile](docs/hierarchical-ir-spec.md), distinguishing their
specifications from implementation. The [six imaginary-v1 drafts and index](docs/imaginary-v1/README.md)
and [semantic review](docs/imaginary-v1/review.md) satisfy the initial-draft
prerequisite only. Final syntax/APIs, implementation, validation and proof are
separate. Preserve [R14 and the QPE prerequisites](docs/imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
and revise drafts when counterexamples require it.

## Proofs and records

Mark proofs intended for later removal with `temporary (TP-...)` in their Lean
documentation comments, giving the importance (`P0`, `P1` or `P2`), replacement
and removal condition. Importance and lifetime are separate: P0 protects actual
acceptance/binding obligations, P1 preserves reusable mathematics and currently
required components, and P2 covers superseded or projection-only wrappers.
Do not mark a result temporary merely because it is long, conditional, bounded
or low priority. A temporary P1 component can still be required by the current
registry. Prefer the constructed checker path for new work; extend temporary
wrappers only for a concrete compatibility or replacement obligation. Maintain
the [temporary-proof inventory](docs/formal-core.md#temporary-proof-markers).
Keep them built and audited until removal; retain reusable lemmas and respect
public Lean API compatibility rather than treating the marker as permission
to delete declarations or bypass checking.

Follow the [proof priorities](docs/formal-core.md#4-theorem-status-and-proof-work):
independent IR verification and the evidence kernel precede general frontend
adequacy. Keep Lean/Mathlib at 4.30.0 and run `Audit.lean` for proof work.
The user adopted the [staged Lean kernel migration](docs/lean-kernel-migration.md)
from 0.2.0 onward. New production M2 acceptance logic belongs in `lean-kernel/`,
which must remain free of Mathlib and external Lake packages. Keep Rust parsing,
diagnostics, transport, evidence generation and simulation outside that pure
acceptance core. Prove acceptance soundness of the actual executable definitions;
writing code in Lean alone is insufficient. The existing `lean/` Mathlib models
remain separate. Follow the [pipeline migration policy](docs/lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary):
move passes in sequence from the backend or frontend while retaining independent
IR checking at every Rust/Lean boundary. Extend the verified downstream segment
only with actual-transform correctness proofs or independent translation
validation. Remaining Rust transformations still produce untrusted IR. Record
the boundary IR, direction, proof coverage and transitional assumptions; moving
code alone never changes the fixed trust partition. Apply the
[de Bruijn criterion per pass](docs/lean-kernel-migration.md#external-search-and-the-leafrealizer-checker):
move correctness-critical transformations/checkers to Lean, while candidate and
proof search may remain external. In particular, rotation-synthesis norm-equation
search can remain an untrusted oracle; the planned `LeafRealizer` checker belongs
in Lean and must bind the actual circuit/witness to the independent exact or
certified-approximate request. This is a future checking role, not a current API.
No blanket migration of all Rust or proof of the search procedure is required.
A substantive proved Lean backend remains required by v1. Enforce the
[backend execution policy](docs/lean-kernel-migration.md#backend-execution-must-match-kernel-definitions):
forbid `unsafe def`, `@[implemented_by]`, `@[extern]` and `partial def` in
project executable kernel/backend code. CI must check source and compiled
declaration metadata, including private/generated helpers by origin module;
an axiom allowlist alone cannot detect runtime replacement. Any future separate
backend package must inherit these gates before executable integration.
Run the runtime source policy, compiled-declaration audit and
independent native differential checks for kernel changes; reject project
axioms, partial/unsafe code and implementation overrides, including generated
helpers. Do not claim production authority or H1–H5 from the initial phase-word
slice. Production Rust verification remains authoritative until explicit gates
transfer it. The user selected proof of the **Qleisli Soundness Theorem** as
v0.5.0's central milestone; follow [S05-C1–C5](docs/release-milestones.md#qleisli-soundness-theorem-v050).
It concerns the actual production IR checker and its complete declared profile,
not just the phase-word seed or tests. Prepare wider community participation in
0.4.x and expand from individual development into a full-scale open-source
project from v0.5 onward, following the [community roadmap](docs/v0x-roadmap.md#community-development-from-v05).
Keep adopted targets distinct from completed proofs and existing maintainers.
The user added the **Resource Safety Theorem** as the third v1 pillar on
2026-09-30, explicitly **to prove** in the
[dated trust-boundary amendment](TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30).
Follow [RS-C1–C5](docs/release-milestones.md#resource-safety-theorem-v1) and the
[resource-semantics direction](docs/resource-semantics.md): finite static bounds
must cover actual execution and survive lowering/optimization under declared
cost models. Do not confuse quantitative bounds with ownership/R1 safety,
checker budgets or measured diagnostics. Estimators/certificates remain untrusted;
this future target adds no implementation/proof gate to 0.2.1 or 0.2.2.
Development Python scripts require 3.11 or later.
Physlib remains a [future dependency](docs/physlib-environment.md); recheck its
compatibility and external axioms when adding a concrete semantic bridge that
uses it. Library availability is not a proof of Qleisli semantics.

Update current state through `docs/project-status.json` and the manifests;
generate tables with `python3 scripts/check_docs.py --write-status`. Preserve
historical results beside their fixtures. Record new design decisions in their
GitHub Issues; the current release record is a temporary v0.2.x summary.

## Licensing

- The external input corpus is restricted to QuantumKatas, Qualtran Bloqs and
  PennyLane Demos by the adopted [corpus policy](corpus/POLICY.md). Adding or
  replacing a source requires explicit user approval and a policy amendment.
  Pin commits and file hashes; retain source-specific licenses and notices.
  Qleisli remains Apache-2.0, Katas translations are MIT, and the other two
  translations are Apache-2.0. Do not label the collection Apache-2.0 OR MIT.

- Unless individually stated otherwise, Qleisli's code, standard library,
  examples, tests, scripts, Lean proofs and documentation are **Apache-2.0**.
  Maintain [LICENSE](LICENSE), [NOTICE](NOTICE) and [CONTRIBUTING](CONTRIBUTING.md).
- Identify the project copyright holder as **Masahiko G. Yamada**, initially
  `Copyright 2026 Masahiko G. Yamada`. Keep LICENSE/NOTICE/README attribution
  consistent. Do not replace contributor or third-party attribution with it.
- Preserve existing copyright, license and attribution notices. Record the
  source and permission terms of third-party material, check compatibility,
  and retain required notices. Dependencies are not Qleisli-owned work.
- Include appropriate metadata in new public packages; Rust packages use
  `license = "Apache-2.0"`.

## Versioning and releases

[Versioning](docs/versioning.md) is authoritative.

**Track future breaking changes in a GitHub Issue targeting a `0.x.0` release.**
Before implementing a breaking change, create or reuse an Issue and state the
intended `0.x.0` target, affected public contracts, reason for the break,
migration path and acceptance/validation criteria. Keep these changes out of
compatible PATCH work. Reuse existing Issues rather than duplicating them.
**For any work tracked in a GitHub Issue, no backlog entry, backlog update
or backlog ID is required.** This includes breaking changes. Use the Issue
as the tracking record; do not require duplicate backlog records. Filing an
Issue does not adopt the proposed semantics or authorize a release.

The 2026-09-30 user decision names both the first crates.io package and Rust
import `qleisli`, replacing `qleisli-core` / `qleisli_core` at 0.2.1. This is an
explicit, narrow pre-registry identity exception; document the
[migration and Cargo alias](docs/crates-io-release.md#name-migration-from-github-releases-through-020),
preserve historical names in validation records, and retain all other PATCH
compatibility rules. `qargo` / `qlidoc` are possible separate future tool names,
not implemented or reserved packages. The later 2026-09-30 user request lifts
the registry hold and authorizes `cargo publish` outside the sandbox after
rechecking. Keep validation, upload success, tagging and hosted releases distinct.
The verified `v0.2.1` source tag, crates.io package and GitHub Release were
published on 2026-09-30; registry publication followed account email verification. Follow the
[publication record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.1.md#successful-registry-publication-2026-09-30).
The published tag/artifact are immutable; later result-record commits do not
replace their source identity.
The user's later release request authorizes the verified **v0.2.2** tag,
crates.io package and GitHub Release, published on 2026-09-30. Its
[publication record](docs/releases/v0.2.2.md#successful-publication-2026-09-30)
binds the immutable source and artifact to all seven CI jobs, fresh registry
installation, hosted docs and source-archive comparisons. Later result-record
commits do not replace the tagged source; PyPI distribution remains separate.

The user adopted Cargo-compatible 0.y.z versioning on 2026-09-28. Compatible
features need no exception. The user selected development version 0.1.9 on
2026-09-28 for compatible review fixes; follow its [record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.9.md).
Preserve the historical 0.1.8 authoring decision and public Rust AST migration
in the [0.1.8 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.8.md). Type/size
parameters and cross-interface QPE reuse were initially deferred. The user
subsequently adopted shared QPE over `Bits<n>`, then moved its remaining work
from 0.2.0 to the 0.2.1 target on 2026-09-29. Preserve compatibility for that
PATCH; a necessary public break selects 0.3.0. Use `CBits<m>` for
copyable measured bit sequences. The 2026-09-29 user decision adopts
[arity-preserving tuples](docs/tuple-shapes.md): flat and nested products are
distinct and conversions are explicit. Follow the consolidated
[type system](docs/type-system.md). Arbitrary basis-type parameters remain
deferred. Sizes still require R14 and H1–H5.

The user explicitly plans **Qleisli type-system specification in the v0.3.0
breaking-change release** (2026-09-29); follow the
[release plan](docs/v0x-roadmap.md#v030-qleisli-type-system-specification).
Concrete rules and public migrations remain to be specified. Current finite
type rules and compatible 0.2.2 scope stay in force. **QLT implementation is
deferred to v0.4.0 or later**, after that type-system work; preserve its existing
design/source records without treating them as implemented APIs.

Follow the adopted [linear-size and explicit register-reshape design](docs/size-expressions.md):
constant multiplication and guarded subtraction stay within the specified
linear fragment; use `n+1` recursive interfaces and deterministic size
normalization. Arithmetic equality does not erase type trees, reorder axes or
drop owners. Preserve the intact-atom reshape helper's existing contract.
Solver failure is not inequality or evidence; retain full compiled axiom audits
and focused theorem guards. Array notation remains a separately specified future API.

- `Cargo.toml`'s `package.version` is authoritative; synchronize Qleisli's own
  `lean/lakefile.toml`, `lean-kernel/lakefile.toml`, `python/pyproject.toml` and
  Python's `__version__` and `stdlib/Qargo.toml`'s qrate version. Compiler, Python host, bundled library and proofs currently share a
  release. Do not synchronize dependency versions with the project version.
- Use `MAJOR.MINOR.PATCH` and annotated Git tags `vMAJOR.MINOR.PATCH`.
  Accumulate unreleased work in [CHANGELOG](CHANGELOG.md); do not bump per task
  or commit. Align version, changelog and current descriptions when selecting
  a release. Prereleases such as `0.2.0-rc.1` are allowed.
- In 0.y.z with y > 0, PATCH covers compatible fixes, refactoring, documentation,
  features, syntax additions and deprecations without removal. MINOR is for
  breaking changes, resetting PATCH to zero. In 0.0.z, successive PATCH releases
  are incompatible. Document migration and use the largest required increment
  for combined changes; new features still need specifications and validation.
- From 1.0.0, use PATCH for compatible fixes, MINOR for compatible additions and
  deprecations, and MAJOR for breaking changes. Reaching 1.0 requires evidence
  for V1-C1–C5 and explicitly stabilized public contracts.
- Compatibility includes `.qli` syntax/resolution; public Rust, IR and evidence
  APIs; standard APIs; CLI commands, exits and results; and public Lean
  declarations. Phase, bit/axis order, ownership, effects, entry premises and
  auxiliary zero return are public semantics. Enum variants and struct fields
  can also be breaking changes.
- Rejecting an input/evidence that already violated published rules can be a
  PATCH fix. Record the violated rule, before/after behavior, diagnostic and
  regression. A new restriction or changed meaning for previously supported
  inputs, or an incompatible Rust change, cannot use this exception.
  Reduced capacities and raised toolchain requirements need
  compatibility review and at least MINOR in 0.y.z with y > 0.
- Keep specification v0, ledger format v1, development stages and product
  versions separate. Never mechanically renumber historical checks/spec files.
- For release, check changelog, norms, conformance, Rust fmt/all-target tests/
  Clippy, document checks, Lean build/axiom audit, representative examples and
  package license notices. Record performed and skipped checks accurately;
  documentation-only edits do not justify claims of rerun Rust/Lean tests.
- Tag the verified commit containing the actual release changes. Never tag an
  older HEAD while implementation remains uncommitted. Do not mutate published
  tags/artifacts; corrections require a new version. Version selection, tagging,
  push, hosted publication and registry distribution are distinct actions;
  record authorization scope and what actually happened.

## Language and status discipline

- Write production language specifications in **English**, including normative
  grammar, typing/effect/ownership rules, semantics, examples and IR mappings.
  Standard-library public names, contracts, references, comments and example
  explanations must also be English.
- English is authoritative. Supporting Japanese design discussions/translations
  may coexist if their relationship is explicit. Follow the
  [documentation map](docs/documentation-map.md). Preserve dated Japanese
  conformance entries as historical evidence.
- Translate existing Japanese material when preparing it for production use;
  preserve mathematical premises, contracts and proposed/adopted/implemented/
  tested/proved status. These working guidelines are now English too.
- Distinguish proposal, provisional decision, adoption, implementation and
  validation. Parsable source is not executable without checking and lowering.
- Mathematical claims need types, premises and equations or counterexamples.
  Separate resource safety, ideal quantum soundness, protocol/algorithm
  correctness and hardware behavior. Do not claim that typing proves physical
  correctness before the applicable theorem is implemented and proved.
- Human/AI source, evidence proposals and raw IR follow identical verification.
  Author identity and prose are not evidence; never bypass sealed primitives
  or the independent verifier.
- Resolve conflicts between stage-0 decisions and [language v0](docs/language-spec.md)
  in the same change, or record them explicitly as unresolved.

## Quantum invariants

- Arbitrary free-vector-space `bind` is not a safe execution API. Distinguish
  isometries for pure operations from reversible unitary operations.
- `Q<A>` is an ownership type, not a computation-effect type. Composition tracks
  resources, classical values and effects with Kleisli-inspired principles;
  a strict monad structure is not proved.
- Quantum ownership is linear: no unknown-state cloning, aliased wire operands
  or implicit discard. Sharing basis indices does not copy quantum resources.
- Separate owners do not imply product states or absence of entanglement.
  Interpret local operations, measurement and discard globally; pure release
  requires evidence eliminating correlations.
- Keep measurement/reset/discard out of pure operations. Distinguish classical
  `if` from coherent `qif` and retain phase required by controlled operations.
- Initial `measure_z` consumes logical ownership and returns only `CBit`.
  Reusing a physical element does not resurrect that logical owner.
- Pure auxiliary release needs static zero-return/separation evidence for all
  inputs and reference systems. A borrow duration alone is insufficient.
- Diagnose unsupported backend capabilities; never silently change meaning.

## Recording specification changes

Classify each new `.qli` syntax or standard API as a language form, sealed
built-in operation, or ordinary `.qli` definition. For quantum/effectful forms,
record input/output types, ownership, effects, acceptance/rejection examples
and lowering. Specify totality and types of basis functions. Update
[standard-library organization](docs/standard-library.md) for stage 0, and
[language v0](docs/language-spec.md) plus [ROADMAP](ROADMAP.md) for stage 1.
Run relevant checks after Rust changes and record actual results. Semantic
prose alone does not make unimplemented tests pass.
