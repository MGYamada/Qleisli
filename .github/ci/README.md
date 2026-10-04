# CI scheduling and evidence

`profiles.json` selects docs-only versus executable validation conservatively.
Executable, proof, normative and unknown changes still run every selected suite.
`ci_profiles.py` separately selects proof maintenance without treating tests as
proof evidence. Required contexts aggregate all selected suites against the
exact checkout; missing/unknown lanes and failed/skipped selected jobs reject.
Dependency archive misses take the same validation path. Cargo `target`, Lean
project outputs and prior validation reports are never cached.

Constitution, governance records, constitutional fixtures and Reference changes
select the full policy-risk lane. The always-run documentation job also checks
the adopted constitutional identity, historical candidate evidence, pending
ledger, separately adopted initial interpretations and scoped admissions. PR/push checks compare
the available event base; tags reject incomplete proof enforcement as
release-unready. This is the first identity-enforcement
component of #141, not complete interpretation/proof/artifact enforcement.
Human decisions and changes to enforcement code or workflows still need review.

The v4 ledger separates append-only admitted identities from current evidence
bindings. Explicit code registrations bind reviewed human events and exact
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

The current manifest contains 67 groups and 79 commands. Preparation/readout
transport tests require the exact product version, exercise both dynamic modes,
and distinguish version rejection from malformed or semantically invalid frames.

The native-paths group exercises the single Lean acceptance boundary through
source, raw, QIRF, foreign and Python entry points. Environment selection and
explicit kernel arguments use the same implementation; missing and incompatible
checkers cannot fall back. Runtime Rust/MSRV/installation jobs first build and
audit the matching kernel, then set an absolute `QLEISLI_KERNEL` path.

The native-acceptance group exercises immutable accepted handles and replays all
799 retained original Rust/Lean decision pairs. Those input bytes and baseline
results are immutable. It also requires the accepted-artifact round-trip suite,
including receipt-path coverage, as a distinct command. The obsolete two-verifier generator has been removed;
current Rust adapters are not described as an independent semantic verifier.
Transport failures never count as matched semantic rejection. Existing pure
component proofs, independent semantic oracles and audit jobs remain required.
