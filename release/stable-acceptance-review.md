# Qleisli 0.3.0 acceptance review packet

Maintainer review is pending. The two stable indices refer to the candidate
sources and to the separate proposed requirements base. The hosted pre-tag
workflow must produce fresh full proof, native, distribution, clean-install
and companion receipts from the final `main` commit in one run and attempt.

## Frozen audit and current evidence

- The [approved beta requirements](https://github.com/MGYamada/Qleisli/pull/643#issuecomment-7030282663)
  come from `5b75e6431ba9261cde1233f7de6fd759e648f3fb`. Their SHA-256 is
  `00f95429a72489e3bdd2b41f20dc7859d53d25ece050496eae16119db419c53b`.
  The [published beta tree](https://github.com/MGYamada/Qleisli/tree/v0.3.0-beta)
  at `ce71d151427af30f9fffe8d967524b905265701f` supplies the bytes for all
  224 historical evidence and review paths. Its recorded product and native
  reply identities remain `0.3.0-beta` and `qleisli.native-result 3`.
- The [proposed stable requirements commit](https://github.com/MGYamada/Qleisli/commit/d0d73c48f6efe10d68a95387e9d22ad78dc62524)
  contains the same frozen audit and adds six stable criteria. The supplement
  SHA-256 is `beb43240bf8f1d254e1feec956bce739d9500955f27ec9ea803144ebfc20c781`.
  The supplement pins qlirgo `b4010e93d14c27b755b3c72e6f02ec78fae4436c`.
- The [stable baseline acceptance index](stable-baseline-acceptance.json)
  carries all 1,082 criteria across 127 Issues, with 1,066 implemented criteria
  and the original 16 `explicit-later-version` dispositions. Issues #39 and
  #63 retain their approved exclusions. The baseline preserves the historical
  review reference for unaffected rows. Rows whose evidence changes point here
  for the release delta. The original index, snapshots and beta review record
  remain the historical evidence for each frozen criterion.

### Evidence differences to review

The [candidate comparison](https://github.com/MGYamada/Qleisli/compare/ce71d151427af30f9fffe8d967524b905265701f...5373fd311c35ea29875fa37e5f33cee0a9119827)
contains 62 changed historical evidence paths affecting 932 criteria. All
62 paths still exist. The stable baseline preserves the original role and
path for each of these references and records the current digest. The
candidate also replaces nine beta-only proof references and ten beta-only
companion references with this review and the current source and suite
results. Together these updates affect 935 criterion rows.

| Evidence roles | What to review |
| --- | --- |
| Language Reference and examples | The [Reference rewrite](https://github.com/MGYamada/Qleisli/commit/6f6b0580) and [follow-up review changes](https://github.com/MGYamada/Qleisli/commit/ae2545b4) reorganize the contracts. Inspect the current type, source and operation contracts for the original ownership, effects, tuple shape, finite phase and axis ordering rules. Check manifest changes against the [package contract](../docs/src/reference/packages-and-artifacts.md) and the edition tests. |
| Rust, Python and diagnostics | Match the parser and CLI changes to the original source-error and capability cases; retain source spans and the distinction between parsing, native checks and execution. Inspect the [verification trace](../docs/src/reference/production-boundary.md#stable-verification-request-migration), [CLI tests](../tests/cli.rs), [JSON diagnostics](../tests/cli_json.rs), and [Python regression](../scripts/test_python_host.py). |
| CI and production inventories | The [workflow](../.github/workflows/ci.yml), [coverage gate](../scripts/check_production_coverage.py) and compressed coverage inventory retain the individual proof, runtime and test scopes. Review old wire fixtures with the compatibility rules of the [single stable entry](../lean-kernel/Main.lean). The [package job](https://github.com/MGYamada/Qleisli/actions/runs/45007847277/artifacts/14749832736) verified the earlier candidate crate, complete source archive and clean installation. |
| Proof scope in #129, #135, #141 and #142 | Follow the [current production inventory](../docs/src/reference/production-boundary.md), [Lean evidence](../governance/guarantees/current-evidence.json) and [disclosures](../governance/guarantees.json). The two admitted guarantees cover the original decoded QLV1 root's ownership and classical scope with their recorded premises. QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 remain pending. Bounded native comparisons, engineering results and placement results retain their individual scopes. General source and target preservation remain pending. The [beta proof report](beta-proof-scope.md) retains the historical proof audit. |
| Companion scope in #171, #230 and #231 | Check the selected std and stable build identities against the pinned source comparison below. The [distribution contract](../docs/src/reference/packages-and-artifacts.md) gives the atomic install, update and rollback requirements for each supported train. The [beta companion report](beta-companion-evidence.md) retains the separate historical pairing. |

## Stable supplement

| Criterion | Candidate evidence to review |
| --- | --- |
| `349-manifest-selection` | The [edition loader](../src/frontend/project/edition.rs) and [integration tests](../tests/editions.rs) exercise canonical and legacy names, nearest-root and explicit `--qrate` selection, byte-identical and differing pairs, malformed files, and missing edition. The release coordinates are compiler and std `0.3.0`, edition `2026` and qrate manifest schema `2`. |
| `349-version-sync-packaging` | [Version synchronization](../scripts/maintain_release.py) covers Cargo, Lean, Python and std. The version plan for `5373fd31` has no pending source review or version edits. The [candidate distribution report](https://github.com/MGYamada/Qleisli/actions/runs/45007847277/artifacts/14751149285) verifies package metadata, bundled std, clean install and Bell `check`, `run` and `sample`. |
| `349-companion-candidate` | The pinned [qlirgo 0.2.0 candidate](https://github.com/MGYamada/qlirgo/tree/b4010e93d14c27b755b3c72e6f02ec78fae4436c) declares `qleisli = "=0.3.0"`. The [companion qualification](../scripts/qualify_stable_companion.py) selects the exact Qleisli crate, checks the effective linked version and std, and exercises all four tools and the six manifest cases. See the candidate pairing below. |
| `622-request-and-admission` | Review [VerificationRequest v1](../lean-kernel/Protocol/VerificationRequest.lean), [native routing](../lean-kernel/Cli/NativeContext.lean) and the [execution view contract](../docs/src/reference/execution-view.md). The reply protocol is `qleisli.native-result 4`. Admission binds the current reply to the request, exact artifact and scope. |
| `622-compatibility-migration` | The [21-obligation map](../docs/src/reference/production-boundary.md#stable-verification-request-migration) locates the current selector for each former flag, with v2/v4/v5 inner obligations retained. The [native regressions](../scripts/test_native_execution_protocol.py) cover actual retained ordinary, contract, caller and source cases, including work limits and view mutations. Local ARM64 replay gave 215 matching results against the offline legacy dispatcher. The [hosted native result](https://github.com/MGYamada/Qleisli/actions/runs/45007847277/artifacts/14751241982) reports 73 manifest tasks passed. Its `native-paths` run skipped optional PyQIR, which the separate relocated-bundle check ran with all 12 interop tests passing. |
| `622-cli-outcomes` | The [common source command engine](../src/bin/qleisli/source_commands.rs) selects source and constructs the disposition for text and JSON. Inspect [CLI JSON outcomes](../tests/cli_json.rs) and [selected-source regressions](../tests/selected_source_cli.rs) for scope, diagnostic identity, unavailable native checking, and the limits of inspection. |

### Candidate pairing and release order

Qleisli 0.3.0 precedes qlirgo, qlinties, qlifmt and qlidoc 0.2.0. The
local macOS ARM64 source comparison used Rust 1.85.0, Lean 4.30.0, the
`5373fd311c35ea29875fa37e5f33cee0a9119827` crate from Actions run
`45007847277` attempt `1`, and the exact pinned qlirgo tree exported with
`git archive`. Cargo metadata identified one `qleisli` 0.3.0 package at the
unpacked crate path. The unchanged companion verifier passed for four tools
and three qrates. All six manifest selection cases passed. The build artifact
mutation regression returned `artifact_mismatch` and preserved the bytes.

| Local comparison input | SHA-256 |
| --- | --- |
| Qleisli `.crate` | `5c5bd01757f8b9f7dc72b4ffd1d72afb96a2c311e9ffa907f8dfde7edaa3c36e` |
| Bundled std manifest | `35abd8eb5c93055135ad1c6ebf56dac984a059e5df0c3a924226670c1879e3a9` |
| Locally built macOS ARM64 checker | `0fcb56ae4470941333bc6bb1b43579a1b48172771e3f60e1a4e51c6ef50b3cf1` |

The pre-tag job links the unpacked candidate crate into a disposable checkout.
On Linux x86_64 and macOS ARM64 the job selects the native bundles from its
own validation run. Intel macOS builds and fully replays the pinned Lean
sources. The stable release gate checks the same-run three-host receipt.
After Qleisli publication, the companion release verifies and locks the exact
crates.io package before its separate release. See the
[companion release procedure](https://github.com/MGYamada/qlirgo/blob/b4010e93d14c27b755b3c72e6f02ec78fae4436c/docs/releasing.md).

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
