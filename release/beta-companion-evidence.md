# Beta companion verification

The evidence covers the edition declaration and canonical std pairing in
[#171](https://github.com/MGYamada/Qleisli/issues/171#issuecomment-7030015660)
and [#255](https://github.com/MGYamada/Qleisli/issues/255#issuecomment-7030016027).
The four binaries built from qlirgo
[`4a194a6`](https://github.com/MGYamada/qlirgo/tree/4a194a616cf0a1ca2703e9481f677bb89caff4d3)
used the explicitly selected, checked Qleisli beta package. The companion
dependency declaration pins `=0.3.0-beta`.

| Input or check | Exact record |
| --- | --- |
| Local Qleisli package | Commit `6068d19175560a4c3b59f7c577e1dc3593a6d8a0`, SHA-256 `2b152af47ab3058e9374a2622051ef91dc79800a30156016f700c7189849b058` |
| Identical engine and std sources in the hosted package | Commit `63894774ed8fe6869b9412767adb3cbed5de2a22`, SHA-256 `ec5f8a43dc1653a642f54e7fd9879d5f8f943c9b987715a1fcd9d2a11beaea71`. Of 13,917 paths, only the Cargo revision record and three documentation files differ. |
| Fresh install | Package inspection and Bell check, run and sample in text and JSON, embedded qft2, and refusal of measured-owner reuse. [Hosted result](https://github.com/MGYamada/Qleisli/actions/runs/44647898177) |
| Local versions | On macOS ARM64, Rust 1.99.1 and 1.85.0 each passed 25 bundle/qargo cases and 20 linter engine cases. The MSRV std-identity unit test and stable all-target Clippy passed. |
| Four tools | The candidate `bin/` contains qargo, qlippy, qlifmt and qlidoc from the checked build. The companion verifier exercised all four binaries and all three qrates against the explicit Qleisli source and audited native checker. [Companion review](https://github.com/MGYamada/qlirgo/pull/41) |
| Exact selection and stale records | The real qargo build selected std 0.3.0-beta. Exact reuse and restored records succeeded. An altered std version and manifest digest each rejected with `artifact_mismatch` and kept the existing bytes. Independent std selection received a refusal with guidance to select the matching toolchain. |
| Explicit edition | Missing, floating and unsupported editions rejected. Explicit 2026 accepted with the original source configuration. Native packet regressions bind the checked edition, product, protocol mode and scope. |

The official companion registry guard rejects local overrides. Official
crates.io registration, the resulting official registry lock and supported-host
distribution checks follow the beta goal. The latest registry CI fails during
the unpublished dependency fetch. [Registry CI](https://github.com/MGYamada/qlirgo/actions/runs/44647863961)

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
