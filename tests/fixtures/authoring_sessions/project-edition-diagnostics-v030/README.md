# Project edition diagnostic observations

[The archived observations](observations.tar.xz) retain six first source
trees and the paired outputs of `qleisli check <source-tree> --format=json`.
The first executable came from the beta comparison in PR #639. The repair
was tested against the same native executable and the same saved source
bytes. Each run records both executable digests, standard output, standard
error and the exit code. These are inert observations.

| First source trees | Observed result on both builds |
| --- | --- |
| Missing manifest, missing edition, numeric edition, floating edition and unsupported edition | Exit 1 and a located `project` diagnostic |
| Supported explicit edition | Exit 0 and complete reported native decisions |

The comparison found the same JSON values, exit codes and stderr after
excluding the five diagnostic message strings. The repair explains the
constitutional regime in those messages. The Rust integration test also
changes the manifest explicitly and checks the same source again through
the native path.

The archive SHA-256 is `7ca5e4864b9b881c0b555e94b872b6a6548e045084ca00a3ef55445f169fb36b`.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
