# First word-coordinate Grover predicate

This three-bit first source marks the ordered label `(1,0,1)`. Its protected
scope should apply -1 to just that label and preserve the complete data owner.
The proposed `word[k]` spelling is a statically checked ordinary coordinate
read. It is still a language design probe.

The actual `check` invocation used selected Raw mode with `--entry=main::oracle`,
`--module=main=/private/tmp/qleisli-30-bits-first.mCof1a/first.qli`,
`--ir-profile=raw`, `--format=json` and an explicit Lean kernel. The saved
`parse-stdout.json` is unchanged. The command exited 1 with empty stderr at the
first `[`. An earlier invocation without the manifest returned a project
error; copying the recorded manifest left the first source unchanged.

CLI SHA-256 `79eedf4ed421ea9126e6faa349fb22e13a1b07cd4e95c1928fe7be54087c71a0`.
Kernel SHA-256 `1f901c07e6ec679f2adb851e8615b5307ecaa992a6925ae43ce2b2846ed048bc`.

The Lean component checks a normalized word-coordinate expression directly.
These observations do not show that the parser or runtime accepts the spelling.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
