# 0.2.0 review reproductions

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

These six informed fixtures were written from the user's review in the 0.2.1
working tree, before any check. [First sources](first-sources.json) records
hashes, baseline commit and development version. No source repair was needed.
These are maintenance reproductions, not a controlled model benchmark or an
algorithm proof. They add no external corpus source or downloaded material.

[The initial invocation](invocation-attempt.json) incorrectly passed each
`main.qli` file instead of its source directory. [Baseline](baseline.json)
retains the corrected commands and actual outputs before implementation edits.
[After repair](after.json) replays them against the modified compiler, additionally
checking the emitted artifact and the roundoff case's JSON output. The Lean
`#eval` probe only calls the source scanner; it never executes the IO expression.

| Fixture | Observation before repair | Expected after repair |
| --- | --- | --- |
| [Long trajectory](long_trajectory/main.qli) | Check/run succeed; 6,144 H and T gates fail sample at norm guard. | Three seed-0 samples succeed; same step/RNG limits. |
| [Shared identities](shared_identities/main.qli) | Forty contract pairs check/run, but emit exceeds repeatedly charged source budget. | Emit and independent verify succeed. |
| [Expansion limit](expansion_limit/main.qli) | Shared project work ends inside a helper; diagnostic obscures enclosing declaration. | Still rejects; identifies `main::main` and the inner exhausted charge. |
| [Repeat 300](repeat_300/main.qli), [repeat 1000](repeat_1000/main.qli) | 300 checks; 1000 exhausts exact arithmetic. | Same acceptance; capacity diagnostic explains bounded exact arithmetic. |
| [Roundoff outcome](roundoff_outcome/main.qli) | Ideal-zero result has computed weight about `6.16e-33`. | Same text/JSON contract, now prominently documented. |

[Integration tests](../../review_v020.rs) add long flat/compound identity
circuits, unchanged execution/draw budgets, QIRF1/2 round trips with 300,000
extra source bytes and CLI usage. Internal tests check norm corruption,
source-sharing identity/order/duplicates and real byte limits. Runtime policy
regressions reject both eval commands without rejecting comments/plain literals.
The response lists all nine dispositions;
[validation](validation.json) records commands actually run for this checkpoint.
