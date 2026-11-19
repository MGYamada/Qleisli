# First authoring across the four surface roles

Two independent authors received the same five tasks, README, STDLIB and the
English Reference at [`1751b32f`](https://github.com/MGYamada/Qleisli/commit/1751b32f0bde9a716a245ed7797dee2c1fa07d6f).
Each produced five modules, one deliberately invalid alternative and notes
before any compiler feedback. The [archive](first.tar.xz) and
[inventory](first-index.json) retain the task, input hashes, original sources,
notes, observer clients, commands, exit codes and complete output streams.

| Task | First choice of both authors | Observation on unchanged sources |
| --- | --- | --- |
| Coherent conditional H | `qif` with an identity block and an H arm | Selected Raw accepted. Closed clients checked both selector values and interference after two applications. |
| Flip and control in place | `excl` and `ctrl`, followed by two measurements | Both binding names remained usable. Both closed programs returned `(1, 1)` with probability one. |
| Move a qubit | Ordinary `let`, a consuming H call and its returned owner | Both moves passed. Both attempted uses of a consumed binding failed with `ownership`. |
| Repeat H with a quantum carry | `qfor static` with an ordinary `const n: Nat` bound | Selected Raw accepted at n = 2. Closed clients checked n = 0, 1 and 2. |
| Select ordinary bit alternatives | Ordinary `if` | Both open entries received `unsupported` from selected Raw for the runtime expression. Each unchanged declaration passed all eight closed project truth-table cases. |

All 32 closed project executions agreed with the expected distributions within
`2.3e-16`. The 12 selected checks yielded eight acceptances, two ownership
refusals and two profile refusals. The subjects identified when to measure a
qubit for an ordinary condition and when to preserve coherent selection.
The study covers these first attempts. It establishes neither a population
success rate nor general source preservation. The native checker identity is
recorded separately from the observed Rust CLI.
