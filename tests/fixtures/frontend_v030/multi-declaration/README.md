# Multiple checked declarations: first study and implementation preparation

The [posted #32 contract](contract.md) defines the next ordinary frontend unit.
This directory preserves its first study, the implementation preparation, and
the candidate implementation's bounded checking observations.

[initial-study](initial-study/) is a byte-for-byte copy of the original
`/private/tmp/qleisli-multidecl-study-fae0` directory: ten projects, seventeen
`.qli` files, ten manifests, the original [session](initial-study/session.json)
and actual [observations](initial-study/observations.json). The baseline is
`fae0e6a149f5b218bcc7f67f38d9509eb8aeb4f3`. Sources were frozen before those
observations according to the retained session. Original absolute paths, argv,
diagnostics and the distinction between source preparation and finite checking
are unchanged. These are informed studies, not a controlled model benchmark.

[preservation.json](preservation.json) hashes all 29 copied files, records their
sizes and verifies every source hash from the original session. Copying and
hashing does not independently authenticate the original process or rerun it.
No historical diagnostic was replaced with an expected future result.

[expectations.md](expectations.md) specifies independent small-program outcomes
and additional bounded cases required by the posted contract.
[interfaces.md](interfaces.md) records the private interface plan written before
implementation, using the existing declaration and lexical identities.

Keep future after-results separate from `initial-study`. Proposal identities
will differ between equivalent split-module and same-module programs; their
independent complex-amplitude expectations are the comparison oracle. Every
actual proposed artifact still needs its existing Lean acceptance check.

## Candidate implementation observations

Implementation started after lexical commit
`0d93a186fbe2e1345542595b75f680f867e1e4e5` (the exact checked-out commit is also
recorded in the validation). The sized projection now retains functions in
source order. Definition lookup uses the common `DefId`'s `ast_index`, imports
are resolved once per module, and every function retains its own lexical table
and undergoes generic checking. No lowerer or Lean acceptance rule changed.

[after/validation.json](after/validation.json) binds the actual replay commands,
input hashes, observer and kernel identities, and all captured outputs. The
compiled observer binary remains at its recorded temporary path and is omitted
from this source fixture; its source and exact build command are retained by
reference. Source/kernel identities were unchanged during the replay.
[comparison.json](comparison.json) reports the ten source outcomes: the first
four intended successes now prepare, all six negative cases still reject, and
all finite observations are unchanged after normalizing only the two absolute
study-root path prefixes. The original outputs remain untouched.

The focused command also passed 37 `sized_source` tests and three
`shared_resolution` tests. Three existing native integration tests were ignored
by this command. The dedicated phase/axis/provider test and single-function
replay are recorded separately in
[the independent fixture](../sized-declarations-independent/README.md).

`replay.py` invokes fixed build/observer/test commands; it does not execute argv
from stored records. Reproduce into a fresh directory with the separately built
kernel selected explicitly:

```sh
python3 tests/fixtures/frontend_v030/multi-declaration/replay.py \
  --kernel /absolute/path/to/qleisli-kernel \
  --output-dir /private/tmp/qleisli-multi-declaration-replay
```
