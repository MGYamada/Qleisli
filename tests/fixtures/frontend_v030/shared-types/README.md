# Shared internal type migration

This is an informed implementation study and bounded regression record for
Issue #27, starting from commit `44e23e4`. It is not a blind authoring benchmark,
new source syntax, a Basis-polymorphism implementation or a proof of source
preservation. The original 22-case investigation is preserved byte-for-byte in
`initial-study/`; its original absolute paths describe where it actually ran.
`session.json` inventories those unchanged files and the four additional small
proposal sources recorded before their first replay.

The common internal `Type<N>` retains Unit, Bit, Bits, immediate tuple arity,
ordered nesting and an explicit Q owner constructor. The size representation is
an implementation parameter: uninhabited for the finite profile, existing
symbolic Linear for sized preparation, and u32 for concrete elaboration.
Source evaluation stage remains separate. Current `CBit` and `CBits` map to
ordinary internal Bit and Bits; the old sized internal quantum Bit and Bits map
to Q of those ordinary trees. Source profile restrictions remain unchanged.

Finite type/value capacity charges retain their existing node/depth meaning.
Sized value-cell accounting counts an owner as one cell, as before; the added
internal Q constructor does not lower the accepted limits. Accounting does not
identify types or remove zero-width owners. Existing finite two-field products
map explicitly to contract Pair, while larger products remain Tuple.

The public `SourceType` name now aliases the privately constructed shared
concrete type. Its `kind`, `width`, `fields`, `is_quantum` and exact equality
observations retain the current profile's meaning. **Rust Debug output changes**
from the old `SourceType { kind: ... }` representation to the explicit common
`Type { kind: ... }` tree including Q. This is an observable debugging-format
change, separate from accessor compatibility. CLI diagnostics use explicit
legacy source-display adapters and remain unchanged in the recorded comparison.

## Reproduction

The driver constructs fixed command arguments itself; it does not execute
commands loaded from result JSON. Select an existing matching native checker:

```sh
python3 tests/fixtures/frontend_v030/shared-types/replay.py \
  --tree /absolute/path/to/checkout \
  --kernel /absolute/path/to/qleisli-kernel \
  --output-dir /private/tmp/qleisli-shared-types-replay
```

`baseline-build.json` records the actual git archive and offline build of
`44e23e4`; `before/commands.json` and `after/commands.json` retain actual argv,
exit codes and stream file references. Output directories in those records are
the original scratch locations; stream names also resolve beside each retained
commands file. Observer executables are reproducibly built and not committed.

The observer's `finite:` label means common syntax parsing only. Its `sized:`
label includes sized profile and generic preparation. Twelve separate `check`
commands actually invoke the explicitly selected native checker where frontend
checking succeeds. Three accept and nine reject in both versions. This is not
22 native acceptance checks.

`compare.py --before DIR --after DIR --output FILE` independently compares the
actual retained streams and proposal files; it fails on a difference or missing
comparison case.

`comparison.json` records all **34/34 exit/stdout/stderr observations identical**
and **8/8 successful untrusted proposal byte comparisons identical**. The four
shared-parser sources are reused unchanged from the adjacent common-parser
fixture. The additional sources cover H, ordered owner pairs, a two-bit register
split/join and one-bit observation/readout. At most two quantum wires are used.
`emit-proposal` alone does not invoke native acceptance or prove preservation.

## Validation and review

Actual validation argv and streams are retained in the matching JSON/stdout/
stderr files. The focused integration selection has **191 passed, 8 ignored**
across 20 targets. Four shared-type unit tests and eight finite compiler/scope/
phase-axis unit tests also pass: **203 passed in total**. The ignored tests retain
their pre-existing explicit native-checker or Python-oracle lane requirements;
their exact reasons are in `integration.stdout`. No `--ignored` run is claimed.

The independent read-only review checked the common mapping, finite stage and
zero-owner paths, branch phi, symbolic-size comparison, legacy diagnostics and
public accessor view. It independently compared the retained streams and
proposal files and reported no unresolved concrete finding. It did not rerun
the integration suite. This review and the tests do not discharge a constitutional
guarantee or close general source-preservation obligations.

Final formatting, documentation and compile-only checks are recorded separately.
This task does not claim a full Rust test run, complete corpus replay or Lean
rebuild. It does not generate or check new maximum-size quantum cases.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
