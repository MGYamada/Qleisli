# Canonical-type Python client integration repair

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The canonical ordinary-type cutover intentionally rejects historical `CBit`
source. Hosted run `37217706111`, head `cc11429`, exposed active callers that
still selected those original files. The interop job `111481619958` failed at
`qli-to-qasm` and `qli-to-qir`. The macOS job `111481619947` later reached
`test_source_kernel.py` after its kernel build/audits, fresh replay and native
verification, then failed nine subcases across four tests on `project` and
`generic`. These job facts came from the coordinating task's captured logs;
[the hosted integration record](../../review_v030alpha/hosted-canonical-integration/README.md)
retains the external failure evidence. This fixture does not claim that either
complete hosted job has subsequently passed.

The repair changes nine active Python callers. The independent OpenQASM and
LLVM inputs remain in their original locations. Terminal QLI uses its existing
[explicit current derivative](../ordinary-type-cutover/current/interop/terminal/main.qli).
The other twelve projects have explicit current inputs under `current/` here:
verification-v029 project/generic, phase-layout interference, three interference
clients, two QFT clients, two QPE clients and two coherent-phase clients. Only
whole `CBit` tokens were changed to `Bit`; other source bytes and existing
manifests are retained. There is no runtime source rewrite or legacy alias.

[source-map.json](source-map.json) records both paths and both SHA-256 identities
for all thirteen projects and nineteen files. The shared
[current-source selector](../../../../scripts/current_source_fixtures.py)
checks both complete sets of `.qli` and `Qargo.toml` files before returning a
current project. Existing baseline-hash checks still inspect the historical
files; numerical and format oracles are unchanged. Execution records in the
source-only clients distinguish current hashes from historical hashes.
Historical fixtures and their original baseline records were not edited.

The audit covered active `scripts/*.py` source constants, fixture selectors and
CI commands. Five additional source-only lanes needed current selection:
phase-layout, interference, QFT, QPE and controlled-power. The direct CI layout,
layout-DAG and phase-layout first sources already use supported syntax and all
three passed unchanged. The hierarchy first source is only hashed by its
current Python test; it is not submitted to the source compiler there. Other
historical QIRF, Lean, protocol and authoring records remain historical inputs.

[run-selected.py](run-selected.py), [commands.json](commands.json) and
[validation.json](validation.json) retain the actual selected replay. It reused
the already-built canonical-cutover CLI and native checker: no Cargo/Lean
build, new checkout, tool install or maximum-size case was run. The independent
CLI build snapshot is identified in the validation record; current source
hashes are recorded separately. Subsequent formatting/documentation deltas do
not make this a fresh build of the present checkout.

The selected checks passed:

- Five source-only mathematical-oracle commands, including the wrong-order and
  wrong-reversal programs whose distributions must differ from the desired
  reference. Their type-correct semantic faults are preserved.
- All four source/native tests, including unused-body rejection and missing
  checker refusal; all three unchanged direct CI source checks.
- Historical terminal exports still reject, while the current terminal passes
  native checking and both exports.
- The existing `check_qasm` and `check_qir` oracles validate main-CLI output with
  OpenQASM 3's parser and LLVM `llvm-as`/`opt`. This is the shared exporter path,
  **not** a replay of the absent current `examples/interop` executable or the
  entire external target-coefficient suite.
- One Python project/raw-IR reverification test and two selected native interop
  tests across formats/actions and Python program methods.
- Six [selector identity regressions](../../../../scripts/test_current_source_fixtures.py)
  reject stale original/derivative bytes, extra or missing source/manifests,
  and missing or duplicate project mappings. The final licensed test run is in
  [test-final.json](test-final.json); root wired this test into ordinary CI.

The selected replay's bound inputs were identical before and after execution.
[additional-commands.json](additional-commands.json) records the three direct
CI checks and initial identity-test run. No format oracle, source/native
acceptance condition, historical baseline hash or library implementation was
weakened to obtain these results. Full hosted/external-suite results remain
separate follow-up evidence.
