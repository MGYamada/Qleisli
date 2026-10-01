# VM-22: frozen verification boundaries

Implemented for unreleased 0.2.2 on 2026-09-30. Rust remains the production
authority. These development fixtures add no public format, dependency,
acceptance rule or proof. The original baseline comparisons use at most three qubits.

[inventory.json](inventory.json) freezes 232 public enum constructors (including
all 19 `RawOp` forms), public signatures and capacity constants in 155 reviewed
source snapshots, including VM-23 arithmetic and the VM-24 finite component.
Thirty-six coverage groups give producers, consumers, obligations,
replacement packets and executable positive/negative references. Eighteen boundary
contracts distinguish validity from independent semantic requests and retain
types, ordered ports, effects, phases, source/evidence binding and limits.
Twenty-eight capacity scopes distinguish acceptance, transport and execution,
including module-wide grouped-import prefix and documentation copy budgets.
Capacity references exercise representative successes/failures; frozen constants
and guards retain the remaining endpoints without new maximum-size corpus runs.
Source hashes also cover private guards; changing or adding checking code requires
reviewing the inventory and relevant comparisons. This is a source inventory,
not a Rust parser or a proof of coverage/correctness.

The reviewed continuation adds bounded Rust sized source/CLI preparation,
independent initialization-trace validation, named QPE/provider/instrument
checking and exact finite/H discharge. Execution and fresh-shot sampling stay
outside acceptance, interpreting retained actual definitions and preserving
conditional residual/reference states. Native/decoder/Rust correspondence,
general source preservation and future production replacement remain separate.
Reviewed source/API snapshots and small-system harnesses are updated explicitly;
the original 106-source capture and behavioral fixtures remain historical in
`validation.json`. No comparison artifact is rebaselined.

The user-selected v0.2.3 edition update separately reviews frontend configuration:
every filesystem source tree explicitly declares edition 2026 in `Qargo.toml`.
The new manifest reader is inventoried under source configuration, including its
65,536-byte read limit; it introduces no IR acceptance rule or transfer of
authority. The Python version-only change and Rust documentation/configuration
source hashes are refreshed deliberately. Existing public type/IR declarations,
source capacities, frozen comparison bytes, historical reports and external-disabled
schemas are retained. See [Issue 96](https://github.com/MGYamada/Qleisli/issues/96)
and the [edition contract](../../../docs/language-editions.md).
The [registry review](registry-edition-v023-validation.json) rebuilds/audits both
Lean packages, replays the runtime kernel and exports actual theorem types.
It refreshes only the two package-version source pins; theorem types, domains,
IDs and disabled external entries are unchanged.
The later 0.2.3 corpus extension adds six cases and six semantic faults without
changing this packet's 36-case/12-fault baseline. Its original manifest bytes
are retained in [corpus-manifest.json](corpus-manifest.json) and
[corpus-semantic-faults.json](corpus-semantic-faults.json), with their original
hashes. Current manifests must retain that exact prefix and all original source
pins. Added cases have their own first-source and numerical reports in
[the 0.2.3 session](../../../corpus/authoring/v023-small/session.json).
No behavior or comparison artifact is regenerated.

The [v0.2.5 internal refactoring](../../../docs/releases/v0.2.5.md) reviews eleven
changed private-body/version hashes and adds eight private modules. Shared CLI
execution, frontend flattening state, finite numerical state/circuit execution,
explicit QIRF field maps and native hierarchy response handling retain published
behavior and capacities. Original artifact/request bytes, comparison harness
pins, corpus census and historical reports are unchanged.
The later Lean refactoring refreshes thirty-two kernel source-body pins and adds
eight bounded-capacity/transport modules. Existing public types, legacy rewrite
names, actual result/work behavior and all original comparison bytes remain.
Source/import and compiled-origin policy explicitly cover each transport child;
registry identity includes its complete source. [Universal equality and native
comparisons](../../../docs/releases/v0.2.5.md#lean-kernel-continuation) record the
review without enabling schemas or claiming later migration gates.
The v0.2.2 review repairs explicitly refresh thirteen checking-source snapshots
and two current harness pins, then add eight regression/source pins. Public
declarations and capacities are unchanged except for the additive root
signature/effect preflight method. The new
[review records](../review_v022/README.md) cover capture diagnostics, commuting
QFT candidates, generic/concrete source comparisons and small corpus execution.
Original comparison artifacts, requests, corpus-prefix pins and historical
reports retain their bytes and identities.
The [VM-23 continuation](../verification_v023/README.md) inventories its arithmetic,
reference-data and matrix/capacity proof modules and refreshes the kernel root
and test import hashes. Existing Rust acceptance APIs, capacity constants and
all original comparison bytes remain unchanged. Its separate registry report
rebuilds actual theorem/source identities; no schema or production authority
is enabled.
The [current checkpoint](../authoring_sessions/measured-qpe-v021/checkpoint.md)
separates producer compaction, checker accounting, component proofs and execution.

The coefficient domains remain separate. Finite matrices use exact
`Z[ζ8,1/2]`, with four independent dyadics in ordered basis
`(1, sqrt(2), i, i*sqrt(2))`; entries are row-major, output rows/input columns.
Register field zero is the low bit. Global phase and zero-width owners matter.
The experimental word slice uses modulus 256; the paired T case explicitly
embeds R8 exponent 1 as 32/256. Wider hierarchical dyadic profiles acquire no
implicit finite embedding.

- `finite/`: H, T, Unit scalar, Toffoli, raw-only QuantumIf on Unit and broad
  raw compute/use/uncompute with a target. Each has QIRF1/2 bytes and an
  independently fixed matrix request plus its wrong-global-phase request.
  Rust tests reject aliases, missing Unit owners, changed axes/token/type/domain
  and exhausted work. A separate Python oracle evolves complete complex columns
  and explicitly prepares/uncomputes scratch; it supports only this small slice.
- `source/`: actual emitted artifacts for the six retained simple corpus
  additions and Bell/feedback. The report retains original source paths,
  diagnostics, numerical distributions and ordinary IR decisions. Their
  `request_checked:false` remains explicit; source preservation is unproved.
  Four ownership/effect rejections are replayed. Corpus pins, first attempts,
  notices and the existing 36-case/12-fault report remain intact.
- `native/`: five word artifact/request pairs with independently computed
  decisions, including phase, forged claim, domain and count faults.
- `hierarchy/`: a one-bit H request and phase, zero-repeat leaf and cycle faults.
  The native pass and Rust host freshly check them together; required Rust finite
  premises remain. This conditional path issues no production hierarchy evidence.

[validation.json](validation.json) records performed comparisons and binary
hashes. Full finite/observing Lean replacement is **not implemented**. Parity
in a component slice is not a composed Soundness theorem. Native packaging was
reviewed as explicit source build, audited prebuilt binaries or an optional
bundle; none is selected for production dual checking and Rust-only installation
is preserved.

Run from the repository root with Python 3.11 or later:

```sh
cargo build --bin qleisli
python3 scripts/check_verification_inventory.py
python3 scripts/test_check_verification_inventory.py
python3 scripts/test_test_verification_baseline.py
python3 scripts/test_verification_baseline.py target/debug/qleisli
# Optional, after separately building/auditing the existing kernel:
python3 scripts/test_verification_baseline.py target/debug/qleisli --kernel lean-kernel/.lake/build/bin/qleisli-kernel
```

CI never refreshes snapshots. Explicit capture (`--capture` for source/native/
hierarchy or `QLEISLI_VM22_CAPTURE=<directory>` for the Rust finite test) is a
review operation, not acceptance evidence; review independent requests and
update individual inventory hashes deliberately. Write a new report with
`--report=<path>`; retain historical records. VM-23 starts arithmetic migration
against this baseline under the [staged plan](../../../docs/verification-migration-v0.2.md).

Local harness code is Apache-2.0. Katas-derived SWAP/Fredkin artifacts retain
Copyright (c) Microsoft Corporation and their
[MIT terms](../../../corpus/upstream/quantum_katas/LICENSE); original translations
and notices remain in corpus. These local fixtures add no external corpus source.

The 2026-10-01 bug repairs (#92/#93/#95) deliberately refresh the sized-source
implementation and two Rust regression-harness pins, and add the private
primitive catalog to the same source group. Public APIs and capacities are
unchanged. Comparison request/artifact bytes, original decisions and historical
reports are unchanged; new tests cover scope metadata, primitive omissions and
source diagnostics. The VM-23 scalar proof extension changes proof source only.

The later v0.2.4 repairs (#116–#119) refresh five frontend/source/CLI snapshots
and two sized regression harness pins. Manifest metadata now rejects symlinks
and non-files before opening; Linux retains the descriptor walk with a targeted
procfs capability error. Direct sized bindings obey module visibility, and
`check` rejects the execution-only basis flag. Public Rust shapes, capacities,
frozen artifact/request bytes and earlier reports remain unchanged. Separate
[validation](../issue_fixes_v024/validation.json) records the actual local scope.

The [0.2.3 review packet](../review_v023/README.md) refreshes five current source
body pins for additive phase/identity aliases and the equivalent bundled QFT
source. Public Rust/IR/Lean declarations and capacities are unchanged. Original
36-case/12-fault comparison sources, bytes and reports remain frozen; later
active corpus improvements preserve first attempts in their own sessions.
