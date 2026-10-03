# VM-28: opt-in ordinary QIRF dual checking

`qleisli check`, `run`, `sample`, `emit-ir` and `verify-ir` accept
`--lean-kernel=PATH`. The additive library entry is
`interchange::dual::Kernel::check`. Defaults and existing Rust APIs retain their
published behavior; the selected mode requires **both** independent decisions.
There is no fallback when the native checker is absent, rejects, exhausts a
capacity, crashes, times out or returns an inconsistent response.

```sh
python3 scripts/package_lean_kernel.py --output /tmp/qleisli-native
cargo build --locked --bin qleisli
target/debug/qleisli run tests/fixtures/authoring_sessions/dual-v028/attempt-02 --lean-kernel=/tmp/qleisli-native/bin/qleisli-kernel
python3 scripts/test_dual_verification.py --kernel /tmp/qleisli-native/bin/qleisli-kernel
```

The bundle command requires the pinned Lean 4.30.0 toolchain. It copies source
into a fresh directory, builds without project outputs or external Lake
dependencies, runs source/compiled declaration audits and fresh kernel replay,
then copies the native binary with Qleisli and Lean runtime licenses. Its
manifest records exact source/binary identities and performed commands. The
relocated binary is tested with correct and wrong-global-phase requests; CI
also runs the complete selected CLI harness on Linux and macOS. No bundle is
downloaded automatically. The explicitly selected executable, native compiler,
OS and process transport remain correspondence assumptions, not attested proofs.

## Exact input and execution binding

The host copies the complete artifact/request into immutable owned bytes. The
Rust importer and a fresh Lean process receive these same inputs. Source
commands compile once, export QIRF2 and use the imported program from this dual
check for execution/sampling. Emission writes the retained accepted bytes with
the existing no-overwrite installation. Source files and request files are not
reread after acceptance. The report has no public constructor or serialized
receipt input; changing later caller buffers cannot change its accepted body.

Private stdin framing is `QLV1`, two little-endian u32 byte lengths, original
QIRF1/2 bytes and optional original `qleisli.request` v1 bytes. Zero request
length means absent. Each file is at most 16 MiB; exact EOF is required. The
reply is `qleisli.qirf-dual 1`, `accepted`, exact-work count and a 0/1 request
coverage flag, each followed by LF. Failures use `error` and a closed error
code. The host caps replies at 256 bytes and waits at most 60 seconds, including
pipe completion; malformed/trailing output, status conflicts and request-flag
disagreement reject. The executable path is resolved explicitly without PATH
discovery. A reply alone never bypasses Rust reconstruction.

## Lean checking and proof scope

[Validity](../../../lean-kernel/QleisliKernel/Qirf/Validity.lean) invokes the
existing original-index QIRF graph reconstruction, freshly verifies the original
root and checks optional complete root type trees. Every dependency and both
classical arms are inspected. Unused source entries reject. Ordinary validity
requires no caller equation and retains twelve-bit structural owners; explicit
finite equations retain the existing six-bit domain and exact work allowance.
Requests bind the full type tree, optional exact source snapshot and a freshly
reconstructed mathematical permutation/phase table. Global phase matters.

`inspect_checked` proves actual success entails fresh graph/root checking and
retained interface checking; `requested_equation` proves actual request success
equates freshly reconstructed matrices on the whole space. They compose with
the existing VM25–27 component results without a Rust acceptance premise. This
does not prove universal JSON decoding, native compilation, source preservation,
Rust simulation or full S05. No external schema is enabled.

## Validation and remaining coverage

[Native/CLI observations](dual-validation.json) cover both QIRF versions, raw-only
forms, Unit owners, protected cleanup, measurement/branch execution, independent
phase/type/snapshot faults, invalid unselected arms and strict packet framing.
Seventy-five existing corpus clients use at most four qubits; three five-qubit
clients are deliberately omitted. Numerical equality with Rust is differential
test evidence; the separate corpus report retains mathematical oracle checks.
Rust transport tests cover malformed replies, false exit/acceptance combinations,
overflowing output, deadlines, inherited pipes and immutable library binding.
The [authoring session](../authoring_sessions/dual-v028/session.json) preserves
the initial manifest/unsupported-option failures and repaired manifest.

[Coverage](coverage.json) identifies remaining paths: ordinary Rust embedding,
interop/Python adapters, and experimental hierarchical/sized APIs are not
silently rerouted by this option. Hierarchy VM27 analytic closure, VM29 full
coverage/reproducibility and S05 authority transfer remain open. This is the
selected finite VM28 integration slice, not completion of all migration gates.

[Validation](validation.json) records exact sources, local checks and pending
hosted/platform coverage. The [native bundle manifest](native-bundle-manifest.json)
retains the clean build/audit/replay and relocated runtime checks.
[Source review](source-review.json) records additive source/API inventory changes.
Original VM22 comparison artifacts and historical usage fixtures remain unchanged;
the new [usage fixture](usage.txt) covers the additional option. The retained
[pre-fix audit](schema-before-transport-fix.json) caught a compiler-generated
partial IO helper; the final bounded range loop passes the same unchanged audit.
[Registry validation](schema-registry-validation.json) rebuilds and binds the
actual current sources without enabling schemas.

Three raw Rust logs are stored as lossless gzip to preserve their exact output
whitespace. [Storage identities](log-storage.json) map the original log names
in `validation.json` to stored paths and bind both raw and compressed hashes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
