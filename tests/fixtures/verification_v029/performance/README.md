# Small-client verification timing

Measured on 2026-10-03 against the uncommitted v0.2.9 migration workspace.
The [raw record](results.json) retains all 640 measured wall times, source and
binary hashes, toolchain versions, artifact hashes and native invocation counts.
All measured commands succeeded. Every emission, including warmups and the
separate invocation-count pass, produced byte-identical IR for its client.

The two routes share the Rust frontend. The selected route additionally requires
Lean and Rust acceptance, including all concrete declarations in loaded modules.
These are CLI latency measurements, not a comparison of language implementations
or a prediction of the future Lean-only authority path. The eight existing
clients use one to four qubits; no new maximum-size case was generated.

## Method

Both builds completed before measurement:

```sh
cargo build --release --locked --offline --bin qleisli
(cd lean-kernel && lake build)
python3 scripts/benchmark_verification.py \
  --record tests/fixtures/verification_v029/performance/results.json
```

Environment: macOS 27.0.1, arm64, 10 reported logical CPUs, Rust 1.98.1,
Lean 4.30.0 Release, Python 3.14.5. CPU model and power state were not collected.
The [harness](../../../../scripts/benchmark_verification.py) runs three
warmups and twenty measured repetitions per client, command and route. It
shuffles client order with a fixed seed and alternates route order within pairs.
All processes run sequentially, with warm OS caches and fresh processes. Builds,
output comparison and the invocation counter are outside the timed intervals.
External machine load is uncontrolled; these results are local observations,
not a CI performance threshold or statistical population estimate.

`emit-ir` includes CLI startup, loading, frontend checks, lowering, verification,
JSON output and a fresh file write with synchronization. `verify-ir` reads the
same already-emitted artifact in both routes, without source compilation or an
independent semantic request. Selected commands add `--lean-kernel=PATH`.
Simulation and algorithm runtime are not measured.

## Source to emitted IR

Times are median milliseconds; brackets give the 25th–75th percentile.
Ratios divide the two medians. The native count comes from a separate shell
wrapper that logs then executes the real checker; its overhead is not timed.

| Client | Rust, ms [IQR] | Rust + Lean, ms [IQR] | Ratio | Native launches |
| --- | ---: | ---: | ---: | ---: |
| Bell measurement | 9.16 [8.63–9.55] | 267.36 [261.98–269.05] | 29.2× | 13 |
| Classical branch | 8.78 [8.43–9.51] | 243.91 [242.69–247.51] | 27.8× | 12 |
| Grover, 2 qubits | 9.13 [8.76–9.67] | 263.28 [262.23–268.81] | 28.8× | 13 |
| QFT, 2 qubits | 8.99 [8.57–9.17] | 268.70 [265.04–274.16] | 29.9× | 13 |
| QPE, 3 phase bits / 4 qubits | 9.53 [9.17–10.00] | 327.59 [322.47–336.04] | 34.4× | 16 |
| Add, 2-bit registers / 4 qubits | 9.43 [8.74–9.64] | 267.14 [262.83–269.94] | 28.3× | 13 |
| QAOA path, 3 qubits | 9.18 [8.91–9.70] | 314.63 [305.68–326.63] | 34.3× | 15 |
| Negative rotations, 1 qubit | 9.26 [8.63–9.44] | 303.19 [300.97–308.46] | 32.7× | 15 |

## Already-emitted IR verification

| Client | Rust median, ms | Rust + Lean median, ms | Ratio |
| --- | ---: | ---: | ---: |
| Bell measurement | 3.09 | 22.49 | 7.3× |
| Classical branch | 3.32 | 22.74 | 6.9× |
| Grover | 3.41 | 22.82 | 6.7× |
| QFT | 3.05 | 22.50 | 7.4× |
| QPE | 3.17 | 22.71 | 7.2× |
| Add | 3.32 | 22.78 | 6.9× |
| QAOA path | 3.18 | 23.34 | 7.3× |
| Negative rotations | 3.26 | 22.65 | 7.0× |

All selected `verify-ir` calls launch the native checker exactly once. In these
small examples, the roughly 19–20 ms added per standalone verification and the
12–16 launches per source compilation are consistent with substantial fixed
per-check overhead. This is an inference, not an isolated CPU profile: native
startup, decoding, validation, serialization, Rust rechecking and transport
are not separately timed.

The current [frontend](../../../../src/frontend/compile/mod.rs) visits every
concrete checked function, including loaded standard-library bodies. The
[emitter](../../../../src/bin/qleisli/artifacts.rs) then checks the emitted
entry again. Each [transport call](../../../../src/interchange/native/runtime.rs)
starts a process and polls completion at 5 ms intervals. Batching independent
function packets and waking directly on completion are plausible optimization
targets; this measurement does not change those paths or relax any checks.

User review on 2026-10-03 accepted this latency as adequate for v0.2.9.
Reducing the 12–16 native launches per compilation is deferred to the v0.3.1
TODO as an enhancement in [Issue #274](https://github.com/MGYamada/Qleisli/issues/274);
it is not a v0.2.9 release blocker.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
