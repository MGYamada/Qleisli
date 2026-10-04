# Qleisli

Write quantum algorithms in the language you use to think about them.

Qleisli is an **experimental quantum programming language** with linear quantum
ownership, explicit measurement effects and exact finite semantic contracts.
The Rust frontend produces IR that an independent native Lean verifier checks before
reference execution. Human-written and AI-generated programs use the same checks.

Package: **`qleisli`** · executable: **`qleisli`** · Rust library: **`qleisli`**.
Package version: **0.3.0-alpha** (prerelease preparation; unpublished). The approved
[breaking verifier migration](https://github.com/MGYamada/Qleisli/issues/276)
removes the Rust verifier and dual acceptance API. Verification requires a
matching separately installed native Lean checker; Cargo builds and docs remain
independent of Lean. Select it with `QLEISLI_KERNEL` or `--lean-kernel=PATH`.
Missing, incompatible or failing checkers reject without a fallback or download.
Changes are recorded in
[CHANGELOG](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/CHANGELOG.md).
**Qleisli language edition: `"2026"` for all current
`.qli` and `.qlt` files.** Each source tree requires an explicit `Qargo.toml`.
The bounded implementation and pending proof/migration goals are distinguished below.
Rust 1.85 or later is required. Cargo builds the implementation and its TOML reader;
the native checker needs no Lean development environment at runtime. Python and LLVM are optional host adapters.
On macOS 11+, source loading uses `O_NOFOLLOW_ANY`, requiring only search
permission on ancestor directories. Older macOS keeps the descriptor-relative
`openat`/`O_NOFOLLOW` fallback and requires read permission on those directories.
The runtime version is checked before using the newer flag; Rust's existing
deployment targets remain supported.
Filesystem source loading on Linux x86/x86_64, ARM/aarch64 and RISC-V requires
accessible procfs directory descriptors at `/proc/self/fd`. A missing or
inaccessible descriptor path produces a targeted runtime diagnostic. Ancestors
use `O_PATH` directory descriptors and require only search permission.

## Install and run

Install from a source checkout with
`cargo install --path . --locked --bin qleisli`. Once this version is published,
install it from crates.io with:

```sh
cargo install qleisli --version 0.3.0-alpha --locked
```

Put Cargo's installation `bin` directory on PATH (normally `$HOME/.cargo/bin`).
Install the matching native bundle separately and set `QLEISLI_KERNEL` to its
`bin/qleisli-kernel` executable. For an unpublished source checkout, run
`(cd lean-kernel && lake build)` with Lean 4.30.0, then set
`QLEISLI_KERNEL` to that checkout's `lean-kernel/.lake/build/bin/qleisli-kernel`.

Create a directory named `bell` and save this program as `bell/main.qli`:

<!-- quickstart:bell -->
```qli
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;

observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```
<!-- /quickstart:bell -->

Also create `bell/Qargo.toml`:

<!-- quickstart:manifest -->
```toml
schema-version = 2

[qrate]
edition = "2026"
```
<!-- /quickstart:manifest -->

This edition-only declaration applies even when the source tree is not a qrate.
The standard library is already a qrate named `std` in the `stdlib/` directory,
with a full [qargo](https://github.com/MGYamada/qargo)-compatible manifest.
All other source trees will migrate to qrate management in the future. Rust's
implementation edition remains `"2024"`, independently of Qleisli edition `"2026"`.

From the parent of `bell`:

```sh
qleisli check bell
qleisli run bell
qleisli sample bell --shots=8 --seed=0
```

The standard library is embedded: this example runs without a repository
checkout or a separate library directory. `run` reports `00` and `11` with
probabilities approximately 0.5 each; `sample` returns eight simulated shots,
each `00` or `11`. These are local reference results, not device measurements.
Result bit strings follow the returned tuple from left to right. Numerical
probabilities can contain tiny rounding residues even for ideally impossible
outcomes. Add `--format=json` for structured results and diagnostics.

## Embed in Rust

Once this version is published, add this dependency to your Rust project's `Cargo.toml`:

```toml
[dependencies]
qleisli = "0.3.0-alpha"
```

The [API documentation](https://docs.rs/qleisli) provides a runnable
OpenQASM import and simulation example. Use `frontend::compile::compile_project`
for `.qli` projects, `interchange::native::Kernel::accept_raw` for raw IR, `interchange` for checked QIRF transport,
and `sim` for reference distributions or seeded sampling. Only independently
checked programs become `AcceptedProgram` values.

## Supported scope

- Finite `.qli` programs, modules, linear ownership, measurement/feedback,
  static operation parameters and exact finite contracts are implemented.
- `qleisli interop` supports bounded OpenQASM 3 input/output, QIRF input/output
  and QIR Base output. The terminal-circuit profile has explicit gate/resource
  limits; unsupported constructs reject with diagnostics. QASM input must
  initialize its qubits with `reset`.
- The separate Python host requires Python 3.11+ and the Rust executable.
  QIR text/bitcode **input** additionally requires optional PyQIR 0.12.5.
  Cargo installs neither the Python host nor the Lean checker.
- The additive experimental `qleisli sized` CLI checks and executes bounded
  `Q<Bits<n>>` / ordinary `Bits<m>` source and shared measured QPE. It requires a separately
  built Lean kernel; Cargo does not install that kernel. General source/runtime
  correspondence and full-profile migration remain pending.
- Lean is the sole production acceptance implementation. General **Soundness**, **Physical Realizability** and
  **Resource Safety** theorems remain goals to prove. Successful checking
  is not a proof of an algorithm's correctness, physical hardware behavior or
  a quantitative resource bound.

The published 0.2.1 first registry release adopted the name `qleisli` in place of
the earlier Git/path package `qleisli-core` and Rust import `qleisli_core`.
Those consumers must update dependency/import names or use the documented
Cargo alias.
Version 0.2.9 explicitly breaks the verifier API and runtime installation
contract: replace `verify`/`VerifiedProgram` with native acceptance/`AcceptedProgram`,
remove `interchange::dual`, and select the matching checker. Version 0.2.3 also
requires an edition manifest for filesystem source trees. The 0.3.0-alpha
prerelease uses ordinary `Unit`, `Bit`, `Bits<n>` and `0`/`1`; the retired
`CBit`/`CBits`, `false`/`true` and empty-tuple type spellings reject. General
basis polymorphism and the remaining common-checker work are still incomplete.

## Documentation

- [Language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/tests/fixtures/quick_reference/README.md)
- [Python and foreign-format connections](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/python/README.md)
- [Python setup](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/python/README.md)
- [Trust boundary and proof goals](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/TRUSTBOUNDARY.md)
- [Source, examples and roadmap](https://github.com/MGYamada/Qleisli)

Current documentation links target `v0.3.0-alpha`. The single book has its
sources in `docs/src/`, including the imaginary-v1 drafts and v0.3 Lean backend
plan. The retired `docs-old/` tree has been deleted. New chapters follow adopted
decisions, actual code and proofs.

## License

Copyright 2026 Masahiko G. Yamada. Qleisli's own code and documentation are
Apache-2.0 unless individually stated otherwise. See the packaged `LICENSE`
and `NOTICE`. The included corpus retains source-specific licenses and notices:
QuantumKatas translations are MIT; Qualtran and PennyLane translations are
Apache-2.0. This is not an `Apache-2.0 OR MIT` dual-license offer.
