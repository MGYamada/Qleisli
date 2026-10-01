# Qleisli

Write quantum algorithms in the language you use to think about them.

Qleisli is an **experimental quantum programming language** with linear quantum
ownership, explicit measurement effects and exact finite semantic contracts.
The Rust frontend produces IR that an independent Rust verifier checks before
reference execution. Human-written and AI-generated programs use the same checks.

Package: **`qleisli`** · executable: **`qleisli`** · Rust library: **`qleisli`**.
Package version: **0.2.5**. See the
[release record](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/releases/v0.2.5.md)
for the checked profile and publication evidence.
**Qleisli language edition: `"2026"` for all current
`.qli` and `.qlt` files.** Each source tree requires an explicit `Qargo.toml`.
The version-specific release record distinguishes the
implemented bounded profile from pending proof and migration goals.
Rust 1.85 or later is required. Cargo builds the implementation and its TOML reader;
ordinary CLI/library use requires no Lean, Python or LLVM installation.
On macOS, source loading uses descriptor-relative `openat` with `O_NOFOLLOW`
for each component, preserving Rust's existing deployment targets without
requiring macOS 11's `O_NOFOLLOW_ANY` flag.
Filesystem source loading on Linux x86/x86_64, ARM/aarch64 and RISC-V requires
accessible procfs directory descriptors at `/proc/self/fd`. A missing or
inaccessible descriptor path produces a targeted runtime diagnostic.

## Install and run

Install from a source checkout with
`cargo install --path . --locked --bin qleisli`. Install this version from
crates.io with:

```sh
cargo install qleisli --version 0.2.5 --locked
```

Put Cargo's installation `bin` directory on PATH (normally `$HOME/.cargo/bin`).

Create a directory named `bell` and save this program as `bell/main.qli`:

<!-- quickstart:bell -->
```qli
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;

observe fn main() -> (CBit, CBit) {
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

Add this dependency to your Rust project's `Cargo.toml`:

```toml
[dependencies]
qleisli = "0.2.5"
```

The [API documentation](https://docs.rs/qleisli) provides a runnable
OpenQASM import and simulation example. Use `frontend::compile::compile_project`
for `.qli` projects, `verify` for raw IR, `interchange` for checked QIRF transport,
and `sim` for reference distributions or seeded sampling. Only independently
checked programs become `VerifiedProgram` values.

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
  `Bits<n>` / `CBits<m>` source and shared measured QPE. It requires a separately
  built Lean kernel; Cargo does not install that kernel. General source/runtime
  correspondence and full-profile migration remain pending.
- The staged Lean kernel migration does not transfer production acceptance
  authority from Rust. General **Soundness**, **Physical Realizability** and
  **Resource Safety** theorems remain goals to prove. Successful checking
  is not a proof of an algorithm's correctness, physical hardware behavior or
  a quantitative resource bound.

The published 0.2.1 first registry release adopted the name `qleisli` in place of
the earlier Git/path package `qleisli-core` and Rust import `qleisli_core`.
Those consumers must update dependency/import names or use the documented
[Cargo alias](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/crates-io-release.md#name-migration-from-github-releases-through-020).
This user-selected identity migration is a narrow exception; other 0.2.x
contracts stay compatible except for the explicitly selected v0.2.3 requirement
to add an edition manifest to filesystem source trees. The planned 0.3.0
type-system work is a separate
breaking-change boundary.

## Documentation

- [Language editions and qrate migration](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/language-editions.md)

- [Language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/qli-quick-reference.md)
- [Python and foreign-format connections](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/interop-m1.1.md)
- [Python setup](https://github.com/MGYamada/Qleisli/blob/v0.2.5/python/README.md)
- [Trust boundary and proof goals](https://github.com/MGYamada/Qleisli/blob/v0.2.5/TRUST_BOUNDARY.md)
- [Release and validation record](https://github.com/MGYamada/Qleisli/blob/v0.2.5/docs/releases/v0.2.5.md)
- [Source, examples and roadmap](https://github.com/MGYamada/Qleisli)

Version-pinned documentation links above target the `v0.2.5` source tag.
Packaged files contain the current specifications and release record;
source validation, tagging and publication are recorded separately.

## License

Copyright 2026 Masahiko G. Yamada. Qleisli's own code and documentation are
Apache-2.0 unless individually stated otherwise. See the packaged `LICENSE`
and `NOTICE`. The included corpus retains source-specific licenses and notices:
QuantumKatas translations are MIT; Qualtran and PennyLane translations are
Apache-2.0. This is not an `Apache-2.0 OR MIT` dual-license offer.
