# Qleisli

Write quantum algorithms in the language you use to think about them.

Qleisli is an **experimental quantum programming language** with linear quantum
ownership, explicit measurement effects and exact finite semantic contracts.
The Rust frontend produces IR that an independent Rust verifier checks before
reference execution. Human-written and AI-generated programs use the same checks.

Package: **`qleisli`** · executable: **`qleisli`** · Rust library: **`qleisli`**.
Rust 1.85 or later is required. There are no external Rust dependencies;
ordinary CLI/library use requires no Lean, Python or LLVM installation.

## Install and run

Install the 0.2.1 executable from crates.io:

```sh
cargo install qleisli --version 0.2.1 --locked
```

Alternatively, install from a repository checkout with
`cargo install --path . --locked --bin qleisli`.
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

From its parent directory:

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
qleisli = "0.2.1"
```

The [API documentation](https://docs.rs/qleisli) provides a runnable
OpenQASM import and simulation example. Use `frontend::compile::compile_project`
for `.qli` projects, `verify` for raw IR, `interchange` for checked QIRF transport,
and `sim` for reference distributions or seeded sampling. Only independently
checked programs become `VerifiedProgram` values. The docs.rs page becomes
available after the registry release and its documentation build succeed.

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
- Sized `Bits<n>` / `CBits<m>` source and shared-QPE hierarchy experiments are
  not integrated into the production CLI. Their remaining integration and
  proof work targets 0.2.2.
- The staged Lean kernel migration does not transfer production acceptance
  authority from Rust. General **Soundness**, **Physical Realizability** and
  **Resource Safety** theorems remain goals to prove. Successful checking
  is not a proof of an algorithm's correctness, physical hardware behavior or
  a quantitative resource bound.

This first-registry-release preparation adopts the name `qleisli` in place of
the earlier Git/path package `qleisli-core` and Rust import `qleisli_core`.
Those consumers must update dependency/import names or use the documented
[Cargo alias](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/crates-io-release.md#name-migration-from-github-releases-through-020).
This user-selected identity migration is a narrow exception; other 0.2.x
contracts stay compatible. The planned 0.3.0 type-system work is a separate
breaking-change boundary.

## Documentation

- [Language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/qli-quick-reference.md)
- [Python and foreign-format connections](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/connections-v021.md)
- [Python setup](https://github.com/MGYamada/Qleisli/blob/v0.2.1/python/README.md)
- [Trust boundary and proof goals](https://github.com/MGYamada/Qleisli/blob/v0.2.1/TRUST_BOUNDARY.md)
- [Release and validation record](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/releases/v0.2.1.md)
- [Source, examples and roadmap](https://github.com/MGYamada/Qleisli)

Documentation links are pinned to the `v0.2.1` source tag. The packaged files
retain the same version-specific specifications and validation account.

## License

Copyright 2026 Masahiko G. Yamada. Qleisli's own code and documentation are
Apache-2.0 unless individually stated otherwise. See the packaged `LICENSE`
and `NOTICE`. The included corpus retains source-specific licenses and notices:
QuantumKatas translations are MIT; Qualtran and PennyLane translations are
Apache-2.0. This is not an `Apache-2.0 OR MIT` dual-license offer.
