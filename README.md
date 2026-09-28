# Qleisli: A Language for Structured Quantum Algorithms

Write quantum algorithms in the language you use to think about them.

Qleisli is an experimental quantum programming language implemented in Rust.
It combines **linear quantum ownership**, **explicit measurement effects**, and
**exact semantic contracts** so that reusable operations carry checkable meaning.
Human-written and AI-generated programs go through the same independent IR verifier.

[Quick reference](docs/qli-quick-reference.md) · [Current status](docs/current-status.md) · [Language reference](docs/frontend-v0.md) ·
[Roadmap](docs/v0x-roadmap.md) · [Documentation](docs/documentation-map.md)

## A small example

This program prepares a Bell pair and returns two correlated classical bits:

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

Each gate consumes its input owner and returns the next owner. Measurement
consumes a quantum owner and returns a classical bit. The checker rejects
copying a quantum value, reusing a consumed value, or silently dropping one.

<a id="rust-開発環境"></a>

## Try it

Install **Rust 1.85 or later**. The core crate has no external Rust dependencies.
From a checkout of this repository:

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/phase_estimation
cargo run --bin qleisli -- run examples/protocols
cargo run --bin qleisli -- run examples/operation_algorithms
cargo run --example shor15
```

To try your own program, save it as `main.qli` in a directory and pass that
directory to `check` or `run`. `run` prints an exhaustive reference distribution,
not hardware results or sampled shots. Bit strings follow the returned tuple
from left to right; probabilities are floating-point approximations.

Add `--format=json` to `check` or `run` for structured results and diagnostics.
Use `cargo run --bin qleisli -- doc stdlib/src/transforms.qli` to render source
documentation. See the [CLI and source guide](docs/frontend-v0.md).

For complete programs to adapt, start with the
[protocol components](examples/protocols/README.md) or
[operation-parameter algorithms](examples/operation_algorithms/README.md).
Their [source corpus](tests/fixtures/qli_authoring/README.md) checks inputs,
reference correlations and deliberate algorithm mistakes. The
[authoring report](docs/qli-authoring-feedback.md) turns observed writing
difficulties into language-design candidates. The
[iterative QPE example](examples/iterative_phase_estimation/README.md) exercises
measurement feedback against coherent QPE and independent branch checks;
[authoring records](tests/fixtures/authoring_sessions/README.md) preserve first
sources and diagnostic repair observations. Future issues are collected with acceptance
experiments in the [v0.2.0 backlog](docs/v0.2.0-backlog.md).

## Connect existing circuits

The bounded [OpenQASM 3 / QIR adapters](docs/interop-m1.1.md) support fixed
registers, twelve exact gates and terminal measurements. OpenQASM input must
explicitly initialize its qubits with `reset` before any gates.

```sh
cargo run --example interop -- qasm-run tests/fixtures/interop/bell.qasm
cargo run --example interop -- qasm-to-qir tests/fixtures/interop/bell.qasm
cargo run --example interop -- qli-to-qasm tests/fixtures/interop/terminal
```

The adapter rejects unsupported operations with a diagnostic. These are host
example modes; they do not submit jobs to a device. The connection contract
lists directions, limits, optional tools and verification boundaries.

<a id="north-starとリリース到達条件"></a>
<a id="現在の優先順位-言語仕様"></a>
<a id="現在の優先順位-v01の言語仕様と意味契約"></a>
<a id="第1開発目標-ai時代の量子言語"></a>
<a id="第2開発目標-量子アルゴリズムの構造化"></a>
<a id="第3層の将来計画-量子アルゴリズムの標準語彙"></a>
<a id="設計の境界"></a>

## Status and direction

**Version: 0.1.8.** The [release record](docs/releases/v0.1.8.md) and
[GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.8)
separate implemented features, executed checks and publication status. Basis
parameter patterns, n-ary tuples and binding-level ownership diagnostics address
friction found in the executable authoring corpus.

The [operation-contract example](examples/operation_contracts/main.qli) uses one
static operation parameter with two independently checked implementations.
Run it with `cargo run --bin qleisli -- run examples/operation_contracts`.

Today, Qleisli checks and executes finite programs with modules, linear
ownership, measurement/feedback, static inverse/control/repetition, and exact
finite semantic contracts, plus bounded static operation parameters and
basis-derived meanings. Small Grover, QPE and order-finding examples are
regressions. Function contracts allow different checked implementations of the
same meaning to serve an unchanged client.

The v1 goal is for **Shor, QPE and Grover to read like their textbook structure**
using shared components and parameters. General size-polymorphic algorithms,
scalable arithmetic and a general compiler soundness proof remain open.
Passing the current checks is not a proof of algorithm correctness or hardware
behavior. See the [design principles](docs/design-philosophy.md),
[acceptance criteria](docs/release-milestones.md) and [current inventory](docs/current-status.md).

<a id="文書"></a>

## Develop and contribute

Start with [AGENTS.md](AGENTS.md) and [CONTRIBUTING.md](CONTRIBUTING.md).
The [documentation map](docs/documentation-map.md) distinguishes current
specifications, future designs and historical evidence.

```sh
cargo test --all-targets
cargo fmt --check
cargo clippy --all-targets -- -D warnings
python3 scripts/check_docs.py
```

[Lean proofs](lean/README.md) use Lean/Mathlib 4.30.0. The [release checklist](docs/versioning.md#release-records-and-validation)
includes the additional proof, platform and packaging checks. Changes are
recorded in the [changelog](CHANGELOG.md).

## License

Copyright 2026 Masahiko G. Yamada.

Qleisli's own code, standard library, examples, tests, scripts, proofs and
documentation are licensed under [Apache-2.0](LICENSE), unless a file states
otherwise. See [NOTICE](NOTICE) and the [contribution policy](CONTRIBUTING.md).
Third-party material retains its own licenses and notices. This license does
not automatically apply to independently authored programs written in Qleisli.
