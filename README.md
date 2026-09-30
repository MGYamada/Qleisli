# Qleisli: A Language for Structured Quantum Algorithms

Write quantum algorithms in the language you use to think about them.

Qleisli is an experimental quantum programming language with a
**Rust frontend and verifier**.
It combines **linear quantum ownership**, **explicit measurement effects**, and
**exact semantic contracts** so that reusable operations carry checkable meaning.
Human-written and AI-generated programs go through the same independent IR verifier.

**Version: 0.2.2.** See the [release record](docs/releases/v0.2.2.md) for
validation and publication status.
The Rust CLI and library need no Lean, Python or LLVM installation.
Start with [installation and a Bell-pair program](#try-it).
Python connections and QIR input have separate optional requirements below.
Sized `Bits<n>` / `CBits<m>` source remains experimental; the three theorem
pillars below are future proof goals. The
[0.2.2 release record](docs/releases/v0.2.2.md) and
[release procedure](docs/crates-io-release.md) distinguish version selection,
validation and publication. Version 0.2.2 is available on
[crates.io](https://crates.io/crates/qleisli/0.2.2) and
[GitHub Releases](https://github.com/MGYamada/Qleisli/releases/tag/v0.2.2).

[Quick reference](docs/qli-quick-reference.md) · [Type system](docs/type-system.md) · [Trust boundary](TRUST_BOUNDARY.md) · [Current status](docs/current-status.md) · [Language reference](docs/frontend-v0.md) ·
[Roadmap](docs/v0x-roadmap.md) · [Documentation](docs/documentation-map.md)

## A small example

This program prepares a Bell pair and returns two correlated classical bits:

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

Each gate consumes its input owner and returns the next owner. Measurement
consumes a quantum owner and returns a classical bit. The checker rejects
copying a quantum value, reusing a consumed value, or silently dropping one.

<a id="rust-開発環境"></a>

## Try it

Install **Rust 1.85 or later**. The core crate has no external Rust dependencies.
The package is named `qleisli`, its executable is `qleisli`, and its Rust
library is imported as `qleisli`.
Earlier Git/path users of `qleisli-core` / `qleisli_core` should follow the
[name migration](docs/crates-io-release.md#name-migration-from-github-releases-through-020).

Install the matching executable from crates.io:

```sh
cargo install qleisli --version 0.2.2 --locked
```

Alternatively, install from this checkout:

```sh
cargo install --path . --locked --bin qleisli
```

This checkout and the installation command select the same 0.2.2 version.
The [release record](docs/releases/v0.2.2.md#successful-publication-2026-09-30)
records the verified tag, registry artifact and installation checks.

Put Cargo's installation `bin` directory on PATH (normally `$HOME/.cargo/bin`).
Create a directory named `bell` and save the [small example above](#a-small-example)
as `bell/main.qli`. From its parent directory, run:

```sh
qleisli check bell
qleisli run bell
qleisli sample bell --shots=8 --seed=0
```

`run` reports `00` and `11` with probabilities approximately 0.5 each;
`sample` returns eight simulated shots, each `00` or `11`. The standard library
is embedded in the executable, so running this program needs no repository
checkout or external standard-library directory.

For Rust embedding, start with the executable example and API guide in
[src/lib.rs](src/lib.rs); build local API documentation with `cargo doc --no-deps`.
The registry landing page uses the shorter [package README](README.crates.md),
with absolute links and no dependency on a math renderer.

Additional examples from a checkout of this repository:

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/phase_estimation
cargo run --bin qleisli -- run examples/protocols
cargo run --bin qleisli -- run examples/operation_algorithms
cargo run --example shor15
cargo run --bin qleisli -- sample examples/bell --shots=8 --seed=0
cargo run --example sampled_shor15
```

The separate, optional [Lean kernel package](lean-kernel/README.md) builds with Lean 4.30.0
and no external Lean dependencies. Its README includes the native checker,
Rust launcher and independent differential test commands. Development checks
require Python 3.11 or later; the kernel executable does not require Python.

To try your own program, save it as `main.qli` in a directory and pass that
directory to `check` or `run`. `run` prints an exhaustive reference distribution,
not hardware results or sampled shots. Bit strings follow the returned tuple
from left to right; probabilities are floating-point approximations. Even an
ideally impossible outcome may appear with a tiny positive rounding residue
in text or JSON output; see the [numerical output contract](docs/ir-prototype.md#reference-execution).

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
sources and diagnostic repair observations. Track future work and its acceptance
experiments in [GitHub Issues](https://github.com/MGYamada/Qleisli/issues).
A GitHub Issue does not require a duplicate backlog entry or update.

## Connect existing circuits

The bounded [OpenQASM 3 / QIR adapters](docs/interop-m1.1.md) support fixed
registers, twelve exact gates and terminal measurements. OpenQASM input must
explicitly initialize its qubits with `reset` before any gates.

```sh
cargo run --example interop -- qasm-run tests/fixtures/interop/bell.qasm
cargo run --example interop -- qasm-to-qir tests/fixtures/interop/bell.qasm
cargo run --example interop -- qli-to-qasm tests/fixtures/interop/terminal
```

The [Python and CLI connection layer](docs/connections-v021.md) adds structured
import/check/run/sample/export commands and optional QIR text/bitcode input:

```sh
cargo run --bin qleisli -- interop run tests/fixtures/interop/bell.qasm --input=qasm
```

The [Python package](python/README.md) uses the Rust executable and optionally
PyQIR 0.12.5 for LLVM parsing. Unsupported operations reject with diagnostics;
these are bounded terminal-circuit adapters, not device submission or full
OpenQASM/QIR support. Every imported artifact goes through the Rust verifier.

<a id="north-starとリリース到達条件"></a>
<a id="現在の優先順位-言語仕様"></a>
<a id="現在の優先順位-v01の言語仕様と意味契約"></a>
<a id="第1開発目標-ai時代の量子言語"></a>
<a id="第2開発目標-量子アルゴリズムの構造化"></a>
<a id="第3層の将来計画-量子アルゴリズムの標準語彙"></a>
<a id="設計の境界"></a>

## Status and direction

This version is **0.2.2**; the [release record](docs/releases/v0.2.2.md)
identifies its validation and publication results. The active
[0.2.2 plan](docs/v0.2.2-plan.md) and [0.2.2–0.2.9 verification migration](docs/verification-migration-v0.2.md)
remain the current work targets. [Current status](docs/current-status.md) records
bounded sized-source/QPE integration and the remaining checking/proof scope.
Rust remains the production acceptance authority; external schemas are disabled.

The [development record](docs/releases/v0.2.2.md) records local validation and
[release preparation](docs/crates-io-release.md). Future type-system breaks use
v0.3.0; QLT implementation remains deferred to v0.4.0 or later. These schedules
do not establish the three general theorems or completion of the v1 algorithms.

## Project goals

The enduring goals are three theorems — **Qleisli Soundness**, **Physical
Realizability** and **Resource Safety** — and six v1 algorithm goals:
**QPE, Grover, amplitude estimation, Shor, quantum walks and QSVT**. Express them
in executable source that follows their mathematical structure, with shared
components and explicit contracts. These are goals; the general theorems and
all six general algorithm implementations are not complete.

The active [v0.2.x migration goals](docs/verification-migration-v0.2.md) remain
in force. Under **docs/ cleanup boundary at v0.3.0**, obsolete documents are
removed now and the remaining legacy documentation is retired at v0.3.0, when
the documentation will be written from scratch.

The [standard-library goal](docs/stdlib-roadmap.md#adopted-library-goal) is a
**BLAS/LAPACK-like foundation for quantum computing, integrated with a textbook
and formal specifications**. Readers should be able to learn quantum information
by reading the library: concepts, derivations, reusable source, examples and
explicit proof status belong together. This is an adopted goal; comprehensive
library organization and generalized APIs remain future design work.

Passing the current checks is not a proof of algorithm correctness or hardware
behavior. See the [design principles](docs/design-philosophy.md),
[acceptance criteria](docs/release-milestones.md) and [current inventory](docs/current-status.md).

<a id="文書"></a>

## v0.5.0 milestone: Qleisli Soundness Theorem

**Our central v0.5.0 milestone is to prove the Qleisli Soundness Theorem in
Lean 4 for the production verification kernel's supported IR profile.**

```math
\mathrm{verify}(p,C,\pi)=\mathrm{true}
\quad\Longrightarrow\quad [\![p]\!]\models C.
```

Acceptance must guarantee the independently requested contract: linear resource
safety, declared effects, exact phase, and clean auxiliary return, including
inputs entangled with a reference system. This is a **planned proof milestone**;
the current bounded phase-word and DAG theorems are initial steps. See the
[theorem scope and completion gates](docs/release-milestones.md#qleisli-soundness-theorem-v050).
Source translation validation continues after this kernel milestone.

By v1, we also aim to prove the
[Physical Realizability Theorem](docs/release-milestones.md#physical-realizability-theorem-v1)
alongside a substantive Lean 4 backend. The intended chain is: the Soundness
Theorem yields completely positive, trace-preserving (CPTP) semantics as a
corollary for the complete computation, including all measurement outcomes;
physical realizability then constructs an isometric dilation and synthesizes
it over a declared gate set, with the required preparation, measurement and
discard. The backend proof must connect the actual emitted circuit to the
checked meaning, with exact equality or an explicitly certified approximation
bound. CPTP validity alone does not establish that synthesis result.

**The third pillar toward v1 is the
[Resource Safety Theorem](docs/release-milestones.md#resource-safety-theorem-v1),
adopted on 2026-09-30 and still to prove:** well-typed programs in the supported
resource-checked profile admit finite, statically computable resource bounds
that are preserved by compilation. Lowering and optimization must maintain
the checked resource contract of the actual emitted program.

| Theorem pillar | Intended guarantee |
| --- | --- |
| Qleisli Soundness | Programs satisfy their checked semantic contracts. |
| Physical Realizability | The actual target implementation realizes the checked quantum meaning. |
| Resource Safety | Programs have finite, statically computable resource bounds preserved through compilation. |

The planned [resource semantics](docs/resource-semantics.md) makes resource
accounts first-class alongside types, meanings and effects: live qubits,
auxiliary space, gate counts, depth and measurements compose with the program.
These bounds depend on a declared cost/target model and all permitted execution
branches. Existing ownership checks and work limits do not already prove this
quantitative guarantee; finite does not mean efficient. The
[dated trust-boundary amendment](TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30)
records the new proof obligation without adding a trusted estimator.

These are planned theorems, not current guarantees about generated circuits or
hardware. Our longer-term direction is to move the implementation beyond the
frontend into Lean. [Candidate search can remain external](docs/lean-kernel-migration.md#external-search-and-the-leafrealizer-checker):
for example, a rotation-synthesis oracle proposes circuits and witnesses for
a proved Lean `LeafRealizer` checker. The goal is to prove or check each pass's
correctness, not rewrite all search code. Under this project direction, a Lean backend with proofs of
its actual transformations is a prerequisite for the goal “LLMs write `.qli`;
Lean guarantees it all the way down.” Source-to-IR translation validation and
the remaining native compiler/runtime and device assumptions must also be
accounted for before making that claim. The
[backend execution policy](docs/lean-kernel-migration.md#backend-execution-must-match-kernel-definitions)
requires source and compiled-declaration CI to reject project `unsafe def`,
`@[implemented_by]`, `@[extern]` and `partial def`, so runtime replacements
cannot silently escape the proved definitions.

**From v0.5 onward, Qleisli will grow from individual development into a
full-scale, community-oriented open-source project.** The
[roadmap](docs/v0x-roadmap.md#community-development-from-v05) ties that expansion
to a reproducible proof foundation, independent review, contributor onboarding
and transparent maintenance. Qleisli is already open source under Apache-2.0;
this is a change in development scale and organization.


Start with quantum programs written as they ought to be expressed, then grow
the language with AI so it can express and check them. This
[development method](docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write)
uses desired source, executable translations and concrete failures to guide
language design. The [code-driven development procedure](docs/code-driven-development.md)
defines the 0.1.x foundation, concrete obstacles and acceptance experiments for
the user-selected continuation from 0.2.0 onward.

## Develop and contribute

Start with [AGENTS.md](AGENTS.md) and [CONTRIBUTING.md](CONTRIBUTING.md).

The planned [QLT test language](https://github.com/MGYamada/Qleisli/issues/50) will compare `.qli`
implementations with independent mathematical references, inspect structural
costs and run documentation examples outside the physical language. A Rust
experiment is deferred to v0.4.0 or later, after the type-system work, followed
by instrument tests and Lean evaluation proofs. The [source drafts and counterexamples](tests/fixtures/qlt_design/README.md)
are preserved; `.qlt` and `qleisli test` are not implemented. This adds no
0.2.0 release gate or new requirement to the soundness/realizability milestones.
A future 0.x.0 [Lean-assisted mathematical debugger](https://github.com/MGYamada/Qleisli/issues/51)
will connect proof obligations and checked counterexamples to IR and source
locations, distinguishing contract mismatches from missing evidence and
undecided checks. It is planned, with no implemented command or selected version.

The [documentation map](docs/documentation-map.md) distinguishes current
specifications, future designs and historical evidence.

```sh
cargo test --all-targets
cargo test --doc
cargo doc --no-deps
cargo fmt --check
cargo clippy --all-targets -- -D warnings
python3 scripts/check_docs.py
```

[Lean proofs](lean/README.md) use Lean/Mathlib 4.30.0. The [release checklist](docs/versioning.md#release-records-and-validation)
includes the additional proof, platform and packaging checks. Changes are
recorded in the [changelog](CHANGELOG.md). The
[crates.io preparation and publication procedure](docs/crates-io-release.md)
separates local validation, release approval and registry publication.

## License

Copyright 2026 Masahiko G. Yamada.

Qleisli's own code, standard library, examples, tests, scripts, proofs and
documentation are licensed under [Apache-2.0](LICENSE), unless a file states
otherwise. See [NOTICE](NOTICE) and the [contribution policy](CONTRIBUTING.md).
Third-party material retains its own licenses and notices. This license does
not automatically apply to independently authored programs written in Qleisli.

The [input corpus](corpus/README.md) is restricted to QuantumKatas, Qualtran
Bloqs and PennyLane Demos by the adopted [corpus and licensing policy](corpus/POLICY.md).
Katas translations are MIT; the other two sources' translations are Apache-2.0.
The repository is not dual-licensed `Apache-2.0 OR MIT`.
