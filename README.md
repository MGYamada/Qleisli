# Qleisli: A Language for Structured Quantum Algorithms

Write quantum algorithms in the language you use to think about them.

Start with quantum programs written as they ought to be expressed, then grow
the language with AI so it can express and check them. This
[development method](docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write)
uses desired source, executable translations and concrete failures to guide
language design. The [code-driven development procedure](docs/code-driven-development.md)
defines the 0.1.x foundation, concrete obstacles and acceptance experiments for
the user-selected continuation from 0.2.0 onward.

Qleisli is an experimental quantum programming language built around a
**Rust frontend and a Lean 4 verification kernel**.
It combines **linear quantum ownership**, **explicit measurement effects**, and
**exact semantic contracts** so that reusable operations carry checkable meaning.
Human-written and AI-generated programs go through the same independent IR verifier.
The [Lean migration](docs/lean-kernel-migration.md) is underway: the first executable
kernel checks phase-sensitive words and [shared call/repetition DAGs](docs/lean-hierarchy-slice.md)
**without Mathlib**, with soundness proofs for the actual checking functions
over cyclic phase semantics. A [typed layout checker](docs/lean-layout-slice.md)
also verifies owner/axis permutations, with proofs covering zero-width ownership
and reference-preserving reindexing. [Shared typed calls and composition](docs/lean-layout-dag-slice.md)
now bind those layouts to actual dependencies with an executable soundness theorem.
The [combined phase/layout checker](docs/lean-phase-layout-slice.md) also composes
controlled dyadic phases and typed call adapters with proved cyclic-phase semantics.
The [interference foundation](docs/lean-interference-slice.md) proves Hadamard
cancellation on joint amplitudes and connects the actual definitions to complex
semantics in a separate proof package; the runtime remains Mathlib-free.
The [QFT circuit proof](docs/lean-qft-proof-packet.md) now establishes all Fourier
coefficients and reference amplitudes for the actual matched gate template at
widths 1–8, now extended to a [typed shared-circuit projection](docs/lean-qft-graph-packet.md).
The [QPE component proofs](docs/lean-qpe-instrument-packet.md) establish the
actual controlled-power schedule, full residual target/reference instrument,
and completeness and total trace preservation under the provider-isometry premise.
Their [component registry](docs/lean-qpe-instrument-packet.md#shipped-type-and-source-manifest)
pins rebuilt theorem types and source revisions; external entries remain disabled.
The complete external hierarchy, provider evidence and schema binding remain open.
The full production `check`/`run` path still uses the Rust verifier during this staged migration.

[Quick reference](docs/qli-quick-reference.md) · [Type system](docs/type-system.md) · [Trust boundary](TRUST_BOUNDARY.md) · [Current status](docs/current-status.md) · [Language reference](docs/frontend-v0.md) ·
[Roadmap](docs/v0x-roadmap.md) · [Documentation](docs/documentation-map.md)

## v0.5.0 milestone: Qleisli Soundness Theorem

**Our central v0.5.0 milestone is to prove the Qleisli Soundness Theorem in
Lean 4 for the production verification kernel's supported IR profile.**

$$
\operatorname{verify}(p,C,\pi)=\mathrm{true}
\quad\Longrightarrow\quad \llbracket p\rrbracket\models C.
$$

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

This is a planned theorem, not a current guarantee about generated circuits or
hardware. Our longer-term direction is to move the implementation beyond the
frontend into Lean. Under this project direction, a Lean backend with proofs of
its actual transformations is a prerequisite for the goal “LLMs write `.qli`;
Lean guarantees it all the way down.” Source-to-IR translation validation and
the remaining native compiler/runtime and device assumptions must also be
accounted for before making that claim.

**From v0.5 onward, Qleisli will grow from individual development into a
full-scale, community-oriented open-source project.** The
[roadmap](docs/v0x-roadmap.md#community-development-from-v05) ties that expansion
to a reproducible proof foundation, independent review, contributor onboarding
and transparent maintenance. Qleisli is already open source under Apache-2.0;
this is a change in development scale and organization.

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
cargo run --bin qleisli -- sample examples/bell --shots=8 --seed=0
cargo run --example sampled_shor15
```

The separate [Lean kernel package](lean-kernel/README.md) builds with Lean 4.30.0
and no external Lean dependencies. Its README includes the native checker,
Rust launcher and independent differential test commands. Development checks
require Python 3.11 or later; the kernel executable does not require Python.

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

**Version: 0.2.0.** See the [release record](docs/releases/v0.2.0.md) and
[GitHub publication](https://github.com/MGYamada/Qleisli/releases/tag/v0.2.0).
The [revised 0.2.0 scope](docs/v0.2.0-plan.md) packages the implemented tuple/type
correction, finite external verification, sampling/trials, resource limits and
experimental Lean kernel/proof foundation. The remaining production hierarchy,
sized source, common QPE/QFT and integrated execution/acceptance move to the
[0.2.1 target](docs/v0.2.1-plan.md), with their existing proof and H1–H5 gates.
The measured-bit sequence is named `CBits<m>`; sized syntax remains unimplemented.
0.2.1 requires backward compatibility; a necessary breaking change uses 0.3.0.
The [development record](docs/releases/v0.2.0.md) separates completed packets,
validation and release gates. The finite B019 foundation and published 0.1.9
history remain in the [0.1.9 record](docs/releases/v0.1.9.md).

The first implementation packets add seeded `sample`, typed host trials and
bounded source loading. The CLI defaults to 1 MiB per source and 16 MiB per
project; `--legacy-source-limits` explicitly retains prior byte loading.
Existing `run` still returns an exhaustive reference distribution.

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

The planned [QLT test language](docs/qlt-design.md) will compare `.qli`
implementations with independent mathematical references, inspect structural
costs and run documentation examples outside the physical language. A Rust
experiment is targeted for 0.3–0.4, followed by instrument tests and Lean
evaluation proofs. The [source drafts and counterexamples](tests/fixtures/qlt_design/README.md)
are preserved; `.qlt` and `qleisli test` are not implemented. This adds no
0.2.0 release gate or new requirement to the soundness/realizability milestones.
A future 0.x.0 [Lean-assisted mathematical debugger](docs/lean-debugger-plan.md)
will connect proof obligations and checked counterexamples to IR and source
locations, distinguishing contract mismatches from missing evidence and
undecided checks. It is planned, with no implemented command or selected version.

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

The [input corpus](corpus/README.md) is restricted to QuantumKatas, Qualtran
Bloqs and PennyLane Demos by the adopted [corpus and licensing policy](corpus/POLICY.md).
Katas translations are MIT; the other two sources' translations are Apache-2.0.
The repository is not dual-licensed `Apache-2.0 OR MIT`.
