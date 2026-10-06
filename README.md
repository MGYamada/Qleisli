# Qleisli: A Language for Structured Quantum Algorithms

Write quantum algorithms in the language you use to think about them.

Qleisli is an experimental quantum programming language with a
**Rust frontend and native Lean verifier**.
It combines **linear quantum ownership**, **explicit measurement effects**, and
**exact semantic contracts** so that reusable operations carry checkable meaning.
Human-written and AI-generated programs go through the same independent IR verifier.

**Qleisli is pronounced exactly like Kleisli.** The initial Q is semantic,
not phonetic; see the [canonical name and ecosystem naming principle](docs/src/reference/project-identity.md).

**Policy as Theorem. Constitution as Harness. Compiler as Executor.**
The [architecture principle](docs/src/reference/architecture.md) connects human
interpretation, independent proof and execution of the authorized boundaries.

**Development version: 0.3.0-alpha (prerelease preparation; unpublished). Latest published version: 0.2.9.**
**Qleisli language edition: `"2026"`.**
Edition identifies the constitutional regime, not a syntax generation.
The [Constitution](CONSTITUTION.md) was ratified on 2026-10-04 (Asia/Tokyo);
the [adoption record](docs/src/design/ratification.md) identifies the exact text
and initial Guardian appointment. The 0.3.0 language migration stays in edition 2026.
All current `.qli` sources and `.qlt` drafts use edition 2026; every source tree
explicitly declares it in `Qargo.toml`. Compatible changes are recorded in the
[changelog](CHANGELOG.md).
Cargo builds and documents the Rust CLI/library without Lean. Verification and
execution require the matching native checker, selected by `--lean-kernel=PATH`
or `QLEISLI_KERNEL`. All public entry points use Lean acceptance; the Rust
verifier and dual API have been removed under the approved
[v0.2.9 breaking exception](https://github.com/MGYamada/Qleisli/issues/276).
Missing, incompatible or failing checkers reject without fallback or download.
Start with [installation and a Bell-pair program](#try-it).
Python connections and QIR input have optional requirements below.
The experimental sized-source pipeline uses an explicitly selected Lean kernel;
[executable clients and validation records](corpus/sized/README.md) describe
the supported experiments.
The three theorem pillars below are project goals. The
[Migration decision](https://github.com/MGYamada/Qleisli/issues/276) records implementation and proof scope.
Version 0.2.9 was published on 2026-10-04 (Asia/Tokyo): [crates.io](https://crates.io/crates/qleisli/0.2.9)
and [GitHub Release](https://github.com/MGYamada/Qleisli/releases/tag/v0.2.9).
[Publication evidence](tests/fixtures/releases/v0.2.9/publication.json) binds the immutable source,
registry artifact, fresh installation, hosted docs and complete GitHub downloads.

[Quick reference](tests/fixtures/quick_reference/README.md) · [Trust boundary](TRUSTBOUNDARY.md) ·
[Roadmap](ROADMAP.md) · [Verification migration](https://github.com/MGYamada/Qleisli/issues/276) ·
[Algorithm drafts](docs/src/imaginary-v1/index.md)

## Language edition and qrate management

The closest enclosing `Qargo.toml` explicitly selects edition `"2026"` for
each source. Compiler version `0.3.0-alpha`, Qleisli edition `"2026"` and the Rust
implementation's Cargo edition `"2024"` are independent. Missing manifests,
unsupported editions and malformed schema-2 manifests are rejected.

There is no `Qargo.toml` in the repository top-level directory. The
[corpus](corpus/Qargo.toml) and [standard library](stdlib/Qargo.toml) have their
own manifests; each example and the test trees declare their edition too.
**The standard library is already a qrate named `std` in `stdlib/`**, with a
complete schema-2 manifest following
[qargo](https://github.com/MGYamada/qargo), including its name, version and
source/test/documentation roots. Other trees currently use edition-only
manifests and are not qrates. **All source trees will migrate to qrate management
in the future.** QLT execution
remains deferred to v0.4.0 or later.

## A small example

This program prepares a Bell pair and returns two correlated classical bits:

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

Each gate consumes its input owner and returns the next owner. Measurement
consumes a quantum owner and returns a classical bit. The checker rejects
copying a quantum value, reusing a consumed value, or silently dropping one.

<a id="rust-開発環境"></a>

## Try it

Install **Rust 1.85 or later**. Cargo builds the Rust implementation and its TOML reader;
verification requires the matching native checker.
The package is named `qleisli`, its executable is `qleisli`, and its Rust
library is imported as `qleisli`.
Earlier Git/path users should rename the Cargo dependency `qleisli-core` to
`qleisli` and Rust imports from `qleisli_core` to `qleisli`.

Install from a source checkout:

```sh
cargo install --path . --locked --bin qleisli
```

Once 0.3.0-alpha is published, install this version from the registry:

```sh
cargo install qleisli --version 0.3.0-alpha --locked
```

For this unpublished checkout, build the checker with Lean 4.30.0 and select it:

```sh
(cd lean-kernel && lake build)
export QLEISLI_KERNEL="$PWD/lean-kernel/.lake/build/bin/qleisli-kernel"
```

A release native bundle needs no Lean development installation at runtime.
Cargo does not install or download that bundle; use the matching product version.
Native archives are prepared as
`qleisli-kernel-VERSION-TARGET.tar.gz`, with a matching `.sha256` checksum file,
an audited manifest, source commit and licenses. macOS and Linux full CI builds
produce release candidates; a candidate is not a published release. Extract the
whole archive and select its `bin/qleisli-kernel` using the environment variable
above. For this unpublished version, build from source until its matching assets
appear on [GitHub Releases](https://github.com/MGYamada/Qleisli/releases).


For the latest published release, use `--version 0.2.9` instead.
The [0.2.9 publication evidence](tests/fixtures/releases/v0.2.9/publication.json)
records its completed publication. The registry command and [API documentation](https://docs.rs/qleisli/0.2.9/qleisli/)
were verified after publication, including a fresh exact-version registry install.

Put Cargo's installation `bin` directory on PATH (normally `$HOME/.cargo/bin`).
Create a directory named `bell` and save the [small example above](#a-small-example)
as `bell/main.qli`. Also create `bell/Qargo.toml`:

<!-- quickstart:manifest -->
```toml
schema-version = 2

[qrate]
edition = "2026"
```
<!-- /quickstart:manifest -->

This edition-only form also applies to standalone projects that are not qrates.
From the parent of `bell`, run:

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

To try your own program, put `main.qli` and the explicit edition manifest above
in its top-level directory and pass that directory to `check` or `run`.
`run` prints an exhaustive reference distribution,
not hardware results or sampled shots. Bit strings follow the returned tuple
from left to right; probabilities are floating-point approximations. Even an
ideally impossible outcome may appear with a tiny positive rounding residue
in text or JSON output; interpret these values with a numerical tolerance.

Add `--format=json` to `check` or `run` for structured results and diagnostics.
Use `cargo run --bin qleisli -- doc stdlib/src/transform.qli` to render source
documentation; comments are isolated as fenced text so unfinished Markdown or
HTML cannot hide subsequent declarations. `qleisli --help` lists available commands.

Bounded source loading checks each manifest once per load and separately limits
directory entries to `max(64, project_bytes / 1024)`, including empty and non-source
files. Source byte limits retain their independent meaning. On Unix, selected qrate
roots anchor discovery and file reads by directory handle; this is identity binding,
not a snapshot of concurrently modified file contents.

Reference simulation reserves amplitude/component capacity across nested branches.
Its execution budget also charges copied classical values and quantum-owner
metadata before allocation, including sampling, reset and discard; reported
execution work includes these copies without relaxing numerical error alarms.
Branch phi outputs share that budget, including empty quantum owners. Sampling
reserves projection copies before requesting randomness for each observation.

For complete programs to adapt, start with the
[protocol components](examples/protocols/README.md) or
[operation-parameter algorithms](examples/operation_algorithms/README.md).
Their [source corpus](tests/fixtures/qli_authoring/README.md) checks inputs,
reference correlations and deliberate algorithm mistakes. The
[iterative QPE example](examples/iterative_phase_estimation/README.md) exercises
measurement feedback against coherent QPE and independent branch checks;
[authoring records](tests/fixtures/authoring_sessions/README.md) preserve first
sources and diagnostic repair observations. Track future work and its acceptance
experiments in [GitHub Issues](https://github.com/MGYamada/Qleisli/issues).
A GitHub Issue does not require a duplicate backlog entry or update.

## Connect existing circuits

The bounded OpenQASM 3 / QIR adapters support fixed
registers, twelve exact gates and terminal measurements. OpenQASM input must
explicitly initialize its qubits with `reset` before any gates.

```sh
cargo run --example interop -- qasm-run tests/fixtures/interop/bell.qasm
cargo run --example interop -- qasm-to-qir tests/fixtures/interop/bell.qasm
cargo run --example interop -- qli-to-qasm tests/fixtures/interop/terminal
```

The Python and CLI connection layer adds structured
import/check/run/sample/export commands and optional QIR text/bitcode input:

```sh
cargo run --bin qleisli -- interop run tests/fixtures/interop/bell.qasm --input=qasm
```

The [Python package](python/README.md) uses the Rust executable and optionally
PyQIR 0.12.5 for LLVM parsing. Unsupported operations reject with diagnostics;
these are bounded terminal-circuit adapters, not device submission or full
OpenQASM/QIR support. Every imported artifact goes through the native Lean verifier.
Select `--lean-kernel=PATH` on every `interop` action, or pass
`lean_kernel=PATH` to Python `Client`, or set `QLEISLI_KERNEL`.
The selection also applies to QIR translation and subsequent program methods;
native failure blocks checking, execution and output.

<a id="north-starとリリース到達条件"></a>
<a id="現在の優先順位-言語仕様"></a>
<a id="現在の優先順位-v01の言語仕様と意味契約"></a>
<a id="第1開発目標-ai時代の量子言語"></a>
<a id="第2開発目標-量子アルゴリズムの構造化"></a>
<a id="第3層の将来計画-量子アルゴリズムの標準語彙"></a>
<a id="設計の境界"></a>

## Status and direction

**0.3.0-alpha** starts preparation for the next prerelease. It selects the
new product version and completes the planned documentation cleanup; the
v0.3.0 type-system work remains in progress. [CHANGELOG](CHANGELOG.md) records
the unpublished changes.

The published v0.2.9 baseline uses Lean acceptance for source libraries,
unused concrete bodies, raw Rust adapters, foreign CLI operations and Python.
Sized hierarchy execution uses native-checked artifacts without repeating
Rust leaf acceptance. The
[VM29 record](tests/fixtures/verification_v029/README.md) gives exact scope and
remaining gates. [Decision #276](https://github.com/MGYamada/Qleisli/issues/276)
approves the exceptional v0.2.9 single-verifier migration. All production
acceptance now uses Lean, including function evidence and encoded contracts;
the Rust verifier and dual API are removed. Full Soundness remains a v0.5.0 obligation.
The published baselines are retained in their validation fixtures. The
[adopted cutover criteria](https://github.com/MGYamada/Qleisli/issues/276)
separate implementation, release validation and proof completion;
external schemas remain disabled. The [VM-25 pure raw-IR profile](tests/fixtures/verification_v025/completion/README.md)
has actual-checker complex-denotation, cleanup and retained-body binding proofs.
The [VM-26 component](tests/fixtures/verification_v026/README.md) checks observing
raw IR, SSA/phis and retained branch-functions. Actual matrix-free coefficients
refine original complex instruments and prove CP/TNI/TP for finite references.
Hierarchy semantics, source/native/runtime correspondence and full-profile
Soundness retain their explicitly scoped proof obligations.

The v0.3.0 type-system goals remain open; QLT implementation remains deferred to
v0.4.0 or later. These targets do not establish the three general theorems or
completion of the v1 algorithms.

The requested [v0.3.1–v0.3.9 backend plan](docs/src/lean-backend-plan-v0.3.md)
proposes earlier Lean backend expansion and staged Rust retirement, with local
pass relations, independent validation and explicit compatibility/deletion gates.

## Project goals

The enduring goals are three theorems — **Qleisli Soundness**, **Physical
Realizability** and **Resource Safety** — and six v1 algorithm goals:
**QPE, Grover, amplitude estimation, Shor, quantum walks and QSVT**. Express them
in executable source that follows their mathematical structure, with shared
components and explicit contracts. These are goals; the general theorems and
all six general algorithm implementations are not complete.

The active [v0.2.x migration goals](https://github.com/MGYamada/Qleisli/issues/276) remain
in force. The v0.3.0 cleanup retains two existing entries in `docs/`:
the entire `imaginary-v1/` tree and
[lean-backend-plan-v0.3.md](docs/src/lean-backend-plan-v0.3.md).
The retired `docs-old/` tree has been deleted. New documentation belongs in
`docs/` and must follow adopted decisions, actual code, proofs and executable
examples. Retired prose remains available through Git history.

The standard-library goal is a
**BLAS/LAPACK-like foundation for quantum computing, integrated with a textbook
and formal specifications**. Readers should be able to learn quantum information
by reading the library: concepts, derivations, reusable source, examples and
explicit proof status belong together. This is an adopted goal; comprehensive
library organization and generalized APIs remain future design work.

Passing the current checks is not a proof of algorithm correctness or hardware
behavior. The adopted decisions and fixture records state each checked component's scope.

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
the current bounded phase-word and DAG theorems are initial steps. The
[Migration decision](https://github.com/MGYamada/Qleisli/issues/276) states the remaining transfer gates.
Source translation validation continues after this kernel milestone.

By v1, we also aim to prove the
Physical Realizability Theorem
alongside a substantive Lean 4 backend. The intended chain is: the Soundness
Theorem yields completely positive, trace-preserving (CPTP) semantics as a
corollary for the complete computation, including all measurement outcomes;
physical realizability then constructs an isometric dilation and synthesizes
it over a declared gate set, with the required preparation, measurement,
discard and explicitly admitted synthesis workspace. Semantic unitarity does
not guarantee exact synthesis on the source wires alone; clean workspace must
return to zero and its resources must be counted (workspace contract). The backend proof must connect the actual emitted circuit to the
checked meaning, with exact equality or an explicitly certified approximation
bound. CPTP validity alone does not establish that synthesis result.

**The third pillar toward v1 is the
Resource Safety Theorem,
adopted on 2026-09-30 and still to prove:** well-typed programs in the supported
resource-checked profile admit finite, statically computable resource bounds
that are preserved by compilation. Lowering and optimization must maintain
the checked resource contract of the actual emitted program.

| Theorem pillar | Intended guarantee |
| --- | --- |
| Qleisli Soundness | Programs satisfy their checked semantic contracts. |
| Physical Realizability | The actual target implementation realizes the checked quantum meaning. |
| Resource Safety | Programs have finite, statically computable resource bounds preserved through compilation. |

The planned resource semantics makes resource
accounts first-class alongside types, meanings and effects: live qubits,
auxiliary space, gate counts, depth and measurements compose with the program.
These bounds depend on a declared cost/target model and all permitted execution
branches. Existing ownership checks and work limits do not already prove this
quantitative guarantee; finite does not mean efficient. The
[dated trust-boundary amendment](TRUSTBOUNDARY.md#resource-safety-amendment-2026-09-30)
records the new proof obligation without adding a trusted estimator.

These are planned theorems, not current guarantees about generated circuits or
hardware. Our longer-term direction is to move the implementation beyond the
frontend into Lean. Candidate search can remain external:
for example, a rotation-synthesis oracle proposes circuits and witnesses for
a proved Lean `LeafRealizer` checker. The goal is to prove or check each pass's
correctness, not rewrite all search code. Under this project direction, a Lean backend with proofs of
its actual transformations is a prerequisite for the goal “LLMs write `.qli`;
Lean guarantees it all the way down.” Source-to-IR translation validation and
the remaining native compiler/runtime and device assumptions must also be
accounted for before making that claim. The
backend execution policy
requires source and compiled-declaration CI to reject project `unsafe def`,
`@[implemented_by]`, `@[extern]` and `partial def`, so runtime replacements
cannot silently escape the proved definitions.

**From v0.5 onward, Qleisli will grow from individual development into a
full-scale, community-oriented open-source project.** The
roadmap ties that expansion
to a reproducible proof foundation, independent review, contributor onboarding
and transparent maintenance. Qleisli is already open source under Apache-2.0;
this is a change in development scale and organization.


Start with quantum programs written as they ought to be expressed, then grow
the language with AI so it can express and check them. This
development method
uses desired source, executable translations and concrete failures to guide
language design. The code-driven development procedure
defines the 0.1.x foundation, concrete obstacles and acceptance experiments for
the user-selected continuation from 0.2.0 onward.

## Develop and contribute

On GitHub, **Issues track implementation. Discussions determine the language.**
Use [Issues](https://github.com/MGYamada/Qleisli/issues) for implementation tasks
and bugs, and [Discussions](https://github.com/MGYamada/Qleisli/discussions) for
language proposals and decisions. This policy is limited to GitHub operations.

Start with [AGENTS.md](AGENTS.md) (mirrored in [CLAUDE.md](CLAUDE.md)) and
[CONTRIBUTING.md](CONTRIBUTING.md).

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

The VM plan distinguishes checked components from pending guarantees;
imaginary-v1 contains future designs, and fixtures retain historical evidence.

```sh
cargo test --all-targets
cargo test --doc
cargo doc --no-deps
cargo fmt --check
cargo clippy --all-targets -- -D warnings
python3 scripts/check_docs.py
```

[Lean proofs](lean/README.md) use Lean/Mathlib 4.30.0. The release checklist
includes the additional proof, platform and packaging checks. Changes are
recorded in the [changelog](CHANGELOG.md). The
crates.io preparation and publication procedure
separates local validation, release approval and registry publication.

The [three logo concepts](assets/logo-concepts/v0.4.0/README.md) are preserved
for the v0.4.0 design discussion.

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
