# Qleisli: Quantum Vibecoding Language

**Current version: 0.1.6** · [Release record and validation](docs/releases/v0.1.6.md) · [Current status](docs/current-status.md) · [Apache-2.0](LICENSE) · [Changelog](CHANGELOG.md) · [Versioning policy](docs/versioning.md)

**Rust-style source documentation is available.** Use `//!` for a module and
`///` for a function; nested block comments and inner/outer block docs are also
supported. `qleisli doc stdlib/src/transforms.qli` renders source documentation
without checking types/contracts or executing it. Every bundled definition is documented in
English. See the [comment rules and migration](docs/documentation-comments.md),
including the user's explicit exception to retain this feature in 0.1.6.

**v0.1.6 starts compatible IR/evidence maintenance.** The independent verifier
now enforces its existing 64-level classical-branch limit even when the deepest
arms are empty. Boundary regressions also cover the separate 32-level function
evidence profile. Legacy qif-arm execution now shares the existing finite circuit
executor while retaining public IR compatibility. Version selection and local
checks do not establish publication.

The [selected path](docs/decisions/2026-09-27-v1-path.md) starts with fixed-width
operation/access contracts and basis-derived meanings, followed by bounded
symbolic checking, hierarchical IR and multi-width QPE. [M0–M5](docs/v0x-roadmap.md)
are independent of release numbers; maintenance audits continue alongside them.
The [M1 language rules](docs/next-minor-spec.md),
[machine interfaces](docs/machine-interface-spec.md), and
[M2 checker profile](docs/hierarchical-ir-spec.md) specify the selected future
slices; their implementations and acceptance tests remain open.
The [local v0.1.5 roadmap is complete](docs/releases/v0.1.5.md#roadmap-completion-evidence).
The [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.6)
identifies the exact commit, CI, annotated tag and publication state.

The selected [interoperability direction](docs/interoperability-roadmap.md)
adds future Python bindings and bounded OpenQASM 3/QIR import/export around the
shared verifier. Specifications and implementation of these adapters are pending.
The [small trusted-core boundary](docs/design-philosophy.md#keep-the-trusted-core-small)
puts convenience in desugaring, not the checker. The [IR reduction inventory](docs/interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
records raw-only variants as compatibility debt; numeric execution sharing
does not yet remove trusted verification rules.

Here **[desugaring](docs/terminology.md#desugaring-layer)** means translating
convenience syntax/representations into already specified core operations,
preserving meaning and submitting the untrusted result to independent checking.
It adds no new primitive or checker rule. The [coefficient-domain note](docs/coefficient-domains.md)
records future parameterization of exact algebra and separate approximation
and hardware contracts, so the design need not assume one future gate set;
these extensions are not implemented.

The [six imaginary-v1 drafts](docs/imaginary-v1/README.md) and
[semantic review](docs/imaginary-v1/review.md) are design artifacts. The
[independent symbolic prototype](research/semantic-kernel/README.md) remains
outside production `.qli` checking. Its bounded continuation is selected for
M2; integration, scalable arithmetic and general compiler soundness are still
open. Current finite-core contracts and their regression examples are preserved.

Qleisli is a purely functional quantum programming language with an implementation in Rust. It treats quantum data as owned resources that cannot be copied, and programs as composable, effectful transformations of classical values and quantum resources.

**The project is at the design and implementation-prototype stage.** The [finite-core language specification v0](docs/language-spec.md) is specified. Within the implementation profile's capacity limits, name resolution, type/effect/ownership checking, IR generation, independent IR verification, and reference execution are connected. Alongside Bell, phase-oracle, and feedback examples, [small structured Grover, Bernstein–Vazirani, and bit-flip correction examples](docs/algorithm-routines.md) execute with the expected distributions. Bundled ordinary definitions live in `stdlib/src/basis.qli`, `stdlib/src/routines.qli`, `stdlib/src/transforms.qli`, and `stdlib/src/arithmetic.qli`. [Static adjoints, control, finite repetition, and small QPE examples](docs/static-operations.md) are also implemented. The [supported profile](docs/frontend-v0.md) is limited; general implementation soundness proofs and external backends remain unfinished.

This is the English project overview. The [documentation map](docs/documentation-map.md) identifies authoritative specifications, accepted design principles, proposals, and historical evidence. Translating a design document does not adopt new syntax or strengthen a guarantee.

<a id="north-starとリリース到達条件"></a>

## North star and release milestones

**North star (adopted 2026-09-27):**

> Make the language people use to think about quantum algorithms coincide with the language they use to write programs.

State preparation, oracles, reflections, phase estimation, uncomputation, and their compositions should become program vocabulary that preserves their meaning. **For v1, Shor, QPE, and Grover must be readable in their textbook algorithmic structure.**

The design note [“The language takes responsibility for quantum bookkeeping”](docs/quantum-bookkeeping.md) connects this principle to ownership, auxiliary cleanup, control, and phase checks. It proposes QPE → amplitude amplification → Shor as language-design test cases.

The minimum foundation is that **v0.1 must compose and reuse semantic contracts `U E_in = E_out u` and independently check them through actual IR**. Different implementations of the same contract must be interchangeable without changing their client, while preserving phase, ownership, and exact auxiliary zero return.

For v1, preparation, oracles, reflections, controlled powers, phase estimation, and order reconstruction must be assembled from shared components and parameters. Evaluation uses three algorithms that actually compile, verify, and execute; fixed-size examples or pseudocode alone do not suffice. The [release milestones](docs/release-milestones.md) are authoritative; this section summarizes them. **The declared finite v0.1 profile is implemented and tested; v1 is not achieved.** These milestones are distinct from the crate version and completion of a general compiler proof.

**Before v0.2.0, write ideal code in imaginary Qleisli 1.0.** The prerequisite covers QPE, Grover, amplitude estimation, Shor, quantum walk, and QSVT: express their structure in code even before it compiles, and identify semantic contracts, capabilities, and unresolved questions before generalization, new feature implementation, or release. The [six initial drafts, contracts, and requirements index](docs/imaginary-v1/README.md), with their review, satisfy the [prerequisite](docs/release-milestones.md#pre-v020-imaginary-v1-code) of having initial code and requirement records. The drafts' general syntax and APIs remain exploratory; the selected fixed-width M1 subset now has a separate future specification. The imaginary code is revisable design material, not evidence of executable v1 completion.

<a id="現在の優先順位-言語仕様"></a>

<a id="現在の優先順位-v01の言語仕様と意味契約"></a>

## Current priority: the v0.1 language specification and semantic contracts

The [finite semantic-contract path](docs/semantic-contracts-v0.1.md) is implemented. An independent exact-arithmetic checker connects to `with_computed(q,f,u){|d,a| body}`, which states the logical action explicitly. It checks a phase oracle, auxiliary H;H, and simultaneous data/auxiliary X using the same rule. At [function boundaries](docs/function-contracts-v0.1.md), `apply_contract(implementation,specification,input)` lets a client demand meaning and retains checked evidence in final IR after adjoints, control, and repetition. A bundled [implementation-substitution example](examples/function_contracts/README.md) is executable. The [conformance ledger](docs/specification-status.md) records the evidence and remaining trust boundaries.

Work continues on **Stage 1 language rules and IR correspondence**, the foundation of v0.1. The [resource rules R1](docs/source-resource-rules.md), [type/effect/name/scope rules](docs/source-typing-rules.md), [local source semantics](docs/source-semantics.md), and [static-transformation proofs](docs/static-semantics.md) support the [paper proofs Q1–Q3 for the explicitly stated mathematical rules](docs/source-soundness.md). They concern isometry/unitarity of pure operations and complete positivity with trace preservation after summing outcomes for observation and adaptive composition.

Alongside the ownership model, five lemmas on composition of Kraus completeness are [checked in Lean](docs/lean-resource-proof.md). Lean supports the required local lemmas. The [conformance record](docs/specification-status.md) records implementation audits and regressions. Correspondence between the mathematical rules and every accepted Rust path, and general source-to-IR semantic preservation, remain unproved. The finite v0.1 semantic contracts and evidence checker connect to this foundation; sized types, operation parameters, algorithms, and the required standard library are generalized afterward toward v1.

The [source-to-IR contracts C1–C5](docs/source-ir-correspondence.md) specify basis-table encoding, primitive operations, auxiliary evidence, and complete φ mappings. Their mathematical translation has a conditional paper proof of semantic preservation, composing existing local proofs. A general proof that all successful Rust paths meet these contracts remains open.

For [scope-exit refinement](docs/lowering-state-refinement.md), Rust environment projection was extracted into an independent function. A Lean model with the same case split proves restoration of classical bindings, non-resurrection of consumed bindings, and preservation of quantum ownership. A finite model of rebinding identity and source regressions provide further checks. Correspondence for all paths reaching the block and their implicit frames remains future work.

Review revisions implemented product patterns in `do (a,b) <- q; pure (a,a xor b)` and ordinary-expression `true` and `false : CBit`, `not`, `and`, and `xor`. Classical operations evaluate both operands from left to right, preserving quantum ownership and effects. `true` and `false` became reserved words. See the [revision and validation record](docs/specification-status.md).

<a id="第1開発目標-ai時代の量子言語"></a>

## Development goal 1: a quantum language for the AI era

AI-generated and human-written code pass through the same type/effect/ownership checks and IR verification. The aim is resource safety first, then quantum-operation soundness in ideal semantics. Protocol correctness, algorithm correctness, and hardware behavior are separate verification targets. The [development goal](docs/ai-era-goal.md) states assumptions and acceptance criteria.

<a id="第2開発目標-量子アルゴリズムの構造化"></a>

## Development goal 2: structuring quantum algorithms

Ask what quantum algorithms are built from and establish a cycle of **existing algorithms → common structures → language abstractions → new algorithms**. Connect reversible computation, reflections, controlled powers, finite iteration, observables, and classical feedback to contracts for types, ownership, effects, and evidence.

The [initial 20-entry corpus](docs/algorithm-corpus.md) and [design contracts and acceptance criteria](docs/algorithm-structure-goal.md) are documented. The first five routines and fixed-width QFT2/3 are bundled as ordinary `.qli` definitions. [Fixed-width arithmetic, order finding for N=15, and classical factor extraction](docs/arithmetic-order-finding.md) are also implemented. Higher-order combinators, a strict monad structure, general QPE and Shor, and VQE/QAOA remain future work.

<a id="第3層の将来計画-量子アルゴリズムの標準語彙"></a>

## Future layer 3: a standard vocabulary for quantum algorithms

Building on the verification foundation of layer 1 and the structure extraction of layer 2, develop algorithmic concepts into a **standard library with semantic contracts**. Its seven areas are primitives, structural combinators, quantum data structures, arithmetic, transforms, algorithm skeletons, and hybrid plans.

The [library roadmap](docs/stdlib-roadmap.md) records proposed contracts for `amplify`, `phase_estimate`, `simulate`, and `estimate`, standard-adoption criteria, verification paths for AI-proposed patterns, and prerequisites for implementation. The [contract ledger v1](docs/stdlib-contracts.md) covers twelve bundled public definitions; finite static operations are implemented. Generalized algorithm-skeleton APIs are not implemented.

<a id="設計の境界"></a>

## Design boundaries

- The free-vector-space monad motivates coherent computation mathematically. Program composition that tracks resources and effects is Kleisli-inspired; arbitrary `bind` is not exposed as a safe execution API.
- `Q<A>` is ownership of operations on a quantum register. It is linear under every effect, with no implicit discard. Sharing basis indices is allowed when the whole map is isometric.
- Measurement, reset, and discard belong to `observe`. Initial measurement consumes the quantum handle and returns only a classical result. Pure auxiliary release requires static zero-return evidence for every input.
- An [open central problem](docs/design-philosophy.md) is how ownership-based control of operations composes with evidence about the entangled global system.
- Rust borrowing provides memory safety for the implementation. A dedicated Qleisli frontend and IR verifier check Qleisli ownership, effects, and constructor premises. General correctness of those checkers is a separate proof obligation.

<a id="文書"></a>

## Documentation

The [documentation map](docs/documentation-map.md) records authority, status, and the English translation inventory.

1. [Design philosophy](docs/design-philosophy.md): fixed principles and remaining freedom in syntax.
2. [A quantum language for the AI era](docs/ai-era-goal.md): assurance levels and proof targets.
3. [Roadmap](ROADMAP.md) and [v0.x release plan](docs/v0x-roadmap.md): stages, ordering, completion conditions, and the v0.1.9 maintenance boundary.
4. [Quantum-language requirements](docs/quantum-language-requirements.md): conditions for the specification and implementation.
5. [`.qli` and the standard library](docs/standard-library.md): Stage 0 organization decisions.
6. [Finite-core language specification v0](docs/language-spec.md): normative types, effects, ownership, and semantics.
7. [Formal core](docs/formal-core.md): theorem statements, constructor semantics, and open proof obligations.
8. [Syntax v0](docs/syntax-v0.md): normative grammar, names and scopes, and static rejection examples.
9. [Rust IR prototype](docs/ir-prototype.md): implemented checks, trust boundaries, and unachieved guarantees.
10. [Finite-IR paper proof](docs/finite-core-proof.md): current constructor semantics and implementation correspondence obligations.
11. [Initial `.qli` frontend](docs/frontend-v0.md): executable subset, checks, diagnostics, and examples.
12. [Structuring quantum algorithms](docs/algorithm-structure-goal.md): common structures, type/composition contracts, and implementation order.
13. [Algorithm corpus](docs/algorithm-corpus.md): twenty entries with primary sources, input models, premises, and unsupported parts.
14. [Finite algorithm routines](docs/algorithm-routines.md): bundled APIs, three structured examples, equations, and tests.
15. [Standard-library roadmap](docs/stdlib-roadmap.md): seven areas, semantic contracts, adoption, maintenance, and feedback into AI exploration.
16. [Finite static operations and QPE](docs/static-operations.md): adjoints, control, repetition, finite IR, and fixed-width QFT/QPE validation.
17. [Bundled contract ledger](docs/stdlib-contracts.md): status, premises, meaning, IR, cost, and evidence for twelve public definitions.
18. [Finite arithmetic and order finding](docs/arithmetic-order-finding.md): full-space reversible operations, N=15, classical reconstruction, and retries.
19. [Specification conformance](docs/specification-status.md): decisions, implementation limits, evidence, and open proofs; historical entries retain their original language.
20. [Source resource rules](docs/source-resource-rules.md): mixed values, pending results, function frames, φ, resource invariant R1, and implementation audit.
21. [Lean resource and Kraus proof ledger](docs/lean-resource-proof.md): checked ownership model and local matrix lemmas, premises, omissions, and reproduction.
22. [Source semantics](docs/source-semantics.md): mixed values, evaluated-value substitution, correlated frames, local φ proofs, and IR correspondence.
23. [Static semantics](docs/static-semantics.md): paper proofs for flattening, axis order, adjoints, control, repetition, and restricted auxiliary phases; Rust correspondence and exact-matrix regressions.
24. [Type/effect/name/scope inference rules](docs/source-typing-rules.md): all AST constructors, basis totality, binding projection, declared effects, and implementation obligations.
25. [Ideal soundness of the source rules](docs/source-soundness.md): paper proofs Q1–Q3 for purity, isometry/unitarity, observation, adaptive composition, hidden histories, and reference systems.
26. [Implementation architecture](docs/implementation-architecture.md): module dependencies, verification boundaries, lowering invariants, and links between specification, implementation, and regressions.
27. [Terminology and notation](docs/terminology.md): English authority, supporting material, ownership, frames, protected scopes, and quantum-state notation.
28. [Source-to-IR correspondence](docs/source-ir-correspondence.md): basis encoding, primitives, auxiliary evidence, complete φ, conditional preservation C1–C5, and Rust/verifier obligations.
29. [Lowering-state refinement](docs/lowering-state-refinement.md): value/environment/register relations, scope-projection Lean theorems, and remaining input/move/binding/call/branch premises.
30. [Release milestones and north star](docs/release-milestones.md): v0.1 semantic contracts and independent checks; executable textbook structure for Shor, QPE, and Grover in v1.
31. [Finite semantic contracts](docs/semantic-contracts-v0.1.md) and [function boundaries](docs/function-contracts-v0.1.md): exact operator equality, auxiliary zero return, public meaning and implementation correspondence, and evidence reuse in final IR.
32. [Language-evolution framework](docs/language-evolution.md) and [six imaginary v1 drafts](docs/imaginary-v1/README.md): current/future boundary, common requirements, and semantic review.

<a id="rust-開発環境"></a>

## Rust development environment

Use **Rust 1.85 or later** with Rust 2024 edition, Cargo, rustfmt, and Clippy. The crate currently has no external dependencies. From the repository root:

```sh
cargo test --all-targets
cargo fmt --check
cargo clippy --all-targets -- -D warnings
python3 scripts/check_docs.py
python3 scripts/test_check_docs.py
```

`Cargo.lock` and `target/` are generated and excluded from Git. Tests cover parsing, module resolution, source compilation, IR verification, and reference simulation. Agreement between compiled finite examples and numerical execution is not a general soundness proof.

The separate [Lean proof environment](lean/README.md) uses Lean/Mathlib 4.30.0
without a required Physlib dependency. The [dependency decision](docs/physlib-environment.md)
retains Physlib as a future candidate for the instrument/CPTP bridge, with
explicit reintroduction and audit conditions.

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/phase_oracle
cargo run --bin qleisli -- run examples/feedback
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo run --bin qleisli -- run examples/phase_estimation
cargo run --bin qleisli -- run examples/order_finding
cargo run --example shor15
```

CLI bit strings follow the returned classical tuple from left to right. The phase-estimation example returns its phase register least-significant bit first, so `100` denotes integer 1. Probabilities are floating-point approximations, including tiny positive values caused by rounding. See the [output-order and numerical-execution conventions](docs/frontend-v0.md).

Stage 0 organization and the normative finite core v0 are specified. Stage 1 proofs and implementation correspondence remain the priority. External package management and hardware-specific APIs are outside the initial scope.

## License and contributions

Copyright 2026 Masahiko G. Yamada.

Unless otherwise stated in an individual file, Qleisli's own source code,
standard library, examples, tests, scripts, Lean proofs, and documentation
are licensed under the [Apache License, Version 2.0](LICENSE).
See [NOTICE](NOTICE) and the [contribution policy](CONTRIBUTING.md).
Third-party material and dependencies retain their own licenses and notices.
This license covers Qleisli's files; it does not purport to license independently
authored programs merely because they are written in or compiled with Qleisli.
