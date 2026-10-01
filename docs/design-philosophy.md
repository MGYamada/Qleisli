<a id="qleisli-の設計思想"></a>

# Qleisli design principles

Adopted principles, 2026-09-26–30. English is authoritative. The north star is to make the language used to think about quantum algorithms coincide with executable source. [Language v0](language-spec.md) fixes present rules; [milestones](release-milestones.md) fix acceptance gates. Adoption, implementation, tests and proof are separate.

## Standard library as foundation, textbook and formal specification

Build a BLAS/LAPACK-like foundation combining reusable components, quantum-information teaching and formal specifications. Connect concepts, derivations, readable source, examples and explicit proof status. Until v0.5, add algorithms to corpus; then grow stdlib as a mathlib-style community library under [STDLIB.md](../STDLIB.md). A comprehensive hierarchy is still open.

## Follow Rust for type and ownership discipline

When uncertain about type identity, tuple arity/nesting, moves, bindings or scopes, follow Rust. A difference must state its quantum/evidence obligation and checking rule. Keep quantum linearity, explicit discard and proved clean release. [Types](type-system.md) and [linear sizes](size-expressions.md) specify the adopted differences; unspecified Rust features are not implicit Qleisli APIs.

## Start with the quantum programs we want to write

Write desired quantum source first, retain an executable finite translation and use concrete gaps to choose a bounded extension. Preserve first attempts, real diagnostics and semantic counterexamples. State the removed author obligation, replacement evidence and independent checker before changing acceptance. [Corpus](../corpus/README.md) translations and [imaginary drafts](imaginary-v1/README.md) have distinct roles; neither authoring success nor attractive notation bypasses verification.

## Resource semantics as a first-class account

The [Resource Safety Theorem](resource-semantics.md) is a third v1 pillar, still to prove. Bound actual execution under declared cost models and preserve those bounds through compilation. Peak live space, additive work, shared representation and repeated execution differ; budgets and ownership alone prove no quantitative bound.

## Keep the trusted core small

Convenience belongs in untrusted [desugaring](terminology.md#desugaring-layer): meaning-preserving translation to already specified operations with explicit ownership/effects. It introduces no primitive meaning or acceptance rule. A new checker rule needs an irreducible semantic/evidence obligation. Valid output IR alone does not prove source preservation. Maintain the [producer/debt inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary); remove public support only through versioned migration. Moving files or sharing numerical code does not shrink acceptance trust. Keep the fixed [partition](../TRUST_BOUNDARY.md) and independent checks at every [pipeline boundary](lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary).

<a id="1-量子データは所有される資源"></a>

## 1. Quantum data consists of owned resources

`Q<A>` is the linear right to operate on ordered logical wires, not a copyable state vector. Reject duplicated owners and implicit discard. Basis information may be coherently copied by an injective lift; arbitrary unknown states may not. Split owners may remain entangled. Pure auxiliary release needs exact zero return and separation for every input/reference.

<a id="2-プログラムは資源の効果付き変換"></a>

## 2. Programs are effectful transformations of resources

Effects obey `Unitary <= Iso <= Observe`. Returned mixed values, surviving environments and pending/caller frames form the complete quantum interface; a residual environment alone is insufficient. Coherent classical outputs depend only on classical inputs. Measurement ends logical ownership; a later initializer creates a fresh wire even if a backend reuses hardware.

```text
(classical input A; quantum context Δin) -[effect ε]->
    (classical output B; quantum context Δout)
```

| Operation | Ownership transition | Effect and meaning |
| --- | --- | --- |
| `init0` | `∅ -> {q}` | An isometry preparing the known state `\|0⟩`. |
| `h` | `{q} -> {q}` | A unitary. |
| `measure_z` | `{q} -> ∅`, with a `CBit` result | A quantum instrument returning the measurement outcome and consuming the logical wire. |
| `discard` | `{q} -> ∅` | An observation effect taking a partial trace. |

<a id="3-合成は-kleisli-的に行う"></a>

## 3. Composition follows a Kleisli-style principle

Compose compatible type/ownership interfaces and join effects. Kleisli-style composition motivates the project name; a strict indexed-monad structure is unproved. Unrestricted free-vector-space bind can identify orthogonal inputs and is not an execution API. Adaptive observation composes quantum instruments by summing hidden classical histories.

```text
(A; Δ0) -[ε1]-> (B; Δ1)
(B; Δ1) -[ε2]-> (C; Δ2)
--------------------------------
(A; Δ0) -[ε1 ∨ ε2]-> (C; Δ2)
```

<a id="4-古典と量子は型レベルで非対称"></a>

## 4. Classical and quantum data are asymmetric at the type level

Copyable classical information and owned quantum resources have different rules. Basis labels are distinct from measured `CBit`; noninjective basis maps cannot be lifted as pure operations. [Types](type-system.md) specify structural equality and explicit reshape.

<a id="5-純粋関数型の意味"></a>

## 5. Meaning of purely functional

Top-level declarations perform no quantum operations when loaded and contain no implicit mutable quantum state or I/O. Pure functions are total and terminating in the finite core. Explicit observation accounts for probability; host display, files and device I/O remain outside the language effect.

<a id="未解決の中核課題-所有権とエンタングルメントの分離"></a>

## Open central issue: separating ownership from entanglement

Ownership separation does not imply state separation. Local gates, partial measurement/discard/reset and function boundaries must act on the correlated whole system and arbitrary references. General entanglement inference is not required, but zero-release evidence and whole-system semantics are. [Formal obligations](formal-core.md) remain open for the actual complete implementation.

<a id="添付議論からの用語の確定"></a>

## Terminology adopted from the supplied discussion

[Terminology](terminology.md) distinguishes desugaring, source checking, evidence generation, acceptance and post-verification execution. Isometry does not grant an inverse or controlled implementation. A Clean name or lifetime is not zero-return evidence.

| Expression in the supplied discussion | Adopted Qleisli interpretation |
| --- | --- |
| `Qubit` or `Q<A>` | The source ownership type `Q<A>`, not a state vector itself. |
| The outer `Q` in `Q(Qubit)` | A computation-effect concept. Express it using the effectful transformations above rather than stacking the same `Q` on the ownership type `Q<A>`. |
| “It is affine, so it may be discarded” | Physical discard is possible. Pure code has no implicit discard; irreversible discard is explicit. |
| “Quantum operations are not ordinary functions” | A linear signature such as `Q<Bit> -> Q<Bit>` is valid. Its input is not interpreted as a copyable state value. |
| “Transformations are first-class” | Transformations are central to the semantics. First-class operation values and general higher-order functions are not requirements of the initial version. |
