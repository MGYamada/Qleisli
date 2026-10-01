<a id="第1開発目標-ai時代の量子言語"></a>

# Development goal 1: a quantum language for the AI era

Adopted goal: human and AI source use identical type/effect/ownership and independent IR checks. Diagnostics expose failing obligations and locations. An explanation, author identity or proposed certificate has no authority. [Design](design-philosophy.md) and [current status](current-status.md) separate intended guarantees from actual results.

<a id="v01-と-v1-の到達条件"></a>

## v0.1 and v1 acceptance conditions

The finite v0.1 SC/FC path is implemented and validated under its bounded [contracts](semantic-contracts-v0.1.md). General v1 source and implementation theorems remain open. Six [imaginary drafts](imaginary-v1/README.md) satisfy only the initial-design prerequisite. See [release criteria](release-milestones.md).

<a id="保証の階層"></a>

## Levels of guarantees

Keep ownership safety, ideal quantum soundness, protocol correctness and algorithm success separate. The quantitative [Resource Safety](resource-semantics.md) target also needs actual execution and compilation bounds; it does not follow from linear ownership.

| Level | Intended guarantee | Checking boundary |
| --- | --- | --- |
| 1. Resource safety | Reject operations on unowned wires, repeated use of the same ownership, reuse of a measured handle, unhandled quantum ownership, and protected-region conflicts. Conflict checking for general borrowing is a goal for future signatures and syntax. | Type, effect, and ownership checking, with IR linear-token verification. |
| 2. Quantum soundness in ideal semantics | Pure `iso` operations are isometries, `unitary` operations are unitaries, and programs containing observation denote valid quantum instruments. | Sealed primitive meanings, injective lifts, phase, separation evidence, effectful composition, and verification of IR semantics. |
| 3. Protocol correctness | For example, a teleportation output preserves the input's quantum information. | A protocol-specific specification and additional proof obligations; basic types do not automatically establish this property. |
| 4. Algorithm correctness | Produce the intended answers or satisfy the required success probability. | Algorithm-specific mathematical proof, analysis, and validation; type checking alone is insufficient. |

<a id="目指す健全性定理"></a>

## Intended soundness theorem

For the finite terminating mathematical rule system, sealed primitive meanings, injective lifts, certified cleanup and valid composition imply an instrument: each outcome map is CP and trace non-increasing, their sum TP, with arbitrary references. Pure Iso has V†V=I; Unitary also VV†=I. Closed main denotes a normalized classical distribution. This is an ideal-semantics statement; transfer to actual Rust checking/lowering and physical execution remains open. [Formal core](formal-core.md) records scope and current component proofs.

```text
Γ ; Δin ⊢ P : B ; Δout ! ε
```

<a id="ai-を含む開発の流れ"></a>

## Development workflow involving AI

Propose source and independent meaning; frontend-check and lower it; independently verify raw IR/evidence; then execute the accepted artifact under the backend capability contract. Preserve initial sources and real repair observations under the [session procedure](../tests/fixtures/authoring_sessions/README.md).

<a id="到達判定"></a>

## Acceptance criteria for this goal

Specify acceptance/rejection and full correlated-system meanings, prove actual checker acceptance, and bind source/IR/backend translations before claiming compile-time soundness. Bell/phase/feedback tests supplement proofs. [QWIRE](https://arxiv.org/abs/1803.00699) and [Proto-Quipper](https://arxiv.org/abs/1812.03624) are prior work, not Qleisli implementation evidence.
