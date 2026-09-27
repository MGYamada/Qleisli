<a id="量子の帳尻は言語が引き受ける"></a>

# Quantum bookkeeping is a language responsibility

Status: **design note organizing a user-provided design argument**
(2026-09-27). This authoritative English edition of the note replaces its
Japanese edition without adopting new syntax or APIs. It restates the existing
[design principles](design-philosophy.md) and north star from the algorithm
author's perspective. The sequence of design evaluations beginning with QPE
remains a proposal for progressing from the finite v0.1 contract foundation
toward v1.

The [finite core specification](language-spec.md) and
[release milestones](release-milestones.md) remain authoritative for normative
language rules and release acceptance. This note supports those documents;
it does not declare a new grammar, API decision, or completed implementation.

<a id="中心となる原理"></a>

## The central principle

> **Quantum bookkeeping is a language responsibility.**

Algorithm authors describe the intended meaning and structure. The language
and implementation take responsibility for transferring quantum resources
correctly and translating that meaning into a circuit that preserves it.

The strength to develop in Qleisli is consistency: the necessary facilities
and checks should follow from a common principle, rather than from the number
of individual features.

| Bookkeeping responsibility | Obligation of the language and implementation |
| --- | --- |
| Qubit ownership and linearity | Transfer each operation right exactly once; reject copying, repeated use, and implicit discard. |
| Creating and reclaiming auxiliary qubits | Manage auxiliary regions and require evidence of zero return and separation for pure reclamation. |
| Reversible computation and uncomputation | Track the computed relation and the logical operation returned, and construct justified uncomputation. |
| Coherent control and powers | Check required operation-access capabilities, inputs/outputs, effects, and auxiliary cleanup. |
| Global and relative phase | Retain operator phase so meaning survives contexts that use coherent control. |
| Resources and effects | Distinguish pure operations, preparation, and observation, retaining the distinction under composition. |
| Circuit translation | Bind the algorithm's required meaning to checkable contracts for its implementation and final IR. |
| Static checks and tests | State the conditions explicitly and make acceptance/rejection cases and phase-sensitive/reference-sensitive checks reproducible. |

This division of responsibility expresses the north star: make the language
people use to think about quantum algorithms coincide with the language they
use to write programs.

Authors specify the required logical operation, input premises, available
operation capabilities, accuracy, and failure conditions. The implementation
checks that the circuit realizes that contract and reports a diagnostic when
it cannot establish the conditions. This does not promise fully automatic
proof search or that the language eliminates hardware noise. The existing
[v0.1 semantic contracts](semantic-contracts-v0.1.md) and
[function-boundary evidence](function-contracts-v0.1.md) realize this
responsibility within a finite foundation.

<a id="qpeを最初の本格的な試金石にする理由"></a>

## Why QPE is the first substantial design test

Writing QPE in its textbook structure brings state preparation, controlled
powers, inverse QFT, measurement, phase interpretation, and register ownership
into one program. It therefore tests whether the language's abstractions can
express the required meaning, beyond demonstrating individual features.

For a finite-dimensional unitary U and a normalized eigenstate, let
`U|ψ⟩ = exp(2πiφ)|ψ⟩` with `0 ≤ φ < 1`. With a t-bit phase register and
`N = 2^t`, preparation and controlled powers have the following form:

```text
|0⟩^⊗t |ψ⟩
  → (1/√N) ∑_{k=0}^{N−1} |k⟩ |ψ⟩
  → (1/√N) ∑_{k=0}^{N−1} exp(2πikφ) |k⟩ |ψ⟩.
```

Here `k = ∑_j 2^j k_j`, and bit j controls `U^(2^j)`. Inverse QFT and
measurement follow. If `Nφ` is integral, the ideal outcome is that integer;
otherwise the result follows a finite-precision phase-estimation distribution.
For general inputs, the contract also includes the distribution over
eigencomponents and the postmeasurement target/reference state. Explicitly
relate the displayed register order to the implementation's bit and axis order.

The expression `controlled(U^(2^j))` is a particularly useful design test.
Authors should be able to express phase estimation and controlled powers as
components with those meanings, without rebuilding gate sequences and
auxiliary wiring on every use.

The following is **pseudonotation for a future design**, not current `.qli`
syntax or an implemented public API:

```text
phase_estimate(U, psi)
controlled(power(U, 2^j))
```

An actual contract also needs precision t, required access capabilities, and
input/output ownership. Merely writing `U:A→A` does not imply that controlled
access exists. In addition to pure unitarity, require a checked controlled
construction from a known circuit or explicitly supplied controlled-operation
access. The ability to call an unknown black box alone does not grant that
capability. Any private auxiliary region's exact cleanup and phase must also
connect to the public operation contract.

<a id="制御化が位相の意味を露出させる"></a>

## Coherent control exposes the meaning of phase

On density operators of the same system without coherent control, U and
`exp(iθ)U` induce the same map:

```text
(exp(iθ)U) ρ (exp(iθ)U)† = UρU†.
```

Their controlled operators differ:

```text
ctrl(U)          = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U
ctrl(exp(iθ)U)   = |0⟩⟨0| ⊗ I + exp(iθ)|1⟩⟨1| ⊗ U.
```

**The target operation's global phase becomes relative phase between the two
control branches.** For U=I and θ=π, for example, the first operator preserves
a control in `|+⟩`, whereas the second changes it to `|−⟩`. Operations intended
for reuse under coherent control therefore cannot be identified merely up to
global phase.

QPE exposes this difference in its estimates. It directly tests what the
language considers equivalent quantum programs and the contexts in which it
permits transformations. This is also why the current semantic contracts
require the phase-sensitive operator equation `U E_in = E_out u`.

<a id="アルゴリズムで言語設計を順番に検証する"></a>

## Evaluate language design through successive algorithms

**Writing imaginary Qleisli 1.0 code first is an adopted prerequisite before
v0.2.0.** Following the [authoritative condition](release-milestones.md#pre-v020-imaginary-v1-code),
first assemble drafts and semantic requirements/open questions for QPE, Grover,
amplitude estimation, Shor, quantum walk, and QSVT. They need not compile and
remain revisable. The [six initial drafts and requirement index](imaginary-v1/README.md)
and [semantic review](imaginary-v1/review.md) now satisfy the limited
prerequisite of having those artifacts and requirements. They are not evidence
of implementation or v1 completion.

After that prerequisite, the proposed order for deepening implementation and
contracts is:

> **QPE → amplitude amplification → Shor**

| Design test | Principal abstractions to evaluate |
| --- | --- |
| QPE | Coherent control, powers, phase semantics, QFT, measurement, register ownership, and operation-access capabilities. |
| Amplitude amplification, including Grover | State preparation and its inverse, oracles, reflection signs and phases, iteration policies, and success-probability premises. |
| Shor | Shared QPE reuse, reversible modular arithmetic, reversible classical computation, auxiliary regions, classical order/factor validation, failure, and retries. |

This approach uses algorithms to **test the semantics of the quantum language
in sequence**, as well as implementing the algorithms themselves. Use QPE as
an early acceptance test in 0.x design iterations, then reuse the resulting
abstractions in the next example. Formal v1 acceptance still evaluates all
three algorithms against V1-C1–C5 in the authoritative release document.

For QPE, the goal is to align the mathematical stages found in textbooks and
papers with code that can actually compile, pass checks, and run. Fixed-size
circuits or a top-level function bearing only the algorithm's name do not
adequately evaluate that abstraction.

<a id="余計な帳尻合わせが現れたときの問い"></a>

## When authors still have to manage bookkeeping

If writing an algorithm repeatedly requires exposing wiring or reclamation
steps, first ask:

> **Why can the language not take responsibility for this?**

Is the missing element an ownership representation, an operation-access
capability, a semantic contract, or a connection between implementation and
evidence? Hiding the steps inside a function is not sufficient by itself;
check whether the client can compose that function using its meaning and
required premises.

Ordinary library definitions are an important implementation mechanism for
this purpose. Shared structures need not all become sealed operations. The
language must support checking library components and their composition
through types, effects, ownership, and semantic contracts.

Derive design requirements from quantum-algorithm structure and validity
conditions rather than starting with feature-count comparisons to other
languages. Use prior research to assess meanings and verification methods.
After the six ideal-code drafts are assembled, deepen QPE's implementation
and contracts to identify the next necessary abstractions.

The direction expressed by this note is **from a language for writing quantum
circuits toward a language for writing quantum algorithms**. Evaluate that
progress through both readable real source and checkable meaning preserved
through implementation.
