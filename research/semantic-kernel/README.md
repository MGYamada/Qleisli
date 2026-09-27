# Symbolic semantic-contract prototype

Status: **independent research implementation for the v0.1.3 goal**.
This package has `publish=false`; its Rust data structures are experimental,
not new public Qleisli language or compiler APIs. The
[system design](../../docs/symbolic-contract-architecture.md) governs the
meaning/implementation boundary and distinguishes the initial subset from
production integration. Qleisli's Apache-2.0 license and
[attribution](../../NOTICE) apply. Copyright 2026 Masahiko G. Yamada.

The [v0.1.5 decision](../../docs/decisions/2026-09-27-v1-path.md) selects a
bounded M2 continuation, replacing indefinite deferral. The existing prototype
and regression suite are retained unchanged. Hierarchical IR, schema import,
source integration and their validation are planned, not implemented here;
new development belongs outside the compatible 0.1.x maintenance scope.
M2 is a milestone, not a selected product version or release date.

## Purpose

Given an implementation U, isometric encodings Ei/Eo and a separately required
logical operation u, check `U Ei=Eo u` without expanding a whole composite
operator into a dense matrix. The term graph, proof graph and required root
are explicit inputs. The client fixes a `RequiredContract` snapshot before
asking an untrusted producer for a proof. The producer can extend its graph,
but cannot change the fixed meaning behind its IDs. A client that adopts a
provider's self-selected requirement has not independently specified the task.

The package consists of a [kernel](src/kernel.rs) and a separate
[raw-IR adapter](src/adapter.rs). The kernel checks type/term/proof DAGs and
derives conclusions. The adapter binds such a conclusion to actual supported
Qleisli raw IR through ordinary resource verification and independent ordered
extraction. It does not call frontend flattening or the old whole-function
matrix comparator. Bounded leaf arithmetic and the raw resource verifier are
shared trusted implementation components, not independently proved code.

## Initial semantics

Types retain `Unit`, `Bit` and binary products, with the low-left tensor order.
Semantic terms distinguish known unitaries from preparation isometries and
include fixed phase-sensitive gates, identity, composition, tensor, zero
insertion, qualified adjoint, coherent control and finite `u64` repetition. Encodings are terms, not
dense global matrices. Explicit layout terms preserve output coordinates.

Raw proof nodes use bounded exact leaves and algebraic rules. The sequence
rule matches the same intermediate typed encoding. Adjoint requires logical
and physical unitarity; control requires the same entry and exit encoding.
Node references are acyclic and checked; unsupported rules and exhausted
budgets do not issue evidence. The checker derives its conclusion and compares
it with the independently supplied expected contract and implementation root.

The motivating example is the fixed logical Z contract, implemented directly
or by `CNOT(data,aux); Z(aux); CNOT(data,aux)` with the zero encoding
`E0|x>=|x,0>`. This encoded theorem applies to arbitrary references. It does
**not** authorize dropping arbitrary runtime auxiliary ownership: this
package does not yet connect a new fresh-zero/release rule to compiled source
or execution. The existing finite compiler remains responsible for its own
released cleanup path.

Dense exact arithmetic is allowed only within the explicit leaf width/work
limits. Structural composition and large identity frames must preserve those
limits without materializing the global matrix. Term/proof statistics and
rejection tests expose that distinction. General symbolic equivalence and
proof search are not implemented as a hidden simplification oracle.

## Boundaries

- Raw IR preserves ordered physical axes and ownership, but not the complete
  original source type tree. The adapter cannot reconstruct erased source
  semantics or prove that the frontend lowered a particular declaration.
- Unsupported raw operations, effects and legacy evidence constructors fail
  explicitly. No unsupported operation is treated as identity.
- A bound result refers to its exact raw snapshot and required contract.
  Mutating an operation, control, wire order or final interface requires
  fresh checking. A function name or digest does not establish correspondence.
- The prototype establishes operator equations. It provides no new execution,
  cleanup, device-control or portable serialized-proof authority.
- Block contracts, instruments, arbitrary angles, approximation, arithmetic
  families, source size/operation parameters and complete algorithms remain
  future work. Existing finite examples do not discharge these obligations.

## Reproduction

From the repository root:

```sh
cargo fmt --manifest-path research/semantic-kernel/Cargo.toml --check
cargo test --manifest-path research/semantic-kernel/Cargo.toml --all-targets
cargo clippy --manifest-path research/semantic-kernel/Cargo.toml --all-targets -- -D warnings
```

Run the production Rust regressions separately with `cargo test --all-targets`.
The primary and MSRV CI jobs run both packages. The Lean build and axiom audit
include [SemanticContract.lean](../../lean/Qleisli/SemanticContract.lean);
the [theorem ledger](../../docs/lean-resource-proof.md) states its premises and
scope. Rule-level Lean proofs are not a mechanized refinement proof of this
Rust implementation.

## Validation record

The initial implementation has **43 tests**: 25 kernel and 18 adapter tests.
They cover exact equations, wrong phase and encoding, invalid adjoint/control,
zero-count validation, arbitrary-reference frames, shared DAGs, malformed
graphs, budgets, changed IR, ownership, and layout. The
[release record](../../docs/releases/v0.1.3.md) records toolchain validation.

One permanent differential test covers **5,425 cases**, comparing the new
adapter's bounded denotation with the existing independent `Circuit::matrix`
path. It enumerates one-bit phases/permutations, Hadamards, scalar phases,
ordered CNOT axes and mixed positive/negative controls. That old evaluator is
used only as a small test oracle; the production adapter does not call it.
Additional regressions freeze a requirement before mutating both sides from
Z to X at the same IDs, reject incomplete snapshots, and permit safe graph
extension. Non-Hermitian T/control/adjoint/repetition is checked against an
explicit diagonal oracle, including rejection of the wrong adjoint phase.

Concrete scaling regressions:

- An actual 128-bit raw program applies Z to the first physical bit. Its proof
  fixes the required logical Z independently, uses one 1-bit exact leaf, and
  tensors a symbolic identity on the other 127 bits. The test asserts maximum
  dense matrix dimension **2**, and binds the proof to the complete raw IR.
- Actual 128-bit raw identity needs **zero exact leaves**. Separate kernel
  tests extend the encoded auxiliary example with 64/128 reference bits;
  the largest matrix dimension remains **4**.
- Forty shared sequential-composition levels describe exponentially many
  repeated applications while checking a linear proof DAG and one exact leaf.
  This measures proof checking, not execution time or general proof search.

The adapter supports `Gate`, `Cnot`, `Toffoli`, `Split`, `Join`, and restricted
`ApplyUnitary`: Hadamard steps, scalar phase on zero target axes, arbitrary
one-bit monomials, and the canonical phase-free two-bit CNOT table. Explicit
positive/negative controls and output transports preserve phase and ordering.
Other monomial tables, legacy contracts, allocation, cleanup, observations,
host effects and other unsupported operations are rejected explicitly.
Canonical physical types retain all axes but do not recover erased source
type trees; zero-width ownership stays in the checked raw snapshot.

| Boundary | Initial limit |
| --- | --- |
| Exact leaf | Every reachable intermediate input/output has at most 3 bits (matrix dimension at most 8). |
| Default kernel | 4,096-bit width; 8,192 type nodes; 65,536 term nodes; 65,536 proof nodes; 20,000,000 charged work units. |
| Raw import | 4,096 total physical bits and quantum input ports; 10,000 raw operations and circuit steps; 1,000,000 estimated transport work units; existing raw per-register limits still apply. |

Limits reject with diagnostics; they are not a complexity or wall-clock
guarantee. Node interning and graph retention avoid recursive expansion.
The checked result reports nodes, exact leaves, operator evaluations, largest
matrix dimension, exact work and total charged work. Matching is structural;
there is no general interchange/association/conversion proof constructor.

Lean separately proves **20 general semantic lemmas**. Its derivation theorem
covers common-encoding identity/sequence/qualified adjoint, conditional on leaf
soundness; tensor and control have separate theorems. Rust repetition and the
full Rust term/proof calculus are not covered by that induction. Leaf
interpretation, adapter adequacy, checker correctness, source lowering and
entry/release integration remain open proof or implementation obligations.
