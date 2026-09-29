# Qleisli executable Lean 4 kernel

This **Mathlib-free** package is the first executable slice of the
[staged Rust/Lean migration](../docs/lean-kernel-migration.md). It checks a bounded
one-bit X/phase word or a shared call/sequence/repetition DAG against a separately
supplied required action. It also checks [typed owner/axis layouts](../docs/lean-layout-slice.md),
including zero-wire owners and exact n-ary type trees. The phase checkers have
soundness theorems over cyclic actions; layout theorems establish finite
permutations and reference-preserving coefficient reindexing. The
[typed layout DAG](../docs/lean-layout-dag-slice.md) connects these to shared calls
and ordered composition, proving acceptance against direct graph semantics.
The [combined phase/layout profile](../docs/lean-phase-layout-slice.md) adds
exact sparse dyadic phases, including controlled conditions and scalar phase,
with proved normalization and shared-composition semantics modulo 256.
The [interference module](../docs/lean-interference-slice.md) adds amplitude
semantics and proved local H cancellation. Its complex interpretation is in
the separate proof package, which imports these actual definitions.
The [QFT proof packet](../docs/lean-qft-proof-packet.md) adds symbolic path
compilation and an internal literal-circuit matcher. Its Fourier coefficient
theorem is in the separate proof package. A [typed shared circuit checker](../docs/lean-qft-graph-packet.md)
now binds this to actual graph dependencies and exact interfaces; external
hierarchy/registry binding is pending. The [QPE plan checker](../docs/lean-qpe-instrument-packet.md)
binds fresh zeros, H preparation, literal controlled powers, inverse-QFT
orientation, measurement order and retained target layout. The separate
proof package establishes its residual instrument and conditional completeness.
The [hierarchical artifact preparer](../docs/hierarchical-ir-spec.md#typed-artifact-preparation)
now extracts typed dependencies and binds proof endpoints to actual interfaces,
sharing its work budget with the proved acyclic graph scheduler. This is
structural preparation. Meaning/encoding typing now follows the node pass;
mathematical equations and semantic derivation checks remain open.
The side-map checker proves complete owner/axis permutations and coefficient
round trips, including zero-width owners and arbitrary references. Integration
with both sides of actual calls is now checked by the definition-node pass,
including consistent fresh names and the same aggregate budget. Finite leaf
semantics and the semantic derivation pass remain required. Structural meanings
and encodings are checked across their complete tables, including all selected
QPE header shapes and explicit zero-scratch boundaries. Explicit structural
conversions now connect Bits/Bit, immediate tuple fields and empty owners, with
checked actual inverse routing and arbitrary-reference coefficient round trips.
The source conversion producer and semantic derivation binding remain pending.
The [finite request projection](../docs/hierarchical-ir-spec.md#finite-reconstruction-requests)
retains the actual indexed program/meaning bytes, complete unary boundary and
identity encodings under the structural budget. Its theorems establish binding,
not the opaque bytes' meaning. The transitional Rust finite checker must still
be connected to these requests and the semantic derivation pass.
The [conditional derivation entry](../docs/hierarchical-ir-spec.md#conditional-finite-derivations)
now checks whole-artifact composition while retaining every such obligation.
Its state/request-origin invariants and conditional derivation are proved;
the separate mathematical package constructs equal operators/reference maps
from explicit leaf equations and now propagates finite-leaf unitarity to both
entry inverse laws with arbitrary references. Pending results still require
decoder/host correspondence before production acceptance. Rust can now freshly
decode the exact finite matrix descriptions, but its result is not a Lean proof
or a whole-hierarchy seal. The additive `--hierarchy-pending` command now reads
the private bounded binary bridge on stdin, reconstructs complete tables and
runs `Conditional.checkAll`. The Rust host freshly checks every returned finite
proof index on the same immutable external artifact. Its inspection report
does not establish an independently requested root contract. The additive
`--hierarchy-request-pending` command runs `Root.checkAll` on that artifact and
a separate complete request with an untrusted graph-pair proposal. The Rust
`Kernel::check_against` API freshly checks both finite reconstruction and exact
meaning-pair equality; the mathematical package proves the requested-root
equation and unitary/reference laws conditional on those actual obligations.
Remaining profile rules and reader/native correspondence still gate production
acceptance; all external schemas remain disabled.
For singleton named Fourier requests, `--hierarchy-fourier-pending` now reads
the private `QLF1` frame and runs `FourierRoot.checkAll`. Complete artifact
checking, the requested closed `Bits<n>` interface and actual Fourier geometry
share the structural budget. The host additionally reconstructs every returned
H index against the independent exact matrix with its remaining finite budget.
The same `Kernel::check_against` API retains both raw inputs. This remains a
conditional checked-request report, with the same correspondence and production
limitations; [validation and contract](../docs/hierarchical-ir-spec.md#fourier-request-host)
include coordinated semantic faults and malformed process responses.
Production
`qleisli check`/`run` and QIRF verification still use the Rust verifier.

Lean 4.30.0 is pinned. With `elan` and that toolchain installed, from this
directory run:

```sh
lake build
lake env lean Tests.lean
lake env lean Audit.lean
lake env leanchecker --fresh QleisliKernel
lake env leanchecker --fresh Main
```

The [backend execution policy](../docs/lean-kernel-migration.md#backend-execution-must-match-kernel-definitions)
requires source and compiled-declaration rejection of `unsafe def`,
`@[implemented_by]`, `@[extern]` and `partial def` for project executable code,
including private/generated helpers. These bans already apply throughout this
package and must carry over to future backend code or a separate backend
package. Axiom auditing alone cannot rule out runtime replacements. The
compiled negative suite covers nested backend modules and axiom-free
replacement examples; it does not claim an implemented backend.

There are no Mathlib downloads or external package dependencies. The separate
[proof package](../lean/README.md) retains its existing Mathlib models.
The bundled `leanchecker` replays the compiled runtime/transport modules through
Lean's kernel. It complements the declaration/import audit; neither check proves
native compiler correctness or sandboxes arbitrary Lean metaprograms.
The development scripts require Python 3.11 or later (standard library only).
From the repository root:

```sh
python3 scripts/check_lean_kernel.py
python3 scripts/test_check_lean_kernel.py --compiled
python3 scripts/test_lean_hierarchy.py
python3 scripts/test_lean_layout.py
python3 scripts/test_lean_layout_dag.py
python3 scripts/test_lean_phase_layout.py
python3 scripts/test_lean_interference.py
python3 scripts/test_lean_qft.py
python3 scripts/test_lean_qft_graph.py
python3 scripts/test_lean_qpe.py
python3 scripts/test_lean_controlled_power.py
python3 scripts/test_hierarchical_graph.py
python3 scripts/test_hierarchical_artifact.py
python3 scripts/test_hierarchical_typing.py
python3 scripts/test_hierarchical_contract_typing.py
python3 scripts/test_hierarchical_structural.py
cargo build --bin qleisli
python3 scripts/test_lean_phase_layout.py --source-only target/debug/qleisli
python3 scripts/test_lean_interference.py --source-only target/debug/qleisli
python3 scripts/test_lean_qft.py --source-only target/debug/qleisli
lean-kernel/.lake/build/bin/qleisli-kernel --phase-layout tests/fixtures/lean_phase_layout/shared.qhd tests/fixtures/lean_phase_layout/expected.qhr
lean-kernel/.lake/build/bin/qleisli-kernel --layout-dag tests/fixtures/lean_layout_dag/shared.qhd tests/fixtures/lean_layout_dag/identity.qhr
lean-kernel/.lake/build/bin/qleisli-kernel --layout tests/fixtures/lean_layout/reorder.qhl tests/fixtures/lean_layout/reorder.qhr
lean-kernel/.lake/build/bin/qleisli-kernel --phase-dag tests/fixtures/lean_hierarchy/shared.qhd tests/fixtures/lean_hierarchy/identity.qhr
cargo run --example lean_kernel -- lean-kernel/.lake/build/bin/qleisli-kernel tests/fixtures/lean_kernel/phase_pair.qpk tests/fixtures/lean_kernel/t_expected.qpr
cargo run --example lean_kernel -- lean-kernel/.lake/build/bin/qleisli-kernel --self-test
```

The last command compares native Lean decisions with independent Rust basis
trajectories and the existing exact matrix evaluator on its ζ8 subset. It also
checks phase/claim/request mutations, malformed inputs, limits and adapter
failures. `global_phase.qpk` paired with `identity.qpr` must reject.

| File | Role |
| --- | --- |
| [PhaseWord.lean](QleisliKernel/PhaseWord.lean) | Executable checks, normalizer, operational semantics and actual acceptance soundness theorem |
| [Composition.lean](QleisliKernel/Composition.lean) | Phase-sensitive composition and closed powers proved equal to operational repetition |
| [Dag.lean](QleisliKernel/Dag.lean) | Shared evaluation and interpretation law, without body expansion |
| [Hierarchy.lean](QleisliKernel/Hierarchy.lean) | Bounded type/port/dependency and receipt checking; actual cyclic-action soundness theorem |
| [Layout.lean](QleisliKernel/Layout.lean) | Complete typed owner/axis permutation checking, inverse and reference-coefficient round-trip proofs |
| [Interference.lean](QleisliKernel/Interference.lean) | Amplitude semantics and sound local normalization; no new public acceptance protocol |
| [PathSum.lean](QleisliKernel/PathSum.lean) | Symbolic path compilation proved against direct literal gate paths, without path enumeration |
| [Qft.lean](QleisliKernel/Qft.lean) | Internal width-1–8 template matching, compiled bilinear phases and output reversal proofs |
| [QftGraph.lean](QleisliKernel/QftGraph.lean) | Typed cached circuit projection, direct graph semantics and actual acceptance binding |
| [ControlledPowers.lean](QleisliKernel/ControlledPowers.lean) | Actual ordered control/count/provider binding, literal iteration and coherent sector composition; separate complex operator/reference bridge |
| [Uniform.lean](QleisliKernel/Uniform.lean) | H preparation paths from fresh zero input |
| [Qpe.lean](QleisliKernel/Qpe.lean) | Bounded internal QPE plan and complete boundary matching |
| [Schema.lean](QleisliKernel/Schema.lean) | Closed component dispatch, fixed IDs/versions, independent request and witness binding; no external schema enabled |
| [Hierarchical/Graph.lean](QleisliKernel/Hierarchical/Graph.lean) | Bounded schedules, actual-edge checks, reachability and proved cycle exclusion |
| [Hierarchical/Artifact.lean](QleisliKernel/Hierarchical/Artifact.lean) | Typed four-table projection and exact proof endpoint binding under a shared budget; no semantic evidence issued |
| [Hierarchical/Ports.lean](QleisliKernel/Hierarchical/Ports.lean) | Actual side-map bijections and exact types, with proved coefficient/reference round trips and a remaining-budget interface |
| [Hierarchical/Structural.lean](QleisliKernel/Hierarchical/Structural.lean) | Explicit consuming/regrouping conversions, actual inverse routing and reference-preserving coefficient round trips; shared-budget checks used by definition and meaning typing |
| [Reshape.lean](QleisliKernel/Reshape.lean) | Experimental canonical single-owner adapter metadata; general leaf-encoding, inverse/composition and reference-coefficient proofs. Not a new hierarchy rule, source API or evidence issuer; see the [adoption boundary](../docs/reshape-plan.md). |
| [Hierarchical/NodeTyping.lean](QleisliKernel/Hierarchical/NodeTyping.lean) | Actual definition-node ownership/effect checks, both call maps and names, and proved whole-table checking under the shared budget |
| [Hierarchical/ContractTyping.lean](QleisliKernel/Hierarchical/ContractTyping.lean) | Actual meaning/encoding types, QPE provider/header binding and zero-scratch shape, with whole-table budget/coverage theorems |
| [Protocol.lean](Protocol.lean) | Bounded canonical text decoder; correspondence not mechanized |
| [Main.lean](Main.lean) | Native file/JSON adapter; issues no production evidence handle |
| [Tests.lean](Tests.lean) | Reduction-checked examples and maximum-word boundary evaluations |
| [Audit.lean](Audit.lean) | Compiled project declaration, axiom and import audit |

See the [word wire contract](../docs/lean-kernel-migration.md#first-executable-slice)
and [DAG contract and proof limits](../docs/lean-hierarchy-slice.md), plus the
[typed layout contract](../docs/lean-layout-slice.md) and
[shared typed call contract](../docs/lean-layout-dag-slice.md) and
[combined phase/layout contract](../docs/lean-phase-layout-slice.md),
before reusing the experimental formats. This is not a full IR, QFT/QPE schema,
general ownership verifier or compiler-correctness proof. The separate
[complex bridge](../lean/Qleisli/Interference.lean) currently covers H/diagonal
amplitudes and the phase/layout checker's weighted basis transitions. The
[QFT proof](../lean/Qleisli/Qft.lean) establishes the matched circuit's positive
normalized Fourier coefficients and their extension to arbitrary references.

Copyright 2026 Masahiko G. Yamada. Licensed under Apache-2.0; see
[LICENSE](../LICENSE) and [NOTICE](../NOTICE).
