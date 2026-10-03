# Qleisli executable Lean 4 kernel

This Mathlib-free package implements bounded pure checkers and proves facts
about their actual executable definitions. Rust remains the production
acceptance authority. Native hierarchical adapters now discharge original-QIRF,
meaning-pair and exact-H obligations; reports are not production evidence seals.
Decoder/native/Rust correspondence, source preservation, full-profile soundness
and the later [verification migration gates](../docs/verification-migration-v0.2.md)
remain separate.

[Soundness composition](../tests/fixtures/soundness_refactor_v028/README.md)
retains typed QIRF stage results and proves the actual packet check reaches
independent finite original-body/reference semantics. The compatibility proof
preserves every input, failure and remaining work value.
[Ordinary ResourceSafe](../tests/fixtures/resource_safe_v028/README.md) additionally
proves independent linear ownership through actual native acceptance for all
19 constructors and both arms. Full EffectSound/hierarchical S05 remains open.

## Code organization

| Layer | Responsibility |
| --- | --- |
| [Reference data](QleisliKernel/Semantics/Exact.lean) and [finite circuits](QleisliKernel/Semantics/Finite.lean) | Independent data and interpretation interfaces; no checker, transport, capacity or producer dependency |
| [Exact arithmetic](QleisliKernel/Exact.lean), [matrix proofs](QleisliKernel/ExactMatrix.lean) and [capacity proofs](QleisliKernel/ExactCapacity.lean) | Canonical R8 coefficients, bounded actual operations and precise work accounting |
| [Finite reconstruction](QleisliKernel/Finite.lean) | Fresh circuit/dependency reconstruction, independently required encoded equations and whole-space inspection |
| [Pure raw checking](QleisliKernel/Raw/Pure.lean), [retained binding](QleisliKernel/Raw/Function.lean) and [finite extraction](QleisliKernel/Raw/Finite.lean) | Eleven original straight-line pure constructors, complete owners/effects, fresh original bodies/attachments and finite/non-dense clean scopes |
| [Observing raw checking](QleisliKernel/Raw/Observation.lean) and [finite instruments](QleisliKernel/Raw/Instrument.lean) | All nineteen constructors, global SSA freshness, lexical scopes, complete quantum phis and exact unnormalized hidden histories; [VM-26 scope and remaining gates](../tests/fixtures/verification_v026/README.md) |
| [QIRF graph checking](QleisliKernel/Qirf.lean) and [QIRF adapter](Protocol/Qirf.lean) | Original QIRF1/2 tables, fresh full-body attachments, exact unary leaf boundaries and whole-space phase equality; [VM-27 scope](../tests/fixtures/verification_v027/README.md) |
| [Hierarchical artifacts](QleisliKernel/Hierarchical/Artifact.lean), [graph schedules](QleisliKernel/Hierarchical/Graph.lean), [node typing](QleisliKernel/Hierarchical/NodeTyping.lean) and [contract typing](QleisliKernel/Hierarchical/ContractTyping.lean) | Actual dependencies, ordered endpoints, type trees, ownership and effects; structural checks alone do not prove leaf meanings |
| [Conditional derivations](QleisliKernel/Hierarchical/Conditional.lean) and [root binding](QleisliKernel/Hierarchical/Root.lean) | Supported rule closure with every finite obligation retained; binding to a separately supplied meaning graph |
| [Fourier root](QleisliKernel/Hierarchical/FourierRoot.lean), [QPE root](QleisliKernel/Hierarchical/QpeRoot.lean), [instrument](QleisliKernel/Hierarchical/Instrument.lean) and [QPE instrument](QleisliKernel/Hierarchical/QpeInstrument.lean) | Actual algorithm geometry/provider binding and initialization/readout composition, retaining component obligations |
| [Protocol import](Protocol.lean) and [native entry point](Main.lean) | Unproved adapters, split into textual, layout, binary hierarchy and finite-JSON readers and CLI modules; never imported by the pure kernel |
| [Separate mathematical package](../lean/README.md) | Complex operator/reference interpretations and mathematical soundness bridges importing these actual definitions; may use Mathlib |
| [Audit](Audit.lean) and [reduction tests](Tests.lean) | Build-time verification, outside executable acceptance |

The [hierarchical limits](QleisliKernel/Hierarchical/Limits.lean) name existing
capacities without changing them. Equality-only field accounting is distinct
from type/uniqueness checking. Ordinary and typed conditional paths share one
state transition and invariant proof, while their local rule checkers retain
separate premises. Typed context proofs arise from actual complete-artifact
checking, never a serialized flag. The [compatibility proof](../tests/fixtures/releases/v0.2.5/kernel-refactoring-equivalence.lean)
compares all seven conditional entry/transition definitions with their literal
pre-refactor expressions, including failure, visits and request order.

The [VM-23 packet](../tests/fixtures/verification_v023/README.md) covers actual
scalar/matrix semantics, canonicality and work/capacity. The [finite checker](QleisliKernel/Finite.lean)
adds fresh reconstruction and encoded equations for VM-24. Their complex bridges
are [ExactMatrix](../lean/Qleisli/ExactMatrix.lean) and
[Finite](../lean/Qleisli/Finite.lean); independent native comparisons use original
inputs rather than Rust decisions or submitted matrices.

[VM-25](../tests/fixtures/verification_v025/README.md) moves structural checking
and bounded extraction before that circuit boundary. It checks eleven original
pure raw constructors and freshly reconstructs retained bodies and structured
cleanup. [Trace refinement](../tests/fixtures/verification_v025/trace/README.md)
binds every executable constructor to an independent original-operation reader,
including final output order and reconstructed matrix spaces.
[Actual pure proofs](../lean/Qleisli/RawPure.lean) add complete original complex
action, fresh retained graph/attachment semantics and non-dense protected zero
return. The [completion record](../tests/fixtures/verification_v025/completion/README.md)
retains small native Rust/rational/source comparisons. Production seal, QIRF
transport, source preservation and default CLI authority remain separate.

The [VM-26 component](../tests/fixtures/verification_v026/README.md) extends that
original-body boundary to observation and classical branches. A data-only reader
retains full quantum frames and every measurement/reset/discard history. Actual
exact Gram acceptance yields [CP/TNI per outcome and total TP](../lean/Qleisli/RawInstrument.lean)
with arbitrary finite references. General structural checking keeps twelve-bit
owners. [StreamedInstrument](QleisliKernel/Raw/StreamedInstrument.lean) verifies
all exact coefficients without a global dense matrix or global six-bit cap;
[RawStreamedInstrument](../lean/Qleisli/RawStreamedInstrument.lean) proves original
complex refinement and CP/TNI/TP. [BranchFunction](QleisliKernel/Raw/BranchFunction.lean)
freshly binds complete closed classical-branch bodies. Verification remains
exponential and budgeted; production integration is VM-28/29 work.

The phase-word/shared-DAG profiles prove cyclic actions, typed layouts prove
permutation/reference round trips, and interference normalization proves its
local amplitude laws. Internal QFT/QPE matchers have separate complex bridges:
[QFT](../lean/Qleisli/Qft.lean), [typed QFT graphs](../lean/Qleisli/QftGraph.lean)
and [QPE](../lean/Qleisli/Qpe.lean). Internal matching is distinct from complete
hierarchical binding and does not enable an external schema.

The binary stdin modes run fresh checks of complete tables. `--hierarchy-pending`
retains finite leaf requests; `--hierarchy-request-pending` additionally binds an
independent complete meaning graph. `--hierarchy-fourier-pending` retains exact-H
roles. Initialization/readout and named-QPE modes retain their full ordered
boundaries. Native adapters discharge original QIRF leaves, requested matrix
pairs and fixed H under one exact-work budget. Rust native-only reports check
transport coverage; compatible executable reports independently rebuild sealed
Rust leaf handles under their own budget. See the [hierarchical
contracts](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/hierarchical-ir-spec.md) for each mode's scope and remaining
gates. Ordinary CLI/QIRF defaults remain Rust; [VM28](../tests/fixtures/verification_v028/README.md)
adds explicit dual checking with original artifact/request bytes and no fallback.

The [QIRF semantic bridge](../lean/Qleisli/Qirf.lean) proves actual original-graph
and root complex/reference meaning; [native discharge](../lean/Qleisli/NativeHierarchy.lean)
connects every finite leaf, pair and fixed-H body to structural derivations.
All-field decoder and small whole-hierarchy/named-QPE tests are independent
regressions, not universal decoder/compiler or analytic root-reader proofs.

Experimental command formats and pure checking bounds are defined by the
[protocol](Protocol.lean), [phase hierarchy](QleisliKernel/Hierarchy.lean),
[layout](QleisliKernel/Layout.lean), [layout graph](QleisliKernel/LayoutDag.lean)
and [phase/layout](QleisliKernel/PhaseLayout.lean) modules. They are distinct
from QIRF and production hierarchy acceptance. Artifact and independent request
files are capped at 65,536 bytes, use printable ASCII/canonical unsigned decimal
tokens separated by one space, and require LF including the final line.
The phase-DAG envelope is `qleisli.phase-dag 1 phase256-dag-v1`; each actual
summary preserves flip and both cyclic phases, and all proposed summaries are
checked against derived actions and a separate root request. Powers are closed
summary computations, without expanding their execution count.

The layout/request envelopes are `qleisli.layout` and `qleisli.layout-request`
version 1/profile `typed-layout-v1`. Exact prefix type trees, ordered axes,
owner/axis maps and their artifact inverses retain zero-width owners. The pure
checker bounds each interface to 64 owners/16 axes, each type to 128 atoms,
32 tuple levels and Bits width 8, and combined type atoms to 512. Work is charged
conservatively before validation, with a 2,000,000-unit ceiling. Layout DAGs
use `qleisli.layout-dag 1 typed-layout-dag-v1`, cap 256 definitions, 4,096 visits
and depth 64, and bind both call adapters and actual composition order. The
phase/layout profile adds exact sparse phase polynomials without erasing axes,
global phase or type trees. Unknown/malformed profiles, fields and maps reject;
limits fail without partial success. Fixture READMEs retain first sources and
process/mutation results, while actual decoder definitions determine wire fields.

The current internal interference and Fourier contracts are defined by
[Interference](QleisliKernel/Interference.lean), [PathSum](QleisliKernel/PathSum.lean),
[Qft](QleisliKernel/Qft.lean) and [QftGraph](QleisliKernel/QftGraph.lean).
Interference normalization preserves amplitudes and arbitrary references under
the stated ring/root premises; it adds no external artifact profile. QFT uses
positive Fourier coefficients `exp(2*pi*i*x*y/2^m)/sqrt(2^m)` with little-endian
coordinates and actual final data reversal. Both literal and normalized-path
matchers retain widths 1–8, at most 36 gates and exact phase modulo 256.
Normalized path equality is not a complete unitary-equivalence procedure.
The typed graph projection requires one canonical `Bits(m)` owner, no classical
slots, unitary effect and exact call boundaries. Its cached summaries are bounded
to 256 definitions, depth 64 and 4,096 references, with charged gate concatenation.
The complex coefficient/reference and whole-space inverse theorems live in
[Qft](../lean/Qleisli/Qft.lean), [QftGraph](../lean/Qleisli/QftGraph.lean) and
[QftUnitary](../lean/Qleisli/QftUnitary.lean). External decoding, complete hierarchy
projection, source preservation and native correspondence are separate gates;
all external schema entries remain disabled. Historical experiments and first
diagnostics remain with [interference](../tests/fixtures/lean_interference/README.md),
[QFT](../tests/fixtures/lean_qft/README.md) and
[graph](../tests/fixtures/lean_qft_graph/README.md) fixtures.

Lean 4.30.0 is pinned. With `elan` and that toolchain installed, from this
directory run:

```sh
lake build
lake env lean Tests.lean
lake env lean Audit.lean
lake env lean ../tests/fixtures/releases/v0.2.5/kernel-refactoring-equivalence.lean
lake env leanchecker --fresh QleisliKernel
lake env leanchecker --fresh Main
```

The [backend execution policy](../docs/lean-kernel-migration.md#backend-execution-must-match-kernel-definitions)
requires source and compiled-declaration rejection of `unsafe def`,
`@[implemented_by]`, `@[extern]` and `partial def` for project executable code,
including private/generated helpers. These bans already apply throughout this
package and must carry over to future backend code or a separate backend
package. Protocol and CLI submodules are audited by origin too; pure imports
cannot reach either transport namespace. Axiom auditing alone cannot rule out runtime replacements. The
compiled negative suite covers nested backend/transport modules and axiom-free
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
| [Reshape.lean](QleisliKernel/Reshape.lean) | Experimental canonical single-owner adapter metadata; general leaf-encoding, inverse/composition and reference-coefficient proofs. Not a new hierarchy rule, source API or evidence issuer; see the [adoption boundary](../docs/size-expressions.md). |
| [Hierarchical/Readout.lean](QleisliKernel/Hierarchical/Readout.lean) | Actual measurement nodes and explicit little-endian CBits assembly, with residual/reference branch proofs. The private `--readout-check` command checks this slice only; [full measured-QPE integration remains in progress](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md). |
| [Hierarchical/Preparation.lean](QleisliKernel/Hierarchical/Preparation.lean) | Actual fresh `init0` nodes, exact frames and zero-factor/reference proofs. Private `--preparation-check` checks this component; composition with the pure graph/readout remains a separate obligation. |
| [Hierarchical/NodeTyping.lean](QleisliKernel/Hierarchical/NodeTyping.lean) | Actual definition-node ownership/effect checks, both call maps and names, and proved whole-table checking under the shared budget |
| [Hierarchical/ContractTyping.lean](QleisliKernel/Hierarchical/ContractTyping.lean) | Actual meaning/encoding types, QPE provider/header binding and zero-scratch shape, with whole-table budget/coverage theorems |
| [Protocol.lean](Protocol.lean) | Compatibility import for [text](Protocol/Core.lean), [layout](Protocol/Layout.lean), [binary hierarchy](Protocol/Hierarchical.lean) and [finite JSON](Protocol/FiniteCodec.lean); correspondence not mechanized |
| [Main.lean](Main.lean) | Command dispatch to [textual CLI](Cli/Finite.lean) and [hierarchical CLI](Cli/Hierarchical.lean), with shared bounded file/error handling; issues no production evidence handle |
| [Tests.lean](Tests.lean) | Reduction-checked examples and maximum-word boundary evaluations |
| [Audit.lean](Audit.lean) | Compiled project declaration, axiom and import audit |

See the [word wire contract](../docs/lean-kernel-migration.md#first-executable-slice)
and [DAG contract and proof limits](QleisliKernel/Hierarchy.lean), plus the
[typed layout contract](QleisliKernel/Layout.lean) and
[shared typed call contract](QleisliKernel/LayoutDag.lean) and
[combined phase/layout contract](QleisliKernel/PhaseLayout.lean),
before reusing the experimental formats. This is not a full IR, QFT/QPE schema,
general ownership verifier or compiler-correctness proof. The separate
[complex bridge](../lean/Qleisli/Interference.lean) currently covers H/diagonal
amplitudes and the phase/layout checker's weighted basis transitions. The
[QFT proof](../lean/Qleisli/Qft.lean) establishes the matched circuit's positive
normalized Fourier coefficients and their extension to arbitrary references.

Copyright 2026 Masahiko G. Yamada. Licensed under Apache-2.0; see
[LICENSE](../LICENSE) and [NOTICE](../NOTICE).
