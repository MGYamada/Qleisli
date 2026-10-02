# Finite core formalization and soundness obligations

Current general source/Rust/backend adequacy is unproved. Actual models/proofs
and validation remain in [Lean](../lean/README.md), [kernel](../lean-kernel/README.md)
and fixtures. [Milestones](release-milestones.md) govern theorem claims; historical
paper expositions use Git history. Rust is production-authoritative, external
schemas disabled. Independent reference-specification review remains separate.

## 1. Scope and judgments

Finite Unit/Bit/products; distinct fresh tokens/ordered wires; total termination;
Unitary≤Iso≤Observe. Complete quantum interface includes returned mixed values,
residual environment and pending/caller frames. Pure classical results depend
only on classical input; calls retain declared effects. [Language](language-spec.md),
[types](type-system.md) and [grammar](syntax-v0.md) fix rules.

## 2. Ideal semantics on the entire system

Pure VρV† requires V†V=I, and VV†=I for Unitary. Every local operation extends
by reference identity. Observe uses complete Kraus maps, CP/TNI per outcome,
summed TP; adaptive composition sums hidden histories. [Sealed semantics](language-spec.md#6-封印された組み込み操作)
fixes preparation/measurement/discard/reset. Split owners may remain entangled.

## 3. Evidence for pure auxiliary release

Exact factorization F=(I tensor |0>)V for every input/reference, never lifetime
or floating zero. Legacy compute restricts emitted Z/T; [SC](finite-contracts.md)
checks actual W Ef=Ef u with independently fixed u/output order, giving
Cf†WCf E0=E0u. Protected observation/reset/discard and standalone Release0 reject.

## 4. Theorem status and proof work

Prioritize actual independent IR acceptance/evidence, then complete finite/root/
instrument binding, then source/backend preservation. [Inventory](rule-inventory.md)
links every inspected component and its proof scope. VM-23 proves actual bounded
R8 arithmetic; VM-24 actual finite columns/encodings/reference/clean/inverse laws;
[VM-25](../tests/fixtures/verification_v025/completion/README.md) straight-line pure
raw acceptance/complex action/protected cleanup/fresh attachments and capacities.
[VM-26](../tests/fixtures/verification_v026/README.md) checks observation/SSA/phis
and proves original complex instrument CP/TNI/TP without a global matrix;
retained branch-functions are checked. VM-27–29 remain pending.

Mathematical source rule-system R1/T1–3/S1–4/F1–5/C1–5/Q1–3 paper results,
Lean resource/lookup projections and local Kraus algebra do not prove all Rust
paths. Hierarchy constructed denotations/unitarity/root/QPE components retain
finite-reader/native/transport/provider premises; the seed phase-word proof is
not production Soundness or H1–H5. [S05/PR/RS](release-milestones.md) remain targets;
ownership/work limits prove no quantitative Resource Safety bound. Protocol/
algorithm/hardware correctness is separate. [Physlib gate](../lean/README.md#future-physlib-bridge)
is required before a concrete dependency bridge.

### Temporary proof markers

Importance and lifetime are independent. Mark eventual retirements temporary (TP-ID), P0/P1/P2, replacement and concrete removal condition in Lean doc comments. Keep every marked declaration built/audited, reusable mathematics and required current registry APIs. Do not mark a result temporary merely because it is long, bounded, conditional or low priority. No declaration is removed by this inventory. Removal requires caller/registry migration, same obligation coverage and public API review; TP-005/006 remain required.

| Importance | Obligation and current examples | Maintenance policy |
| --- | --- | --- |
| P0 — acceptance and binding | Actual executable checker soundness, complete ownership/effect/entry binding, finite-request extraction, actual-body denotations and reference preservation: kernel `Hierarchical` checks, `Reshape`, `HierarchicalEvaluation`, `HierarchicalAcceptance`, `HierarchicalFiniteEvaluation`, `HierarchicalFiniteUnitary`, `HierarchicalRoot`, `HierarchicalInstrument`, and actual gradient/Fourier inspection bridges. | Keep and repair first. These obligations remain necessary when a checker or representation is replaced; a narrower theorem cannot replace them. Current component scope and explicit reader/native premises still apply. |
| P1 — semantic foundations and required components | Reusable operator/matrix, layout, phase, Fourier, Kraus/completeness and reference-extension laws; source resource/scope models; call-lowering laws; current QFT/QPE projection components and semantic regressions. | Preserve reusable results. Extend them for a concrete caller or acceptance obligation. A component may be temporary while its current callers still require it. |
| P2 — migration and compatibility wrappers | Superseded assumed-environment conclusions, projection-only entry packaging, legacy basis-conditioned dispatch and a misleading compatibility name. | Maintain compatibility and validation; direct new development to the replacement. Avoid adding parallel wrapper families without a concrete caller. |

| ID | Importance | Temporary declarations | Replacement and removal condition |
| --- | --- | --- | --- |
| TP-001 | P2 | `HierarchicalSemantics.Interprets` and `ordinary_sound`, `power_sound`, `derives_sound`, `checkAll_sound`, `checkAll_entry_sound`; `HierarchicalOperators.checkAll_operator`, `checkAll_matrix`, `checkAll_reference`, `powerEntry_operators` | Use the [constructed evaluator and denotation theorems](../lean/Qleisli/HierarchicalEvaluation.lean). Migrate remaining wrappers, including the independent coherent-power request conclusion, before removal. Keep `bodies_sound`, interface/entry binding, operator definitions and matrix laws: the constructed proofs use them. |
| TP-002 | P2 | `HierarchicalPower.inspectEntry_equation`, `inspectEntry_reference` | Replace projection-only entry wrappers with the constructed derivation entry, retaining its independent power request. Keep the local `inspect_operators`/`inspect_unitary` component lemmas where used. |
| TP-003 | P2 | `Schema.power_sound` | The shipped registry already selects `Schema.power_coherent_sound`. Retire the old basis-conditioned wrapper; retain lower-level action lemmas still used by QPE. |
| TP-004 | P2 | [`PhaseLayout.check_reference`](../lean-kernel/QleisliKernel/PhaseLayout.lean) | Use `check_reference_value` for the same product-value statement. Retire only the compatibility name after caller migration and public API review. Neither name proves an entangled-reference theorem; keep `check_sound` and the separate complex/reference bridges. |
| TP-005 | P1 — still required | [`QftGraph.check_fourier`, `check_reference`](../lean/Qleisli/QftGraph.lean); [`QftGraph.checked_matrix`, `check_unitary`](../lean/Qleisli/QftUnitary.lean); [`Schema.qft_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QFT-graph projection interface with an independently requested Fourier theorem over the actual full hierarchical artifact. Require actual outer reversal, full finite H binding, exact phase, both inverse laws and reference preservation; migrate QPE callers and the exported registry type before retirement. The recursive-body theorem alone does not meet this condition. Keep generic Fourier, normalization, index and matrix lemmas, and the bounded circuit regressions. |
| TP-006 | P1 — still required | [`Qpe.inverse_coefficient`, `checked_branch`, `checked_instrument`, `checked_plan`](../lean/Qleisli/Qpe.lean); [`Qpe.checked_complete`, `checked_plan_complete`, `accepted_plan`](../lean/Qleisli/QpeComplete.lean); [`Schema.qpe_sound`](../lean/Qleisli/Schema.lean) | Replace the separate internal QPE-plan interface with a theorem over actual hierarchical preparation, independently verified provider/control access, inverse QFT and measurement. Require the same exact Kraus branches, retained target/reference state, all-outcome completeness/trace preservation and boundary/freshness obligations. Migrate callers and the exported registry type before retirement. Keep `kraus`, `kraus_complete`, character orthogonality, `complete_withReference`, `complete_trace`, bit encodings and reusable preparation/power laws. |
