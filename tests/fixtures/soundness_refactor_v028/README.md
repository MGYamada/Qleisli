# QIRF soundness composition refactor

This continuation keeps v0.2.8 acceptance and work capacities unchanged while
making production QLV1 success usable by mathematical proofs. The existing
[dual authoring source](../authoring_sessions/dual-v028/attempt-02/main.qli)
is the unchanged executable client; no notation, algorithm or evidence source
was added. Earlier VM28 records describe the pre-refactor implementation.

## Composition boundary

1. [Independent data](../../../lean-kernel/QleisliKernel/Semantics/Qirf.lean)
   now owns the existing QIRF types and a budget-free interpretation of the
   caller's complete permutation/phase table. Declaration names and wire types
   are preserved. Reference modules do not import acceptance or transport.
2. [Typed acceptance](../../../lean-kernel/QleisliKernel/Qirf/Checked.lean)
   retains the original root, freshly rebuilt dependencies, structural check,
   canonical target and exact operator. `checkRoot`, `checkRequested` and `check`
   are the production path; callers cannot supply intermediate results.
3. [Refinement contracts](../../../lean-kernel/QleisliKernel/Qirf/Validity.lean)
   expose named `RootPostcondition`, `EquationPostcondition` and `Postcondition`
   facts. `requested_projection` and `inspect_projection` prove equality to the
   former literal WorkM actions for **all inputs and budgets**, including
   errors and remaining work. Compatibility APIs/theorems remain available.
4. [Raw postconditions](../../../lean-kernel/QleisliKernel/Raw/Observation.lean)
   retain original-program identity, final state/output validity and agreement
   with the independent reader's complete live owners and ordered frame.
5. [Independent finite contract](../../../lean/Qleisli/Semantics/Qirf.lean)
   uses original full instrument meanings on both sides and both complex
   inverse laws. It contains no checker success, work budget or decoder premise.
6. [Composition](../../../lean/Qleisli/QirfValidity.lean) proves `check_sound`,
   `inspect_sound` and arbitrary finite `requested_reference_laws` from actual
   acceptance, with no Rust decision, producer correctness or assumed isometry.
7. [Native binding](../../../lean/Qleisli/NativeValidity.lean) proves
   `check_sound` for the exact `Protocol.Validity.check bytes` used by the CLI.
   The existential acceptance record retains the original packet, artifact and
   request decodes and actual typed result at the same final budget.

## Remaining theorem obligations

This is a proof-enabling refactor and a composed bounded theorem, not completion
of [S05](../../../docs/release-milestones.md#qleisli-soundness-theorem-v050).
The root postconditions are **structural refinement facts**, not definitions of
independent `ResourceSafe` or `EffectSound`. Roots without a finite request do
not acquire an algorithm specification or a new full-instrument theorem.

The next proof steps are independent resource/effect judgments over every
original operation and control-flow path; their composition with the existing
observing CP/TNI/TP results for the complete ordinary profile; and the VM27
analytic finite-reader-to-Operator bridge and full hierarchical root theorem.
Parser/native compiler/IO correctness, Rust execution/source preservation,
complete production coverage and independent specification review remain
separate gates. All external schemas remain disabled; Rust authority persists.
No temporary proof was removed or bypassed.

## Validation

[Source review](source-review.json) identifies each change without rewriting
frozen VM22 comparison inputs. [Validation](validation.json) records the actual
builds, audits, fresh kernel replay and small native comparisons. The old/new
native runs preserve positive and negative cases, global phase, Unit owners,
wrong type/source bindings, both classical arms and exact reported work.
Maximum-size quantum cases, hosted release CI and publication are not claimed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
