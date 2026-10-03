# Ordinary raw ResourceSafe

This continuation proves independent linear ownership for the ordinary raw/QIRF
profile, including all 19 constructors and both arms of every classical branch.
It retains the [existing executable client](../authoring_sessions/dual-v028/attempt-02/main.qli)
and native protocols. No language, capacity or acceptance change is intended.

## Independent judgment

[Ownership](../../../lean-kernel/QleisliKernel/Semantics/Ownership.lean) imports
only original semantic data/readers, with no checker, work budget, evidence
receipt or effect decision. `ResourceSafe` requires fresh input owners, a `Run`
derivation for the original operations, and complete returned owners.

- `Valid` gives unique live/issued tokens, disjoint live wires covering the
  ordered frame, correct port widths and issued-axis membership. Zero-width
  owners remain present. Ownership does not imply quantum separability.
- `Pure` binds literal operand consumption/return through `RawTrace.step`,
  exact issued identities, and independent `Access` rules. Gate operands have
  the required width; internal controls/targets are distinct and in bounds of
  the consumed owner or explicit scratch. Protected uses retain source, target
  and scratch scope. A default index cannot grant access to another owner.
- Measurement/discard consume owners; reset consumes then allocates afresh.
  Scratch identities remain issued after scoped release. Exact zero-return
  equations are separate semantic obligations, not consequences of freshness.
- A branch derives both complete arms from the entry live frame, threads issued
  identities across both arms, accounts for every owner in both phi inputs, and
  creates fresh merged owners. `Run.split` gives valid instruction prefixes,
  including inside either arm. Classical SSA is outside this ownership judgment.
- [Independent laws](../../../lean-kernel/QleisliKernel/Semantics/OwnershipLaws.lean)
  prove no implicit drop (also Unit), no empty-phi loss, no identity reuse and no
  gate on a Unit owner. The Unit identity program has a direct resource derivation.

## Actual-checker composition

1. [Raw ownership](../../../lean-kernel/QleisliKernel/Raw/Ownership.lean) proves
   dispatch access/freshness and `prepare_resourceSafe` for the straight-line API.
2. [Observing ownership](../../../lean-kernel/QleisliKernel/Raw/ObservationOwnership.lean)
   proves `verify_resourceSafe` for every successful ordinary verification, at
   any successful budget. Nested branches use the actual recursive checker.
3. [QIRF ownership](../../../lean-kernel/QleisliKernel/Qirf/Ownership.lean) binds
   that property to the original artifact root with or without a finite request.
4. [Native ownership](../../../lean-kernel/Protocol/Validity.lean) proves
   `check_resourceSafe` from actual QLV1 packet success and preserves the full
   original packet/artifact/request binding. All these proofs are Mathlib-free.
5. [Mathematical composition](../../../lean/Qleisli/QirfValidity.lean) strengthens
   `RootMeaning` with `resources`; the existing
   [native soundness theorem](../../../lean/Qleisli/NativeValidity.lean) consequently
   carries ownership together with optional finite contract/reference semantics.

The sole executable refactor names `checkAction` and `checkStep` inside the
existing observing loop. `checkOps_projection` proves equality to the former
literal action for every input, depth and work budget, including errors and
remaining work. The predecessor occurs only in the theorem statement, not as a
second executable checker. [Source review](source-review.json) binds changed files.

## Validation and remaining scope

[Validation](validation.json) records builds, declaration audits, fresh kernel
replay and bounded native comparisons. Old/new native packets are compared by
input digest, exit status and complete output, including work. The observation
comparison retains exact Kraus operators and hidden histories, not just counts
or probabilities. No maximum-size quantum cases are newly generated or checked.

This closes the **ordinary quantum ownership component**, not
S05.
Full `EffectSound`, complete instrument/contract composition, hierarchical
ownership and the analytic reader-to-Operator bridge remain open. Quantitative
resource safety, source/compiler/execution preservation and independent
specification review are separate. Rust authority and disabled external schemas
persist. Historical validation records and temporary proofs remain intact.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
