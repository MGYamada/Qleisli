# VM-26 completion: observing original raw IR

VM-26 moves the independently checked Rust/Lean boundary to all **nineteen
original raw constructors**, including measurement/reset/discard, classical SSA,
branches, complete quantum/classical phis and retained closed branch-functions.
The Mathlib-free checker receives original bodies and independent full bindings;
no Rust decision, extracted circuit or proposed Kraus operator is trusted.
Rust retains production authority. VM-27–29 and S05 remain separate.

## Actual definitions and independent meaning

[Observation](../../../lean-kernel/QleisliKernel/Raw/Observation.lean) checks both
arms from the same live interface and one monotonically growing global ID store.
The actual `classical_fresh`, `checkOps_history` and `exclusive_arms_history`
theorems preserve issuance across exclusive arms; `phi_coverage` includes every
live owner, Unit and untouched caller frames. Lexical SSA visibility, simultaneous
phi operands, widths/effects, complete outputs and original-reader binding are
checked by actual executable definitions. Structural capacities remain twelve-bit
owners and 64 nested branches. No production Rust API/capacity is reduced.

[The independent reader](../../../lean-kernel/QleisliKernel/Semantics/Observation.lean)
imports data/reference modules only. It retains both original arms and their
complete final permutations. Measurement applies every basis bra; discard
retains hidden bra outcomes; reset retains the old hidden outcome and appends
a fresh zero ket. Branch selection uses the actual classical values. No history
is sampled, renormalized or dropped for having zero probability.

[StreamedInstrument](../../../lean-kernel/QleisliKernel/Raw/StreamedInstrument.lean)
checks the complete exact equation `Σ K†K = I` entry by entry, using
[Coefficient](../../../lean-kernel/QleisliKernel/Raw/Coefficient.lean) functions
rather than global dense matrices. All input/output dimensions are taken from
the actual checked interfaces. There is no global six-bit restriction. Shared
charged canonical R8 arithmetic can reject on overflow/work exhaustion;
verification still enumerates exponentially many coordinates/histories and is
**not a scalability or runtime-performance claim**. Retained callable functions
keep their published finite signature/body/graph/identity capacities.

[RawCoefficient](../../../lean/Qleisli/RawCoefficient.lean) proves actual gate,
monomial, adjoint dependency, initialization, basis lift, permutation, original
physical C/W/C and protected-use coefficients equal their independent unbounded
complex actions. Protected scopes use the proved zero-image factorization;
ordinary certified scopes retain independent local cleanup equations.
[RawStreamedInstrument](../../../lean/Qleisli/RawStreamedInstrument.lean) proves
actual adaptive evaluation refines the complete original coefficient instrument,
including all hidden outcomes, residuals and simultaneous phis. Actual streamed
Gram acceptance yields Kraus completeness, CP/TNI per coarse public outcome and
TP overall on arbitrary finite references. Neither Rust acceptance nor an
externally assumed completeness/isometry equation is a premise.

The separate six-bit [Instrument](../../../lean-kernel/QleisliKernel/Raw/Instrument.lean)
component remains for dense comparisons. Its original-operation refinement is
proved in [RawInstrumentDenotation](../../../lean/Qleisli/RawInstrumentDenotation.lean),
and its finite CP/TNI/TP laws in [RawInstrument](../../../lean/Qleisli/RawInstrument.lean).
It is not the general observing acceptance profile.

## Fresh retained functions

[BranchFunction](../../../lean-kernel/QleisliKernel/Raw/BranchFunction.lean)
checks every original arm, closed SSA selection, exact implementation/specification
operators, whole-space unitarity, dependency depth/expansion and full bindings.
[ObservationBinding](../../../lean-kernel/QleisliKernel/ObservationBinding.lean)
proves bounded full-body equality, including unselected arms and type trees;
identity comparison retains every name/source byte. Frame permutations rename
subsequent axes; only the final composite physical route contributes to function
expansion. A dependency prefix is reconstructed from no trusted receipts.
[RawBranchFunction](../../../lean/Qleisli/RawBranchFunction.lean) proves the actual
accepted graph has independent original implementation/specification semantics,
full phase-sensitive operators and exact bindings. Old pure function APIs remain.

## Reproducible small comparisons

- [Finite observation](native-validation.json): **150 native cases, 143 Rust
  comparisons, 145 exact Kraus operators/hidden histories**.
- [Full branch functions](branch-validation.json): **51 native cases, 45 Rust
  comparisons, 69 exact operators**, including full identities, dependency
  prefixes, selected/unselected arms, phis, malformed bindings and phase faults.
  Existing high auxiliary capacities are metadata; only their independently
  fixed small logical specifications are used for operator comparisons.
- [Matrix-free instruments](streamed-validation.json): **154 native cases,
  143 Rust comparisons, 147 exact Kraus operators/hidden histories**. Additional
  retained branch roots cover adjoints, negative controls, residual references,
  unselected invalid bodies and altered source/binding bytes. These retained
  cases reuse the separately compared function graph; no Rust decision is fed
  to Lean. The missing-classical-values case is transport-level and excluded
  from ordinary Rust raw-validity parity.

The independent rational Python oracle retains original gates, physical C/W/C,
frame permutations, basis bras, hidden labels and complete Gram equations.
Five complete source roots are emitted as original QIRF without truncating
terminal measurement: the preserved first measurement-driven source, Bell,
Katas graph state, Qualtran controlled reflection and PennyLane negative ZZ.
All semantic comparisons use at most three data qubits; no maximum-size corpus
is generated. Input/output records, immutable QIRF snapshots and actual
source/compiler/native binary hashes accompany each report.

All runtime recursion is total. Source and compiled audits include generated
helpers; unsafe/partial/runtime replacement helpers have no exemption. The
[registry rebuild](registry-validation.json) audits both packages and replays
the fresh kernel. [Validation](validation.json) records final checks/bindings;
[the earlier finite checkpoint](finite-checkpoint.json) retains its dated scope.
VM-22 updates the reviewed current source census only: public surfaces/capacities,
original comparison bytes and historical corpus prefixes stay frozen.

## Separate remaining gates

Strict private JSON adapters and native binaries are experimental. Decoder/native
correspondence, immutable production transport, source preservation, distribution
and opt-in dual integration belong to VM-28/29. VM-27 retains hierarchy/root closure.
No external schema is enabled. General Soundness/Physical Realizability/Resource
Safety, shared-QPE/R14/H1–H5 and source/backend preservation remain their own goals.
Version selection and VM-26 completion perform no tagging/publication or transfer
of Rust production authority.

Run Python 3.11+ from the repository root:

```sh
python3 scripts/test_lean_observation.py --record /tmp/vm26/native-validation.json
python3 scripts/test_lean_branch_function.py --record /tmp/vm26/branch-validation.json
python3 scripts/test_lean_streamed_instrument.py --record /tmp/vm26/streamed-validation.json
python3 scripts/check_lean_kernel.py
python3 scripts/test_check_lean_kernel.py --compiled
python3 scripts/check_verification_inventory.py
python3 scripts/check_schema_registry.py
```

Build both Lean packages and run their Audit.lean files. In lean-kernel, run
Tests.lean and `lake env leanchecker --fresh QleisliKernel` / `--fresh Main`.
CI retains the pure gates and all three independent VM-26 native comparisons.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
