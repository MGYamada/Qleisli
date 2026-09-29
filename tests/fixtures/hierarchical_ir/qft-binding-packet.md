# Bind the sized QFT circuit to actual hierarchy data

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Continue from the preserved desired shared QFT/QPE source and the Qualtran QFT
translation. Before changing acceptance, construct the actual width 1/2/3/4/8
hierarchical circuits using only existing finite H leaves, explicit consuming
bit extraction/reinsertion, tensor frames, dyadic phase, control, sequence and
the final bit reversal. The scalar is positive and the first axis is least
significant. Preserve zero-width remainder ownership at width one.

Run those complete external artifacts through the existing fresh host. Record
actual structural/exact work and every failure, including capacity failures.
The fixed work ceilings must not be increased or bypassed to make a fixture
pass. Save the first producer before its first check and retain its diagnostics.
Compare an independent interpreter of the actual IR with the Fourier formula;
negative circuits must expose missing reversal, wrong phase and wrong H action.
Numerical semantic probes are diagnostics, never acceptance evidence.

This experiment selects the concrete gate/layout shape for binding the existing
QFT theorem to production hierarchy. Artifact-only consistency does not prove
that the independently requested meaning is Fourier. The final schema must
relate the actual generated graph and finite H equations to that theorem,
preserve original control/target roles and arbitrary reference amplitudes, and
compose with the actual conditional/root checker under the same shared budget.
Only after those bindings and their mutations pass may the schema be enabled.

The capacity experiment now retains two representations. The first lifts each
gate around the whole register and still exceeds the budget at width eight.
The second keeps recursive register boundaries and shares a fixed-precision
phase gradient through ordinary controlled/repeat nodes; all widths 1–8 fit.
This producer refinement changes no accepted primitive or checker predicate.
For N the fixed precision, its intended gradient is
G_r|x⟩ = exp(2πix/2^N)|x⟩ for 0 ≤ x < 2^r; the width-w stage uses a controlled
G_(w−1)^(2^(N−w)). Binding this grouped/shared circuit to the existing ordered
QFT theorem requires a preservation argument for the actual grouping and
repetition. Do not silently treat its different graph as the original schema's
literal ordered stage witness. The numerical DFT agreement does not discharge
that obligation.

The [diagonal-law continuation](gradient-first/README.md) supplies the exact
operator and sparse-phase laws for that preservation argument. The actual
controlled/repeated-node theorem retains the child gradient's diagonal
characterization explicitly. Next derive that characterization from the actual
split/tensor/join graph, then bind the H/stage structure to Fourier semantics.

The subsequent [actual-gradient packet](gradient-binding-packet.md) closes the
shared child-diagonal obligation: actual definition projection and bounded
inspection now imply the exact complex diagonal with arbitrary reference
columns. [Native evidence](gradient-binding-native.json) includes cumulative
remaining budgets after whole-artifact conditional checking. Outer QFT stages,
finite H binding and the final Fourier-root theorem remain the next boundary.
