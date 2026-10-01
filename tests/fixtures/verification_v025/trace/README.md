# VM-25 original-operation trace refinement

The [independent reader](../../../../lean-kernel/QleisliKernel/Semantics/RawTrace.lean)
reads original input ports, operations and final output order. It contains no
acceptance, budgets, cache validity, transport or producer receipts. It records
literal action data and ordered interfaces; it does not decide admissibility or
itself supply the complete complex denotation.

The [actual refinement proofs](../../../../lean-kernel/QleisliKernel/Raw/Trace.lean)
cover all eleven pure constructors. `dispatch_reference`, `operations_reference`
and `prepare_reference` relate successful executable checking to this independent
reader, including Unit owners, both coherent-control arms, original compute/use
fields, local axis order and the final output permutation.

`reconstruct_original` binds actual finite evaluation to that original trace.
`reconstruct_input_dimension` and `reconstruct_output_dimension` fix its matrix
spaces. The [complex bridge](../../../../lean/Qleisli/Raw.lean) adds literal local
embedding coefficients, including empty-axis scalar phases, and connects the
original trace to the actual arbitrary-reference norm law. Existing finite
physical cleanup proofs remain required.

[Native validation](native-validation.json) passes 121 cases, 104 Rust comparisons,
85 independent rational matrices and **180 structurally accepted original
program/trace comparisons**. Rejected structural inputs do not contribute to the
180 count. Six cases retain actual Rust corpus output; semantic validation uses
at most three qubits. Focused kernel reductions verify that a controlled `-1`
operator on Unit gives Z on the control, split/output order permutes basis
coordinates, and trace correspondence also holds for twelve-bit metadata without
constructing a dense matrix.

[Validation](validation.json) binds current commands, reports, binaries and
sources. [Registry replay](registry-validation.json) rebuilds both Lean packages,
audits compiled declaration origins and axioms, and freshly checks the kernel.
The [public type review](public-type-review.json) and
[transport comparison](transport-compatibility.json) preserve existing public
contracts. [Inventory review](inventory-review.json) refreshes source snapshots
without changing frozen VM-22 comparison bytes.

The [earlier VM-25 checkpoint](../boundary-validation.json) and its root-level
reports are historical results for their own source hashes. This continuation
does not overwrite or relabel those results.

Full complex raw denotation, non-dense protected cleanup and complete retained
function identity/source/expanded-step/capacity binding remain VM-25 work.
Classical/observing semantics, hierarchy closure and production transport/dual
integration remain VM-26–29. Rust retains production authority; all external
schemas remain disabled. No future Unit introduction/elimination API from
[Issue 43](https://github.com/MGYamada/Qleisli/issues/43) is implemented here.

Original translated sources and their required notices stay in the
[corpus](../../../../corpus/NOTICE); Katas translations are MIT and Qualtran/
PennyLane translations are Apache-2.0. This packet does not relicense them.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
