# Exact laws for shared phase gradients

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This informed proof continuation follows the actual shared-gradient QFT
producer in the [binding packet](../qft-binding-packet.md). It supplies the
operator laws needed to replace a sequence of individual controlled phases
with an actual controlled repetition. It does not claim that the whole QFT
artifact has been bound to the Fourier schema.

`HierarchicalDiagonal-first.lean.txt` retains the initial proof source before
any repairs. A relative-path snapshot command initially ran from `lean/` and
failed; the absolute-path copy was made while the first Lean check was still
running, before reading or acting on its diagnostics. [That first result](first-check.json)
records function-power extensionality, hidden matrix wrappers in a tensor
proof, and the equal-index branch of permutation conjugation. Repairs use the
matrix diagonal/Kronecker laws and explicitly handle the equal-index branch.
The actual-body bridge later needed `Option`/`List.mapM` reduction before
unfolding the algebra; otherwise simplification lost the matching form of the
child-evaluation hypothesis. Unused simp arguments were removed under the
existing warning-as-error policy.

`Operations-first.lean.txt` and `HierarchicalDiagonal-sparse-first.lean.txt`
were copied before their first sparse-operation checks. The initial operation
file incorrectly opened a nonexistent `PhaseWord` namespace, expanded modular
arithmetic too aggressively and lacked a zero-sum map lemma. Removing that
open, using standard modular reduction and proving the zero map sum by
induction repairs these errors. These later errors are summarized here; their
full terminal logs were not saved. The native script is unchanged from its
first run; `native-first.py.txt` was copied after that successful run.

The pure executable helpers scale each phase coefficient modulo 256 and add
a positive control condition. Their proofs apply to every input, not a finite
basis enumeration. Their term counts stay unchanged, including at zero and
4096 repetitions. The separate [native record](../gradient-native.json)
compares 6,142 compiled results with independent integer oracles, including
1,004 shared-QFT gradient cases and global phases. The helper permits general
polynomials; it grants no permission to alias a quantum control and target.
An enclosing checker must still validate axis scopes, interfaces and work.

The Mathlib proofs use the actual `HierarchicalOperators` definitions for
composition, tensor, control, powers and routing. `physical_controlled_gradient`
reads actual controlled/repeated body fields and the actual child evaluation;
only that child's diagonal characterization remains a premise. It assumes
neither a whole-graph environment nor a producer matrix receipt. Sparse scale
and control operations also describe the exact complex diagonal of those
operators. `joint_amplitude` permits arbitrary correlated reference columns.

Still required: derive each gradient's diagonal characterization from its
actual split/tensor/join graph, bind H and the outer QFT stage order, prove the
complete grouped graph has the requested Fourier coefficients, and connect
that result to the supported external schema. All schema entries stay disabled.
