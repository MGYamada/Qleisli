# Reference contract: existing modular Add2

Existing experimental A002, contract v1, not general add_mod2n; [conventions](../../STDLIB.md).

## Meaning

|a,b> -> |a,(a+b) mod4>, coefficient+1 for all sixteen labels and arbitrary references.
Retain addend, overwrite arbitrary destination, wrap overflow, no input-dependent phase.

## Interface and encoding

[Source](../../stdlib/src/arithmetic.qli): pub unitary add2:
Q<((Bit,Bit),(Bit,Bit))>->same. First pair a=a0+2a1, second b=b0+2b1;
consume/return four wires in positions. Flat four-tuple requires explicit conversion.

## Premises and capabilities

Exactly unsigned two-bit values, arbitrary correlated inputs/destination, not zero-only.
No scratch/oracle; static transforms retain phase/budgets. Wrong trees/reuse/limits reject;
no general size/modulus parameters.

## Ancillas and effects

Unitary, zero scratch/measurement/discard. Both registers retained; fixed addend labels
do not imply unchanged reduced state after entanglement. No read-only borrow permission.

## Approximation

None ideal; classical outputs cannot exclude relative phase.

## Resources

Four data/zero scratch, Toffoli/two CNOT/three split/three join. Carry uses original low
bits before destination overwrite; physical synthesis/depth/resource theorem pending.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Existing production wrapper; [full small-corpus replay](../../corpus/validation-v0.2.6.json). |
| Semantic tests | tested | Complete complex/phase columns, independent [oracle](../../scripts/check_input_corpus.py), tolerance1e-11; numerical evidence is separate from proof. |
| Actual IR conformance | pending | Full theorem for this actual source/emitted body remains open; component mathematics is insufficient. |
| Source preservation | pending | General frontend correspondence remains [open](../formal-core.md). |
| Specification review | pending | Independent community review of mathematical intent/conventions remains required. |

## Adoption and teaching

Read carry order with [client](../../corpus/qualtran/add2/main.qli)/[case](../../corpus/qualtran/add2/README.md)
and [arithmetic tests](../../tests/order_finding.rs). Future candidates need wrap,
nonzero destination, wrong carry/order and extra-phase faults; scratch replacement
also needs encoded entry/exact reference-stable cleanup. Classical/inverse agreement
alone is insufficient. Preserve Apache-2.0/Qualtran attribution; adoption needs reviewed
reuse/held-out client/compatibility. This pilot does not create new fault executions.
