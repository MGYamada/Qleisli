# Reference contract: existing QFT2

Existing experimental F001, contract v1, not generalized qft; [conventions](../../STDLIB.md).

## Meaning

F4[y,x]=exp(2πixy/4)/2, every input/full phase, identity on references.
F4|1>=(|0>+i|1>-|2>-i|3>)/2.

## Interface and encoding

[Source](../../stdlib/src/transforms.qli): pub unitary qft2:Q<(Bit,Bit)>->same.
x=a+2b at both ends; return complete owner. join(b,a) supplies required reversal;
leaf display10 means integer1, not big-endian2.

## Premises and capabilities

All four labels/correlated superpositions, no zero/eigenstate promise. Existing
static inverse/control/repeat and budgets apply; wrong tree/alias/reuse/limits reject.

## Ancillas and effects

Unitary, zero scratch/observation/discard, all wires returned. Correlations transform
by F4; no borrowing or unchanged reduced-state promise.

## Approximation

None ideal; numeric tolerance, approximate QFT and device noise are separate.

## Resources

Two data wires, two H, two controlled T and output reversal; splits/joins do not
promise free physical routing. Physical depth/gates and resource theorem pending.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Existing production wrapper; [full small-corpus replay](../../corpus/validation-v0.2.6.json). |
| Semantic tests | tested | Complete complex/phase columns, independent [oracle](../../scripts/check_input_corpus.py), tolerance1e-11; numerical evidence is separate from proof. |
| Actual IR conformance | pending | Full theorem for this actual source/emitted body remains open; component mathematics is insufficient. |
| Source preservation | pending | General frontend correspondence remains [open](../formal-core.md). |
| Specification review | pending | Independent community review of mathematical intent/conventions remains required. |

## Adoption and teaching

H supplies paths, controlled quarter phase Fourier interference, final routing coordinates.
Read [client](../../corpus/qualtran/qft2/main.qli)/[case](../../corpus/qualtran/qft2/README.md)
with source. Uniform Z probabilities/inverse round trip do not distinguish forward,
inverse/reversal/scalar errors; future candidates need phase/reference and controlled
scalar faults. This pilot creates no new test execution or API. [QFT components](../../lean/Qleisli/Qft.lean)
prove separate scopes. Retain Apache-2.0/Qualtran notices; adoption requires multiple/
held-out clients, independent review and compatibility.
