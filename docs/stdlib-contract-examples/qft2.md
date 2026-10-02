# Existing QFT2 contract v1 (F001)
Experimental,not generalized qft; [conventions](../../STDLIB.md).
## Meaning
F4[y,x]=exp(2*pi*i*x*y/4)/2,every input/full phase/reference identity. F4|1>=(|0>+i|1>-|2>-i|3>)/2.
## Interface and encoding
[Source](../../stdlib/src/transforms.qli) pub unitary qft2:Q<(Bit,Bit)>->same,x=a+2b both ends;join(b,a) reversal/complete owner. Display10 is integer1.
## Premises and capabilities
All labels/correlations,no zero/eigenpromise. Static access/budgets apply; tree/alias/reuse/limits reject.
## Ancillas and effects
Unitary/two data/no scratch/observation/discard/borrow/unchanged-reduced-state promise.
## Approximation
None; numerical tolerance/approximate QFT/noise distinct.
## Resources
Two H/two controlled T/output reversal; routing not physically free/depth-resource theorem pending.
## Validation and proof status
| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | [Production replay](../../corpus/validation-v0.2.7.json). |
| Semantic tests | tested | [Independent full complex columns](../../scripts/check_input_corpus.py),1e-11; numerical only. |
| Actual IR conformance | pending | Actual emitted-body theorem open. |
| Source preservation | pending | General frontend correspondence open. |
| Specification review | pending | Independent intent/convention review required. |

## Adoption and teaching
[Client](../../corpus/qualtran/qft2/main.qli)/[case](../../corpus/qualtran/qft2/README.md): H paths/quarter-phase interference/coordinates. Probabilities/inverse roundtrip miss sign/reversal/scalar faults; require phase/reference/controlled-scalar tests. [Components](../../lean/Qleisli/Qft.lean) separate scope. No pilot execution/API; Apache-2.0/Qualtran notices,multiple+held-out clients/review/compatibility required.
