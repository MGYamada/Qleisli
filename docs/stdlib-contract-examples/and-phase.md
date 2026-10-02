# Corpus AND phase contract
Case-local pilot,not std API; [conventions](../../STDLIB.md).
## Meaning
f=a and b,O_f|a,b>=(-1)^f|a,b>,diag(1,1,1,-1)/every reference; upstream And adaptation,not original signature.
## Interface and encoding
[Source](../../corpus/qualtran/and_phase/kernel.qli) pub unitary kernel:Q<(Bit,Bit)>->same; private both:Bit,weights1/2/marked3,positions retained.
## Premises and capabilities
Total four-label XOR predicate,no state promise/noninjective lift. Protected Z; reuse/unsupported/table/work reject.
## Ancillas and effects
Unitary/two data/one fresh-zero flag, Cf;Z;Cf†|x,0>=(-1)^f|x,0>; exact separated zero for every reference,structured checker not comments. No measurement/discard/escape.
## Approximation
None; polarity/scalar sign matters under control.
## Resources
One Z/two four-entry XOR predicate applications; not physical gate/T-count/upstream measured uncompute. Depth/resource theorem pending.
## Validation and proof status
| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | [Production replay](../../corpus/validation-v0.2.7.json). |
| Semantic tests | tested | [Independent full complex columns](../../scripts/check_input_corpus.py),1e-11; numerical only. |
| Actual IR conformance | pending | Actual emitted-body theorem open. |
| Source preservation | pending | General frontend correspondence open. |
| Specification review | pending | Independent intent/convention review required. |

## Adoption and teaching
[Client](../../corpus/qualtran/and_phase/main.qli)/[case](../../corpus/qualtran/and_phase/README.md): compute flag/phase/uncompute workspace. Require predicate/sign/controlled-scalar/dirty-flag faults and exposed actual scratch checks; factored numerics not literal cleanup. No pilot fault runs/new source; Google/Qleisli Apache-2.0 notices and reuse/name/review/evidence gates required.
