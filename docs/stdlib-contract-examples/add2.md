# Existing Add2 contract v1 (A002)
Experimental two-bit routine, not general add_mod2n; [conventions](../../STDLIB.md).
## Meaning
|a,b>->|a,(a+b)mod4>,+1/all sixteen labels/arbitrary reference; arbitrary destination/wrap/addend retained/no phase.
## Interface and encoding
[Source](../../stdlib/src/arithmetic.qli) pub unitary add2:Q<((Bit,Bit),(Bit,Bit))>->same,a=a0+2a1/b=b0+2b1; four positions retained,flat tuple converts explicitly.
## Premises and capabilities
Unsigned two-bit/correlated inputs/nonzero destination; static phase/access/budgets apply. Wrong tree/reuse/limits reject; no general modulus/size.
## Ancillas and effects
Unitary/no scratch/observation/discard; retained addend need not unchanged reduced state,no borrow.
## Approximation
None; classical labels alone exclude no phase.
## Resources
Four wires/Toffoli/two CNOT/three split+join; original-low carry before overwrite. Physical depth/synthesis/resource theorem pending.
## Validation and proof status
| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | [Production replay](../../corpus/validation-v0.2.7.json). |
| Semantic tests | tested | [Independent full complex columns](../../scripts/check_input_corpus.py),1e-11; numerical only. |
| Actual IR conformance | pending | Actual emitted-body theorem open. |
| Source preservation | pending | General frontend correspondence open. |
| Specification review | pending | Independent intent/convention review required. |

## Adoption and teaching
[Client](../../corpus/qualtran/add2/main.qli)/[case](../../corpus/qualtran/add2/README.md). Require wrap/nonzero/wrong carry/order/phase faults; scratch replacements encoded entry/reference-stable cleanup,not inverse alone. Preserve Apache-2.0/Qualtran notices; reviewed reuse/held-out compatibility before adoption. Pilot itself executes no new faults.
