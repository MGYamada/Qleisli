# Reference contract: corpus AND phase oracle

Corpus-local pilot, not std API/ledger entry; [conventions](../../STDLIB.md).

## Meaning

f(a,b)=a and b, O_f|a,b>=(-1)^f|a,b>, diag(1,1,1,-1), every input/reference.
Adaptation of upstream And, not its original signature.

## Interface and encoding

[Source](../../corpus/qualtran/and_phase/kernel.qli): pub unitary kernel:
Q<(Bit,Bit)>->same, private total both(a,b):Bit. Low weights1/2, marked integer3;
return same data positions/owners. kernel is case-local.

## Premises and capabilities

No state promise; four-label total predicate XOR-computes fresh flag, never noninjective
pure lift. Restricted protected Z; unsupported changes/reuse/table/work limits reject.

## Ancillas and effects

Unitary, one private flag fresh-zero/exactly returns-zero separated: C_f;Z;C_f†|x,0>
=(-1)^f(x)|x,0>, arbitrary references. Structured checker validates cleanup;
comments/document do not certify it. No measurement/discard/escaped flag.

## Approximation

None; marking polarity/scalar sign changes controlled operator despite same basis probabilities.

## Resources

Two data/one flag peak, one Z/two XOR predicate applications of four-entry table;
not physical gate/T-count synthesis or upstream measurement-uncompute cost. Depth/
quantitative resource theorem pending.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Existing production wrapper; [full small-corpus replay](../../corpus/validation-v0.2.6.json). |
| Semantic tests | tested | Complete complex/phase columns, independent [oracle](../../scripts/check_input_corpus.py), tolerance1e-11; numerical evidence is separate from proof. |
| Actual IR conformance | pending | Full theorem for this actual source/emitted body remains open; component mathematics is insufficient. |
| Source preservation | pending | General frontend correspondence remains [open](../formal-core.md). |
| Specification review | pending | Independent community review of mathematical intent/conventions remains required. |

## Adoption and teaching

Coherent compute turns predicate into flag, Z into phase, uncompute retains phase and
removes workspace. Read [client](../../corpus/qualtran/and_phase/main.qli)/[case](../../corpus/qualtran/and_phase/README.md).
Future candidates need wrong-predicate/sign/controlled-scalar/dirty-flag faults and
actual scratch checks where exposed; factored simulation proves no literal cleanup.
No new fault runs claimed here. Retain Google/Qleisli Apache-2.0 notices; standard
adoption needs independent reuse/reviewed name/evidence gates, no new upstream source.
