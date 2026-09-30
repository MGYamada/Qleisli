# Reference contract: corpus AND phase oracle

Status: **contract-writing pilot; corpus-local candidate, not a standard API**.
Follow the [conventions](../../STDLIB.md) before any future adoption.

## Meaning

This pilot fixes `f(a,b)=a and b` and
`O_f|a,b> = (-1)^f(a,b)|a,b>`, hence `diag(1,1,1,-1)`.
All four inputs have exact phase and unchanged data labels; tensor with identity
on any reference. It is a compute/phase/uncompute adaptation of the upstream
And component, not its original signature or a new ledger entry.

## Interface and encoding

[Reference code](../../corpus/qualtran/and_phase/kernel.qli): ordinary
`pub unitary fn kernel(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` with a private
total basis predicate `both(a: Bit,b: Bit) -> Bit`. First leaf has weight 1,
second weight 2; marked label is integer 3. Consume/return the same data owners
in the same positions. The `kernel` name is case-local, not a proposed std name.

## Premises and capabilities

Two data qubits; no initial-state promise. The predicate is total over all
four labels and is used for reversible computation into a fresh flag, not as
a noninjective pure lift to one qubit. The restricted computed body applies
Z to that flag. Unsupported protected changes, reused owners and exceeded
finite table/work limits reject.

## Ancillas and effects

One internal flag starts at zero and returns exactly to zero and separated.
For the restricted implementation, `C_f; Z_flag; C_f†` on `|x,0>` yields
`(-1)^f(x)|x,0>` on every input, extending to correlated references.
The existing structured checker requires the cleanup pattern; the source
comment or contract document issues no cleanup evidence. `Unitary`; no
measurement/discard, and the private flag is not returned to the caller.

## Approximation

None. Wrong marking polarity or a scalar negative changes the operator under
control even when ordinary basis measurement sees the same probabilities.

## Resources

Logical scope: two data qubits and one internal flag at peak, one Z, two
reversible XOR applications of the four-entry predicate table. This is not
a gate synthesis or physical T-count claim; the upstream measurement-based
uncompute and cost formulas are not imported. Exact physical depth and the
future resource-bound theorem are pending.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Production corpus kernel and shipped main pass; [existing validation record](../../corpus/validation-v0.2.2.json). |
| Semantic tests | tested | All complex entries/coherent phases at tolerance 1e-11, [independent predicate oracle](../../scripts/check_input_corpus.py) and [translation contract](../../corpus/qualtran/and_phase/README.md). The cited record is prior execution, not a new pilot run. |
| Actual IR conformance | pending | [Structured cleanup mathematics](../formal-core.md#3-evidence-for-pure-auxiliary-release) states the factorization; a complete actual-checker/source-body conformance theorem is still open. |
| Source preservation | pending | General frontend correspondence remains open; [formal-core obligations](../formal-core.md). |
| Specification review | pending | Upstream specialization and Boolean polarity are explicit; independent community review/adoption of this candidate remains required. |

New candidates need wrong-predicate, reversed marking sign, controlled scalar
and dirty-flag faults. Tests must observe phase/coherence and actual scratch
behavior where exposed by their profile; a factorized simulator cannot supply
an independent literal-cleanup proof. No new faults are claimed by this pilot.

## Adoption and teaching

The Boolean predicate is coherently computed, Z turns its label into phase,
and uncomputation removes private workspace while retaining that phase. Read
the source and [corpus main](../../corpus/qualtran/and_phase/main.qli) together.
This remains a corpus adaptation of Qualtran, with Google and Qleisli
attribution and Apache-2.0 notices retained. Future standard adoption requires
a reviewed public name, independent reuse and the existing evidence gates;
the corpus intake remains exactly the three approved upstreams.
