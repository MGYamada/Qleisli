# Reference contract: existing QFT2

Status: **contract-writing pilot for an existing experimental API**.
The [conventions](../../STDLIB.md) add no generalized `qft` API.

## Meaning

Ledger F001, contract version 1, fixes
`F4|x> = (1/2) sum_(y=0..3) exp(2*pi*i*x*y/4)|y>` for every input,
including exact scalar phase. Tensor with identity on arbitrary references.
In particular `F4|1> = (|0> + i|1> - |2> - i|3>)/2`.

## Interface and encoding

[Reference code](../../stdlib/src/transforms.qli): ordinary
`pub unitary fn qft2(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)>`.
For input `(a,b)`, `x=a+2*b`; the same weights decode the returned two positions.
Consume/return the complete owner. The body's `join(b,a)` includes the reversal
needed for this output convention; removing it changes the operator. Displayed
strings list tuple leaves, so `10` here encodes integer 1.

## Premises and capabilities

Exactly two qubits, all four basis inputs and arbitrary superpositions;
no zero-input or eigenstate promise. Current static inverse/control/repetition
use the eligible closed unitary path and its budgets. Wrong types, aliased/
consumed owners and exceeded limits reject. No arbitrary widths are promised.

## Ancillas and effects

No scratch, measurement or discard. `Unitary`; return both data wires.
References remain outside the operation, although their correlations transform
according to `F4` on the data. No borrow signature or reduced-state preservation
claim is made.

## Approximation

None in the ideal contract. Numerical tests use the separately declared
tolerance; device noise and approximate-QFT variants are outside this API.

## Resources

Logical source model: two live data qubits, zero scratch, two H applications
and two controlled T applications, plus the documented output-axis reversal.
Structural split/join operations are not a claim of free physical routing.
Physical gate/depth costs and a quantitative resource-bound theorem are pending;
[ledger details](../stdlib-contracts.md) retain the expansion-budget scope.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Two-bit production corpus wrapper passes; [existing validation record](../../corpus/validation-v0.2.2.json). |
| Semantic tests | tested | Complete complex columns through coherent X/Y probes at tolerance 1e-11, [independent Fourier oracle](../../scripts/check_input_corpus.py) and [case contract](../../corpus/qualtran/qft2/README.md); the cited record is prior execution, not a new run by this pilot. |
| Actual IR conformance | pending | Bind this emitted finite source body to a conformance theorem. The [hierarchical Fourier components](../../lean/Qleisli/Qft.lean) have different actual-definition scope and do not alone prove this source API. |
| Source preservation | pending | General correspondence for this production compiler remains open; [formal-core obligations](../formal-core.md). |
| Specification review | pending | Existing positive-sign/encoding contract is retained; independent community review of this pilot and convention remains to be recorded. |

Compare the actual forward operation to the independent Fourier formula.
Uniform Z probabilities cannot distinguish `F4` from its inverse, and
`U†U=I` alone cannot select `U=F4`. Require sign/reversal faults and a controlled
scalar-phase fault in any new candidate's acceptance experiment; those are
review requirements, not claims that this pilot added or executed those faults.

## Adoption and teaching

This is existing F001, not a newly adopted generalized component. H creates
equal paths; the controlled quarter phase introduces the Fourier interference;
the final owner order selects the advertised coordinates. Read the small
[corpus client](../../corpus/qualtran/qft2/main.qli), the [static-operation/QPE
examples](../static-operations.md) and the code together. Qleisli source is
Apache-2.0; the corpus client retains its Qualtran attribution and notice.
Future library growth needs reviewed reuse and migration, not a new `verified`
badge on this pilot.
