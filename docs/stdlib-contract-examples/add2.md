# Reference contract: existing modular Add2

Status: **contract-writing pilot for an existing experimental API**.
The [conventions](../../STDLIB.md) add no generalized `add_mod2n` API.

## Meaning

Ledger A002, contract version 1, fixes
`|a,b> -> |a,(a+b) mod 4>` with amplitude +1 for all `0<=a,b<4`.
This preserves the first basis label, overwrites an arbitrary initial destination
and wraps overflow. Tensor with identity on arbitrary references; no extra
input-dependent phase is allowed.

## Interface and encoding

[Reference code](../../stdlib/src/arithmetic.qli): ordinary
`pub unitary fn add2(q: Q<((Bit, Bit), (Bit, Bit))>) -> Q<((Bit, Bit), (Bit, Bit))>`.
The first pair is the addend `a=a0+2*a1`; the second is the destination
`b=b0+2*b1`. Consume and return all four wires in their documented positions.
The nested pairs are not implicitly interchangeable with a flat four-tuple.

## Premises and capabilities

Exactly two unsigned two-bit integers; accept all sixteen input pairs and
arbitrary correlated superpositions. The destination need not start at zero.
No scratch or external oracle access is required. Supported static transformations
retain phase and current budgets. Wrong trees, reused owners and exceeded
limits reject; no general integer/modulus parameters are exposed.

## Ancillas and effects

`Unitary`, no scratch, measurement or discard. Both registers are retained.
The first register's basis label is preserved; its reduced state can change
through entanglement with the destination. Current source consumes/returns
owners; this contract grants no read-only quantum borrowing permission.

## Approximation

None. The ideal permutation has amplitude +1 on every basis image. Classical
input/output agreement cannot rule out an extra relative phase.

## Resources

Logical source model: four live data qubits, zero scratch, one Toffoli and two
CNOT applications, three splits and three joins. The carry uses the original
low bits before overwriting `b0`. Physical synthesis/depth and a quantitative
bound theorem are pending; [arithmetic scope](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md)
does not imply a general efficient adder.

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | checked | Four-qubit production corpus wrapper passes; [existing validation record](../../corpus/validation-v0.2.2.json). |
| Semantic tests | tested | All complex columns including phase at tolerance 1e-11, [independent modular oracle](../../scripts/check_input_corpus.py) and [case contract](../../corpus/qualtran/add2/README.md); [reference round-trip regression](../../tests/order_finding.rs) is separate evidence. No new semantic run is implied by this pilot. |
| Actual IR conformance | pending | A theorem bound to the complete emitted adder IR and specified permutation remains required; existing finite tests are not it. |
| Source preservation | pending | Complete source/IR correspondence remains open; [formal-core obligations](../formal-core.md). |
| Specification review | pending | A002's phase/order/wrap contract is retained; independent community review of the pilot remains to be recorded. |

New candidates need wraparound, nonzero destination, changed carry/order and
extra-phase faults. A scratch-using replacement also needs exact clean-return
and reference checks; zero measurement probability alone is insufficient.
Passing classical basis outputs and an inverse round trip cannot establish the
phase-fixed contract. These fault requirements are not claims of newly executed
tests in this documentation packet.

## Adoption and teaching

This is existing A002, not a generalized standard adder. Read its carry ordering,
the [corpus client](../../corpus/qualtran/add2/main.qli) and the
[arithmetic/order-finding explanation](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md) together.
For a future scratch-using adder, document the encoded zero-scratch entry and
all-state cleanup equation separately from whole-space unitarity. Preserve
Apache-2.0 source and Qualtran client notices. Future adoption still needs
reviewed reuse, a held-out client and public compatibility analysis.
