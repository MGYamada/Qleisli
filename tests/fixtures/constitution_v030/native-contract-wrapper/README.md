# Original-root encoded wrapper correspondence

This proof unit closes the full-axis wrapper/operator correspondence gap in the
encoded native-contract branch. It adds no acceptance rule, wire format,
reference meaning, axiom, or admitted guarantee. The broader QS/PR/RS obligations
keep their existing status.

`Wrapper.circuitMatrix_entries` starts with success of the existing executable
`circuitMatrix [⟨signature, meaning⟩] (contractCircuit signature)`. It proves the
returned matrix has the same dimensions and every bounded complex coefficient
as `meaning`. The proof follows the actual zero omission, accumulation and
row-major reconstruction, proving the ordered full-axis gather/scatter laws for
all widths, including zero. It does not assume the desired matrix equality.

`Wrapper.check_encoded_original` transfers the executable finite check's encoded
equation to the original dependency matrix. `encoded_meaning` then obtains that
dependency from the actual root reconstruction, with its original `BodyMeaning`,
fresh graph `RootMeaning`, exact Basis interface and whole-space inverse laws.
The root, reconstruction and finite check retain their continuous work states.
`check_encoded_sound` composes this result with the actual byte checker and its
original-byte/request `Acceptance` witness. `encoded_reference` includes every
joint input/reference amplitude function without separability or normalization
premises.

This is a theorem about the Lean executable definitions. Rust rematerialization,
source/compiler preservation, compiled I/O or binary attestation, clean release,
runtime/export correctness and quantitative resources remain outside this unit.
No lemma is automatically promoted into the constitutional guarantee ledger.

## Preserved evidence

- `Review.lean` and `review-types.*` expose the closed public theorem types,
  `EncodedMeaning` fields and axiom dependencies. All seven printed theorem
  dependency sets contain only `propext`, `Classical.choice` and `Quot.sound`.
- `Examples.lean` uses exactly three small operators: scalar Unit with phase
  −1, T, and a two-bit permutation with asymmetric phases. The latter sends
  columns `0,1,2,3` to rows `1,3,0,2` with phases `1,T,i,−1`, respectively.
  Nine executable assertions check reconstruction, matching-contract acceptance
  and rejection of a plus-one, inverse-T or transposed target. Five of the small
  concrete equalities are additionally proved by ordinary `decide`.
- `attempts/` retains the concrete two-bit full-contract reduction's heartbeat
  diagnostic. Its operational assertion passes. This elaboration-budget limit
  is separate from the generic proof, which uses the default heartbeat budget.
  No `native_decide` proof oracle or new maximum-size case is used.
- `source-comparison.json` records byte-identical semantic sources and QIRF
  contract source against commit `44e23e4`; existing NativeContract declaration
  tokens are unchanged after removing the appended proofs/structure and import.
- `validation.json` binds these local records and production proof files. Full
  package audit, registry refresh and fresh replay are coordinated separately;
  their authoritative results remain in the repository's registry workflow.

Run from `lean/`:

```sh
lake build Qleisli.NativeContract
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/native-contract-wrapper/Review.lean
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/native-contract-wrapper/Examples.lean
```
