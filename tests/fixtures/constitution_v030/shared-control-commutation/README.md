# Shared control of disjoint target factors: bounded component of #303

This is an informed proof and small checking experiment over existing operator
definitions, based on commit `fae0e6a149f5b218bcc7f67f38d9509eb8aeb4f3`.
It adds no source syntax, access/borrow contract, optimizer transformation,
acceptance rule, semantic definition or admitted guarantee. Issue #303 remains
open for its general contract and implementation. No model-success claim follows
from this development record.

`lean/Qleisli/SharedControlCommutation.lean` proves five statements:

1. `block_tensor_commute`: for an arbitrary finite common control basis `B`,
   the block operators with sectors `U b ⊗ I` and `I ⊗ V b` commute. The ordered
   target widths are `n` and `m`, and each family consists of square complex
   matrices of its stated width. There is no unitarity or separability premise.
2. `controlled_tensor_commute`: the actual existing first-bit coherent-control
   matrix construction commutes for these two ordered tensor factors. The proof
   specializes the general block theorem to `Bool` and transports it through the
   existing `Fin.consEquiv` coordinate map. The arbitrary-`B` theorem does not
   claim that the single-control IR constructor implements every control type.
3. `apply_controlled_tensor_commute`: the result follows for actual hierarchy
   `apply` bodies, using `.control true` over `.tensor [U, identity m]` and
   `.tensor [identity n, V]`. It derives their matrices from the actual control
   and tensor definitions. It does not assume commutation of those operators.
   Input and output widths of both interfaces and leaf operators are explicit;
   width equality alone does not certify source types or owner permissions.
4. `apply_sequence_adjacent_swap`: only these two adjacent operators are
   exchanged inside an actual hierarchy `.sequence`. Every original prefix
   and suffix operator remains in order and must have the joint square width.
   List execution order and matrix multiplication order are accounted for.
5. `apply_sequence_adjacent_swap_reference`: these actual sequences act
   identically at every joint/reference amplitude, for any reference type and
   state, with no finiteness, normalization or product-state premise on it.

All identities retain exact scalar phase and the existing control/target axis
order. Widths `n` or `m` may be zero: the corresponding scalar factor still
contributes its phase. This does not merge `Q<Unit>` owners or infer access
rights from zero physical width. The theorem covers the actual single Boolean
true-control constructor and the stated ordered tensor fragment; it is not a
general routing or typed-footprint theorem.

The results establish neither native byte-checker acceptance nor preservation
of success, failure, work consumption, source evaluation, Rust rematerialization
or compiled runtime behavior. The finite examples below independently exercise
existing executable definitions; this fixture adds no finite/hierarchy codec
correspondence theorem. No PR or quantitative RS obligation is discharged and
the guarantee ledger is unchanged.

## Small examples and retained counterexamples

`Examples.lean` first runs sixteen actual finite-matrix assertions against
independently written exact coefficient matrices. Axis order is `C,A,B`, with
the common control at the least-significant position.

| Case | Matrix | Assertions |
| --- | --- | --- |
| Shared control: H on A, X on B | 8 by 8 | Both orders |
| Shared control: X on A, T on B | 8 by 8, asymmetric phase-bearing example | Both orders |
| A has width zero and scalar −1; H on B | 4 by 4 | Both orders |
| T on A; B has width zero and scalar −1 | 4 by 4 | Both orders |
| Both target factors have width zero, scalars −1 and T | 2 by 2, enabled phase exponent 5 | Both orders |
| Same scalar pair with literal H(C) prefix and X(C) suffix | 2 by 2, retained context | Both orders |
| Shared target: controlled X and controlled Z | Two different 4 by 4 matrices | Each order |
| H on the common control and controlled X on A | Two different 4 by 4 matrices | Each order |

The last two pairs retain counterexamples to dropping the disjoint-target or
common-control-sector condition. Their exact signs and coefficients differ;
they are not equated up to global phase.

Two further executable assertions apply the actual H(A)/X(B) matrices, in both
orders, to the joint amplitude

`|C0,A0,B0,R0> + i |C1,A0,B0,R1>`.

They check every output/reference coefficient against

`|000,R0> + (i/√2) |101,R1> + (i/√2) |111,R1>`

in `C,A,B` order. This unnormalized state retains the cross-sector phase and
reference correlation. The two reference columns are labels, not additional
physical wires. No example exceeds three physical qubits.

Three named mathematical examples are separate from those eighteen runtime
assertions. `unit_phase_visible` reduces the real hierarchy tensor/control
operator and exposes the controlled −1 phase of a zero-width factor, keeping
distinct owner numbers in its literal interface records. The abstract
`four_control_sectors` example retains phases `1, −1, i, −i` for `B = Fin 4`
and zero-width target factors; `four_sectors_commute` instantiates the general
finite-control theorem. This abstract example does not claim a new IR form.

## Recorded validation

The Mathlib package build, its `Audit.lean`, `Review.lean` and `Examples.lean`
all exit successfully. The package enables `warningAsError`; the latter three
commands also pass it explicitly. The audit checks 3,446 Qleisli declarations
and reports only `propext`, `Classical.choice` and `Quot.sound`. All five public
theorems and the three named example theorems have those same axiom dependencies.
No project axiom, placeholder, unsafe definition or partial definition is added.

`Review.lean` prints the public types and actual axiom dependencies. Command
records preserve the actual arguments, working directory, exit codes and
outputs. The eighteen executable assertions are tests, not replacement proofs.

`source-comparison.json` checks all 207 pre-existing non-root Lean sources in
both packages byte-for-byte against the baseline. The sole root-file change is
the new proof module import. This is source identity evidence, not proof
validity or binary attestation. `validation.json` binds the new module and these
fixture records. The native package build/audit, fresh replay and current
guarantee-evidence refresh belong to the separate coordinated registry workflow
and are not claimed by this fixture record.

To replay from `lean/`:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/shared-control-commutation/Review.lean
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/shared-control-commutation/Examples.lean
```
