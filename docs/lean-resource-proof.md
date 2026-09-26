# Lean resource-accounting and Kraus theorem ledger

Status: **R1-accounting projection and five local Kraus algebra lemmas machine checked;
full source mechanization open**
(2026-09-26). This English ledger records the scope of the
[Lean development](../lean/README.md). It refines the
[paper resource rules](source-resource-rules.md) without adding source syntax,
sealed operations, acceptance rules, or public standard-library APIs.

The resource model in §§1–5 remains separate from the exact matrix model in
§6. Combining their existence does not establish a connection between source
typing and quantum operators. The source rule system's
[ideal soundness Q1–Q3](source-soundness.md) is a paper proof, not a theorem
mechanized here.

## 1. Exact statement and model

`Basis` is the exact `Unit | Bit | pair Basis Basis` tree, with width 0, 1,
or the sum of the child widths. A `Port` is `(slot, basis)`. A symbolic `Value`
is unit, a classical identifier, a quantum port, or a pair of values. Its
ownership footprint is an occurrence **list**, with pair footprints appended.
Classical leaves contribute zero occurrences; every quantum leaf contributes
one, including `Q<Unit>`.

A `Register` contains a typed port, an SSA token, and an ordered wire list.
A `Config` contains all current holders and a finite register store. Holders
include visible values, pending tuple fields or actual arguments, suspended
caller values, and protected resources. Their roles are erased in this
projection: lexical names, spent markers, and scopes are not encoded.

`Config.Valid c` asserts:

1. `own(c.holders)` is a permutation of `ports(c.store)`, including exact basis
   trees and occurrence multiplicities.
2. Live store slots and tokens are each duplicate free; concatenating all wire
   lists also gives a duplicate-free list.
3. Each register's wire count equals its basis width.

The main theorem is `Qleisli.CheckedRun.preserves`:

```text
CheckedRun input output → Config.Valid input → Config.Valid output
```

The associated `Config.Valid.unique_holders` theorem makes all holder slot
occurrences duplicate free. `closed_classical_no_resources` proves that a valid
configuration with an empty holder footprint has an empty store. These are
general theorems over finite lists, not bounded enumerations.

No quantum state appears in `Config.Valid`. It neither assumes nor concludes
that separately owned registers are unentangled. It does not establish
physical no-cloning, complete positivity, trace preservation, or unitarity.

## 2. Transition premises and trust boundary

`Action` models the resource shape of initialization, one-/two-/three-register
gates, split, join, lift, measurement, discard, and reset. `Action.preserves`
derives local output validity from input validity and shape-specific premises:
split has distinct output slots/tokens and component widths; lift has the
target width and fresh appended wires; multi-register gates have distinct
replacement tokens. Output validity itself is **not** a constructor premise.

`Replacement` partitions the old store into the consumed registers and an
unchanged frame, applies an `Action`, and requires:

- Complete local coverage of the produced registers by result holders.
- Complete typed coverage of the frame by suspended holders.
- Disjoint produced/frame slots, tokens, and wires.
- The output holders/store are the specified local result plus that frame.

`Replacement.preserves` derives full output validity from these local
conditions. `Replacement.input_coverage` recovers complete input coverage by
the consumed interface plus suspended holders; `frame_preserved` retains
every original frame register. The caller has to establish these local
interface conditions. This development does not yet prove that the Rust
lowerer always establishes them.

The model tracks **live uniqueness**, not the issued-identifier history `H`
of the paper rules. It permits some histories that the source/IR checker
rejects, such as reusing an already retired token. Similarly, `Action.lift`
checks resource width/freshness but contains no basis injection; `Action.gate`
contains no gate matrix or effect proof. `discard` is a resource termination
event, not permission for pure cleanup. Measurement's classical outcome and
reset's physical channel are not represented. The sealed-operation semantics
and source effect rules remain separate obligations.

`ResourceRun` composes local edits and ownership-preserving rearrangements.
`CheckedRun` adds sequencing and two checked arms from the same input,
followed by a complete resource phi. It is an explicit resource-event
derivation, not the source typing/evaluation judgment and not an executable
`.qli` checker.

## 3. Phi and frame scope

`Renaming` supplies total injective maps on slot, token, and wire identifiers.
It retains exact basis trees, maps every register and every quantum holder,
and preserves all validity conditions. `slot_coverage` gives a preimage for
every output slot; injectivity makes the preimage unique. `slot_count` retains
the number of ownership slots even when some widths are zero.

`BranchPhi` relates each entire arm to a common output store up to permutation,
and relates its renamed typed ownership occurrences to the output holders.
Both arm maps are total, so frame and zero-width registers cannot be omitted.
`BranchPhi.preserves` establishes validity for either runtime arm and the
common output. `Renaming.frame_ports` additionally proves exact frame slot and
basis preservation **when the renaming fixes those frame slots**. The abstract
`BranchPhi` alone does not enforce this source-specific fixed-frame condition.

Total injectivity is stronger than Rust's finite live-set checks. Extending
each accepted finite Rust mapping to this abstract renaming is unproved.
Result-position matching, equality of consumed outer bindings, exact source
result type trees, fresh global phi IDs, and simultaneous classical SSA scope
checking are also not yet derived here. Only typed quantum footprints are
compared, so classical data and full mixed-value structure remain outside the
phi theorem. The paper's tensor-axis/reference-system meaning lemma has not
been ported to Lean by proving this identifier-renaming result.

## 4. Theorem ledger

All entries marked **checked** are proved by Lean without proof holes or
project-specific axioms. Names below are in namespace `Qleisli`.

| ID | Status | Lean declaration(s) and contract |
| --- | --- | --- |
| RA-1 | Checked | `Config.Valid.unique_holders`: valid typed coverage implies unique holder slots |
| RA-2 | Checked | `pair_ownership`, `pair_preserves`: pair construction/destructuring redistributes the same occurrences |
| RA-3 | Checked | `pending_frame`, `call_frame`: moving pending values or arguments across the holder/frame partition preserves occurrences |
| RA-4 | Checked | `copy_classical`: copying requires an empty footprint; `quantum_unit_owns`: zero-width quantum values still own a slot |
| RA-5 | Checked | `Action.preserves`: resource shapes of all listed local events preserve store validity under their explicit premises |
| RA-6 | Checked | `Replacement.preserves`, `input_coverage`, `frame_preserved`: complete local interfaces extend over an unchanged disjoint frame |
| RA-7 | Checked | `Renaming.preserves`, `slot_coverage`, `slot_count`, `frame_ports`: complete injective renaming; frame identity has an explicit fixed-slot premise |
| RA-8 | Checked | `BranchPhi.preserves`: each entire arm agrees with a common valid resource interface |
| RA-9 | Checked | `ResourceRun.preserves`, `CheckedRun.preserves`: induction over resource-event derivations, including branches |
| RA-10 | Checked | `closed_classical_no_resources`: valid empty ownership footprint implies empty store |
| R1-source | Paper proof; full mechanization open | Source binders, type/effect derivations, scope, history, static/computed forms, and correspondence to the projection |
| IR/source adequacy | Open | Establish the Rust lowerer/verifier premises and relate every accepted execution to the model |
| Full quantum meaning | Open in Lean | Section 6 proves only local matrix composition; sealed source operations, instruments/trace, auxiliary zero return, references, and source-to-IR preservation are not mechanized |

RA-3 proves ownership redistribution, not semantic substitution or preservation
of lexical name resolution. RA-5 proves resource validity, not that an event's
matrix has the claimed quantum effect. The distinction is part of each
contract and must remain when extending this ledger.

## 5. Reproduction and evidence

See the [Lean README](../lean/README.md) for commands. Lean and Mathlib are
pinned to 4.30.0; the transitive dependency commits are locked in
[lake-manifest.json](../lean/lake-manifest.json).

[Examples.lean](../lean/Qleisli/Examples.lean) contains 13 named boundary lemmas:
mixed/zero-width ownership, splitting a unit-and-bit register, explicit
zero-width discard with a retained frame, pending mixed pair construction,
and a zero-width-result/bit-frame phi; rejection of duplicate or implicitly
dropped zero-width ownership, shared tokens, aliased wires, wrong width,
wrong basis, and an omitted zero-width phi result. They use exact proof terms
and kernel reduction. Some quantify over arbitrary identifiers or branch
choices rather than enumerating them.

[Audit.lean](../lean/Audit.lean) checks transitive axiom dependencies of every
declaration in the imported project modules. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; the current development uses all three. These
are Lean's standard logical axioms, not additional quantum assumptions.
`sorryAx`, native-evaluation axioms, and custom axioms fail the audit. Warnings
are build errors. The root-import coverage check prevents an unimported proof
module from escaping the audit.

The [CI workflow](../.github/workflows/ci.yml) runs Lean build/audit, Rust
tests/fmt/Clippy, and [local documentation/import checks](../scripts/check_docs.py).
The workflow is added here; a hosted GitHub Actions result is not claimed until
the branch is pushed and those jobs actually run. Rust's finite regression
tests remain implementation evidence, not proof of adequacy for these models.

Historical resource-projection validation on 2026-09-26:

- `lake build`: passed, including all 13 boundary lemmas.
- `lake env lean -DwarningAsError=true Audit.lean`: passed; 449 declarations,
  using only the three allowed standard axioms.
- Temporary negative audit probes for a custom axiom, a proof hole, and
  `native_decide` were rejected by the audit; they are not library sources.
- `cargo test --all-targets`: 115 passed; `cargo fmt --check` and
  `cargo clippy --all-targets -- -D warnings`: passed.
- Documentation/import check: 263 local targets and 5 root-imported modules
  checked. Workflow YAML parsing and `git diff --check` passed.

## 6. Local Kraus completeness algebra

[Kraus.lean](../lean/Qleisli/Kraus.lean) introduces namespace `Qleisli.Kraus`
and exact rectangular matrices over `Complex`. Rows index the output and
columns the input. For a finite family `A`, the definition is

```text
Complete A := sum_i (A i)† * A i = I.
```

The summation and intermediate/output index types are finite. Input indices
need only decidable equality in the Lean statements, since no summation
ranges over them; finite source interfaces instantiate this more general
matrix identity. The two-stage lemmas use fixed intermediate/output index
types and finite outcome sets, not history-dependent spaces or dependent
outcome families.

| ID | Checked declaration | Explicit premise and conclusion |
| --- | --- | --- |
| KA-1 | `singleton_complete` | `V†V=I` gives completeness of the one-outcome family indexed by `Unit`. |
| KA-2 | `isometry_postcompose_gram` | `P†P=I` gives `(PA)†(PA)=A†A` for any compatible rectangular `A`. |
| KA-3 | `isometry_comp` | `A†A=I` and `P†P=I` give `(PA)†(PA)=I`. |
| KA-4 | `complete_postcompose` | A complete `A_i` and isometric `P_i` for every outcome give completeness of `P_i A_i`. A unitary phi layout meets this premise. |
| KA-5 | `adaptive_complete` | A complete `A_i` and a complete family `B_(i,j)` for every `i` give `sum_i sum_j (B_(i,j) A_i)†(B_(i,j) A_i)=I`. |

These proofs establish algebraic composition, not positivity, trace
preservation, the meaning of hidden measurement outcomes, or a source
interpreter. KA-5 permits a different continuation at every first outcome;
the source semantics separately restricts dependence to visible classical
records. The wider paper Q2 allows history-dependent dimensions, proves CP
and trace statements, and handles public grouping and arbitrary references.
None of those additional parts has been inferred to be Lean-checked.

Validation on 2026-09-26 after adding the module:

- `lake build`: passed with warnings treated as errors.
- `lake env lean -DwarningAsError=true Audit.lean`: **456 declarations**,
  depending only on `propext`, `Quot.sound`, and `Classical.choice`.
- The root imports the new module, so existing CI build, axiom audit, and
  import-coverage checks include it. No dependency or toolchain version changed.

The earlier 449-declaration/13-boundary-lemma record remains historical
evidence for the resource projection. This addition has one definition and
five lemmas, with seven new audited declarations including a generated helper.

## 7. Next milestones

Lean work is limited to lemmas that help the language specification, semantics,
and IR correspondence. The user's request permits this targeted Kraus
extension; it does not make full mechanization the primary work. The following
are outstanding obligations, not a commitment to port each one to Lean now.

1. Encode lexical bindings, spent markers, type/effect judgments, issued-ID
   history, and result-position/fixed-frame/classical-scope phi premises. Prove
   that each successful source rule produces a checked resource derivation.
2. Establish source/checker/IR adequacy for that extended model. Existing
   implementation audits and regression tests identify cases but do not
   discharge the universal correspondence.
3. Relate the paper source denotations, Q1–Q3 and source-to-IR correspondence
   to a suitable mechanized model if it resolves an important specification
   obligation. KA-1–KA-5 alone does not provide that relation.

SPEC-3, SPEC-4, and Stage 1 remain open. The machine-checked milestones are
RA-1 through RA-10 and KA-1 through KA-5 with reproducible checks, not a
complete formal verification of the language or implementation.
