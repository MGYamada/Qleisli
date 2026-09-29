# Lean resource, scope, Kraus, and semantic-rule theorem ledger

Status: **R1-accounting projection, local lexical scope projection, and five
local Kraus algebra lemmas, and general exact semantic-rule lemmas machine
checked; full source mechanization open**
(2026-09-27). This English ledger records the scope of the
[Lean development](../lean/README.md). It refines the
[paper resource rules](source-resource-rules.md) without adding source syntax,
sealed operations, acceptance rules, or public standard-library APIs.

The resource model in §§1–5, exact matrix model in §6, lexical lookup model
in §7, and experimental semantic-rule support in §9 address distinct obligations.
The lookup model uses the resource
model's values and ownership footprints. Combining these developments does
not establish a connection between source typing and quantum operators.
The source rule system's
[ideal soundness Q1–Q3](source-soundness.md) is a paper proof, not a theorem
mechanized here.

## 1. Exact statement and model

`Basis` is the exact `Unit | Bit | pair Basis Basis` tree, with width 0, 1,
or the sum of the child widths. A `Port` is `(slot, basis)`. A symbolic `Value`
is unit, a classical identifier, a quantum port, or a pair of values. Its
ownership footprint is an occurrence **list**, with pair footprints appended.
Classical leaves contribute zero occurrences; every quantum leaf contributes
one, including `Q<Unit>`.

This model remains binary. The [0.2.0 source type contract](type-system.md)
adds distinct n-ary tuples; its indexed paper rules and Rust regressions do not
extend this Lean model automatically. Establishing their projection and
implementation correspondence remains a separate proof obligation.

A `Register` contains a typed port, an SSA token, and an ordered wire list.
A `Config` contains all current holders and a finite register store. Holders
include visible values, pending tuple fields or actual arguments, suspended
caller values, and protected resources. Their roles are erased in this
`Config` projection: lexical names, spent markers, and scopes are not encoded
there. The separate [scope model](#7-lexical-scope-projection) represents named
lookups and scope exit; it does not add lexical derivations to `Config`.

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
| R1-source | Paper proof; full mechanization open | Source binders, type/effect derivations, scope execution traces, history, static/computed forms, and correspondence to the projections; the local scope-exit theorem in §7 is a separate checked step |
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

Physlib is a [future dependency candidate](physlib-environment.md), removed
from the required environment until a concrete instrument bridge uses it. Its
[preserved optional dependency audit](../research/quantum-libraries/PhyslibAudit.lean)
records the earlier integration experiment. The current Qleisli declarations
and project audit use Mathlib alone; no theorem coverage is lost or added.

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

The coverage scanner reads the initial import header, skipping line comments
and nested ordinary block comments. Text in declaration bodies, including
strings, cannot create import edges. It supports the unquoted module paths
used in this repository; Lean's build remains the authority for parsing and
compiling the source. Regression tests include a custom-axiom module named
only inside a comment, which must be reported as absent from the root audit.

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

Historical Kraus-extension validation on 2026-09-26:

- `lake build`: passed with warnings treated as errors.
- `lake env lean -DwarningAsError=true Audit.lean`: **456 declarations**,
  depending only on `propext`, `Quot.sound`, and `Classical.choice`.
- The root imports the new module, so existing CI build, axiom audit, and
  import-coverage checks include it. No dependency or toolchain version changed.

The earlier 449-declaration/13-boundary-lemma record remains historical
evidence for the resource projection. This addition has one definition and
five lemmas, with seven new audited declarations including a generated helper.

## 7. Lexical scope projection

[Scope.lean](../lean/Qleisli/Scope.lean) models the lookup-level contract of
Rust's [`close_scope`](../src/frontend/compile/lower/scope.rs). A lookup is
`Option (Option Value)`: `none` means an absent name, `some none` a spent
binding, and `some (some v)` a live value. An environment is a function from
an arbitrary name type to these lookups. It need not have finite support.
`Value.ownsQuantum` detects a quantum leaf anywhere in a mixed value and is
equivalent to a nonempty typed ownership occurrence list. In particular,
`Q<Unit>` owns one port despite having zero wires.

The inputs are the entry environment `E`, the current local environment `L`,
and a supplied set `B` of names rebound in the block. `Approved E L B` means
that every live quantum-containing value in `L` has exactly the same value
in `E` and its name is outside `B`. This is equivalent to absence of `Leak`.
The noncomputable specification `Scope.close E L B` succeeds precisely when
`Approved` holds and returns the pointwise projection `Scope.exit E L B`.
Universal approval over a function environment is a mathematical predicate;
this definition is not an executable source checker.

The projection restores the entry domain, spent markers, and classical
values. An entry quantum value survives exactly when its name was not
rebound and its current value is unchanged; otherwise the entry becomes
spent. The rebound premise matters even when a new binder contains exactly
the old slot, basis, and value tree. A local live quantum owner cannot vanish
merely because its name leaves scope.

The following declarations are **checked**. Names are in `Qleisli.Scope`
unless qualified as `Value` in namespace `Qleisli`.

| ID | Lean declaration(s) | Contract |
| --- | --- | --- |
| SC-1 | `Value.ownsQuantum_eq_false_iff`, `Value.ownsQuantum_eq_true_iff`, `quantum_unit_is_linear` | The guard agrees with the exact ownership footprint, including mixed and zero-width quantum values. |
| SC-2 | `approved_iff_no_leak`, `close_eq_none_iff`, `close_eq_some_iff`, `close_rejects_leak` | Approval is absence of a leaking name; closure succeeds exactly with the specified projection and rejects a leak. |
| SC-3 | `exit_absent`, `exit_spent`, `exit_classical`, `exit_domain` | Projection restores absent/spent/classical entry lookups and exactly the entry domain. These projection equalities do not require approval. |
| SC-4 | `exit_quantum_keep_iff`, `approved_quantum_retained` | An entry quantum value is retained exactly when unchanged and unrebound; every current live quantum value survives an approved projection. |
| SC-5 | `introduced_quantum_rejected`, `rebound_quantum_rejected` | A live quantum owner introduced under an absent name or a rebound name is rejected, including equal-value rebinding. |
| SC-6 | `exit_footprint`, `close_preserves` | Successful closure preserves the entry domain and the current typed quantum occurrence list at every name. |
| SC-7 | `exit_footprintOn`, `close_footprintOn` | Under approval or successful closure, concatenating footprints over any finite name list gives the same ordered occurrence list before and after projection. |

These theorems impose no fixed bound on names or value-tree size. To read
SC-7 as the entire footprint of finite Rust maps, choose a duplicate-free
name list covering both map domains. The mathematical equality itself also
holds for incomplete or repeated name lists; it does not supply that coverage
premise or establish unique quantum ownership by itself.

The [lowering-state refinement](lowering-state-refinement.md) gives the
paper correspondence between the two Rust passes and this projection. It
also records finite implementation checks using an explicit binder-identity
oracle and [source regressions](../tests/source_scope.rs). The helper's
read-only rejection pass leaves the entry map unchanged on failure and
reports its first leaking name in map order. The Lean specification models
success or failure, not that diagnostic ordering or the mutable execution.
The block result, suspended holders, register store, and emitted IR are
outside this lookup model; the helper does not modify them.

The environment snapshots and rebound set are premises, not a derivation of
lexical identity from an execution trace. Mechanizing Rust's finite-map/value
representation, proving that every successful lowering path constructs the
required inputs, and connecting this result to complete `Config.Valid`
coverage remain open. Restoring classical lookups does not establish
classical SSA scope or data flow for every source execution. SC-1–SC-7 do not
prove source type/effect preservation, issued-ID freshness, quantum operator
meaning, or compiler/verifier adequacy.

Scope-extension validation on 2026-09-27:

- `lake build`: passed with warnings treated as errors.
- `lake env lean -DwarningAsError=true Audit.lean`: **527 project
  declarations**, depending only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `Qleisli.lean` imports `Scope`, so the build, transitive axiom audit, and
  root-import coverage check include it. The toolchain and dependency pins
  are unchanged.

This validation is separate from the historical 449- and 456-declaration
records above. Rust validation results are recorded with the
[implementation evidence](lowering-state-refinement.md#6-finite-implementation-evidence-and-next-step).

<a id="7-next-milestones"></a>

## 8. Next milestones

Lean work is limited to lemmas that help the language specification, semantics,
and IR correspondence. The targeted Kraus and scope developments do not make
full mechanization the primary work. The following are outstanding obligations,
not a commitment to port each one to Lean now.

1. Extend the lookup model to lexical execution traces, type/effect judgments,
   issued-ID history, and result-position/fixed-frame/classical-scope phi
   premises. Prove that each successful source rule produces a checked
   resource derivation and establishes the scope-projection premises.
2. Establish source/checker/IR adequacy for that extended model. Existing
   implementation audits and regression tests identify cases but do not
   discharge the universal correspondence.
3. Relate the paper source denotations, Q1–Q3 and source-to-IR correspondence
   to a suitable mechanized model if it resolves an important specification
   obligation. The local Kraus and scope lemmas do not provide that relation.

SPEC-3, SPEC-4, and Stage 1 remain open. The machine-checked milestones are
RA-1 through RA-10, KA-1 through KA-5, SC-1 through SC-7, and the local
SEM rules below with reproducible checks, not a complete formal verification
of the language or implementation.

## 9. General exact semantic rules for experimental evidence design

[SemanticContract.lean](../lean/Qleisli/SemanticContract.lean) supports an
experimental design for composing symbolic meanings and evidence. It proves
general finite-dimensional matrix identities over `ℂ`, without a fixed bit
bound and without enumerating matrix entries when composing the proofs.
These are local semantic-rule lemmas, separate from an executable symbolic
checker, the current Rust implementation, and the language's accepted syntax.
They add no Rust or `.qli` API and require no new dependency or toolchain.

`Qleisli.SemanticContract.Encoded U Ein Eout u` states the exact,
phase-sensitive equality `U * Ein = Eout * u`. Rows index outputs and columns
index inputs. This relation alone does not establish physical admissibility:
`Isometry U` separately means `Uᴴ * U = I`, and `Unitary U` additionally
requires `U * Uᴴ = I`. An admissible encoded operation must establish its
encoding isometries and the operation's required isometry/unitarity as well
as the equality. Owning a theorem does not establish that a runtime state is
in the input encoding's image or that its quantum resources are owned.

The following **20 theorems are checked** in namespace
`Qleisli.SemanticContract`:

| ID | Lean declarations | Contract and restrictions |
| --- | --- | --- |
| SEM-1 | `encoded_identity`, `encoded_seq` | Identity and sequential equality. The intermediate encoding has identical entries, typed coordinates, and interface; equal dimensions or equal images alone are insufficient. |
| SEM-2 | `encoded_tensor`, `encoded_reference` | Tensor composition and extension by any finite reference identity. The operator equality covers entangled inputs; no product-state premise is used. Disjoint resource placement remains separate. |
| SEM-3 | `isometry_identity`, `isometry_seq`, `isometry_tensor`, `unitary_identity`, `unitary_seq`, `unitary_tensor`, `unitary_adjoint` | Preserve whole-domain isometry/unitarity through the stated algebraic operations. These properties are not inferred merely from matching resource interfaces. |
| SEM-4 | `encoded_adjoint` | Swap encodings and take adjoints when both physical and logical operations are unitary. The physical left-inverse and logical right-inverse equations are used; a logical isometry alone does not authorize this rule. |
| SEM-5 | `encoded_control`, `isometry_controlEncoding`, `unitary_control` | Control preserves equality with the same exact encoding in both sectors; the encoding stays isometric and control of a unitary stays unitary. This does not grant controlled access to an unknown external operation. |
| SEM-6 | `compute_uncompute`, `zeroEncoding_isometry`, `encoded_zero_leakage`, `compute_uncompute_zero_leakage` | From `W (C E0) = (C E0) u` and `CᴴC=I`, derive `(CᴴWC) E0=E0u`. For the specified zero-ancilla encoding, every nonzero-ancilla output amplitude is zero for every input column. Unitarity of a physical use operation and logical action remains a separate obligation. |
| SEM-7 | `derivation_sound` | Structural induction for a finite proof tree with checked leaves, identity, sequence, and qualified adjoint at one common encoding. Leaf soundness is an explicit hypothesis. Tensor and control change interfaces and are covered separately by SEM-2/5. This is not an executable certificate validator. |

`zeroEncoding zero` inserts an ancilla with its specified basis value and
retains the data coordinates. SEM-6 is an exact factorization, not a small
leakage estimate, a postselection condition, or an observation operation.
SEM-2 extends the resulting operator equality to arbitrary finite reference
systems. The statements do not prove positivity or trace properties of
instruments; the earlier Kraus-completeness development has its own scope.

### Coordinates, interpretation, and remaining bridges

The tensor uses ordered pair indices `(a,b)` with entry
`A(a,a') * B(b,b')` and does not flatten them. For the existing Rust
low-left convention, flatten `(a,b)` as `a + dim(A) * b`; using the usual
high-left display order instead changes coordinates. The control definition
uses the tagged sum `P ⊕ P`, with `Sum.inl` inactive and `Sum.inr` active.
Its connection to a physical control-bit axis requires an explicit reindexing.
No theorem here establishes the Rust indexing transformation.

The matrix meanings are mathematical denotations. A symbolic implementation
can retain operation expressions and instantiate these rule theorems instead
of multiplying dense matrices at every composition. This module does not yet
prove that a particular expression interpreter, proof DAG validator, or
serialization implements the mathematical rules. `SameEncodingDerivation`
is a small proof-tree model with independently justified leaf equations;
it does not validate untrusted nodes or prove DAG traversal complexity.

Remaining bridges include the exact meanings of primitive/provider operations,
their capability and parameter premises, the arithmetic representation,
axis/layout translations, entry-state construction, ownership-to-axis
correspondence, and binding each proof to the actual emitted IR. Reusing a
name, digest, theorem handle, or an operation's probability distribution is
not a replacement for those obligations. In particular, equality up to global
phase is insufficient for coherent control. Instrument outcomes, approximation
bounds, and block-encoding success/failure contracts remain distinct from this
pure-operation relation. These results do not close SPEC-3/4 or establish
general compiler soundness.

Validation on 2026-09-27 used the pinned Lean/mathlib 4.30.0 development:
`lake build` passed with **1,457 jobs**, and
`lake env lean -DwarningAsError=true Audit.lean` passed for **577 project
declarations**. `Qleisli.lean` imports the new module, including its generated
declarations in the transitive axiom audit. Only `propext`, `Classical.choice`,
and `Quot.sound` occur; no `sorry` or additional axiom is used. Whitespace
validation passed. The earlier 527-declaration scope-validation record above
remains historical.
