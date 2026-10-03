# Lean ownership, scope, and Kraus algebra proofs

The [VM-23 exact bridge](Qleisli/Exact.lean) proves actual normalization,
canonical coefficient/scalar equality and full scalar arithmetic. The
[matrix bridge](Qleisli/ExactMatrix.lean) proves general composition, tensor and
adjoint meanings, low-coordinate tensor order, actual isometry soundness and
arbitrary-reference inner-product/joint-norm preservation. Its
[complex reference](Qleisli/Semantics/Exact.lean) imports data only.
The [VM-24 finite bridge](Qleisli/Finite.lean) proves actual column traces,
phase-sensitive encoded/reference equations, clean output-encoding return and
both whole-space inverse laws. Its [data-only literal reference](Qleisli/Semantics/Finite.lean)
and [native scope record](../tests/fixtures/verification_v024/README.md) keep raw
extraction, hierarchy closure and production transport as later obligations.
Rust arithmetic is a compatibility comparison path; its general formal
correctness is not required for the proved Lean replacement. Production
evidence/transport integration remains in later packets; see the
[packet's precise coverage](../tests/fixtures/verification_v023/README.md).

The [VM-25 pure bridge](Qleisli/RawPure.lean) covers all eleven straight-line pure
constructors, independent complex raw action, fresh retained graph/binding and
both clean-release forms. [Non-dense protected cleanup](Qleisli/RawProtected.lean)
holds on arbitrary correlated complex amplitudes; [bounded denotation](Qleisli/RawDenotation.lean)
retains literal physical circuits, phase, interfaces and output order. See the
[completion scope](../tests/fixtures/verification_v025/completion/README.md).

The executable **Mathlib-free** kernel is in [lean-kernel](../lean-kernel/README.md).
This directory remains the separate Mathlib proof/model package. The
staged migration now includes an
[interference bridge](Qleisli/Interference.lean) importing the actual executable
definitions through a local Lake dependency. It instantiates H/diagonal
amplitude laws over complex numbers and interprets accepted phase/layout graphs
as weighted basis transitions. The [QFT proof](Qleisli/Qft.lean) derives the actual
matched gate circuit's Fourier coefficients, including output reversal and
arbitrary reference amplitudes. The [typed graph theorem](Qleisli/QftGraph.lean)
transfers this result to the actual accepted graph's operational coefficients.
[QFT unitarity](Qleisli/QftUnitary.lean) proves both inverse laws for those entries.
The [QPE theorem](Qleisli/Qpe.lean) derives full residual target/reference maps
from actual checked components. [Completeness](Qleisli/QpeComplete.lean) proves
all-outcome completeness and joint trace preservation, conditional on a
whole-space isometric provider. External hierarchical/provider/registry binding
remains open. Runtime definitions must never import this proof package.

This directory contains the **ownership-accounting projection** of the finite
core resource rules, a **lexical scope-exit lookup model**, and a small
exact-matrix development for **Kraus completeness under composition**.
The later semantic-contract module proves local symbolic composition rules,
with separate isometry and unitary premises; it does not enumerate large
operators or verify the experimental Rust kernel.
It does not formalize the complete source
language, the Rust compiler, general positivity, or the full quantum soundness
theorem. The current rule inventory links exact
declarations, checking evidence and remaining proof obligations.

Lean and Mathlib are pinned to `v4.30.0`; the committed manifest pins their
transitive dependencies. Physlib is a [future dependency candidate](#future-physlib-bridge),
not required by this environment or CI. Reintroduce it with an actual instrument
bridge, compatible version selection and a separate external audit. With `elan` installed, run:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

Run `lake update` only when intentionally changing dependency resolution.
The initial cache download needs network access; subsequent builds can use
the installed toolchain and cached dependencies. Julia is not a dependency.

## Future Physlib bridge

Physlib is absent from the required environment and default CI. Its first
candidate use is a finite-IR instrument/CPTP bridge for measurement, discard and
reset. Add it only with a concrete bridge and named theorem obligation covering
coordinate order, complete outcomes, arbitrary references, phase and cleanup.
A POVM's Lüders instrument alone does not cover every Qleisli instrument.

Recheck compatible Lean/Mathlib/Physlib versions, pin the selected commit, audit
actual external declarations alongside `Audit.lean`, test the bridge and retain
its third-party notices. A required toolchain increase needs MINOR review.
Library availability, an import probe and a channel theorem do not establish
source/IR, Rust or native correspondence.

The [optional probe](../research/quantum-libraries/PhyslibAudit.lean) preserves an
experiment at `f5242c99d796b59a390d26cd7d1a8057e04c46b5`; that baseline does not
select a future dependency. After restoring it in a separate compatible
experiment and building the chosen QuantumInfo modules, run from `lean/`:

```sh
lake env lean -DwarningAsError=true ../research/quantum-libraries/PhyslibAudit.lean
```

Physlib retains its own authorship and
[Apache-2.0 license](https://github.com/leanprover-community/physlib/blob/f5242c99d796b59a390d26cd7d1a8057e04c46b5/LICENSE);
no implementation is vendored or relabeled as Qleisli work. Preserve all notices
of any selected transitive dependencies. This optional probe has no current
build target and is separate from the retained 4.34.1 survey.

## Proof modules

| File | Role |
| --- | --- |
| [Resource.lean](Qleisli/Resource.lean) | Basis trees, mixed values, typed ownership occurrences, registers, validity, structural lemmas |
| [Scope.lean](Qleisli/Scope.lean) | Absent/spent/live lookups, rejection of escaping quantum owners, restoration of entry bindings, and preservation of the current ownership footprint on successful scope exit |
| [Transition.lean](Qleisli/Transition.lean) | Explicit resource events, disjoint frame extension, linear execution |
| [Phi.lean](Qleisli/Phi.lean) | Complete injective renaming, resource phi agreement, branching execution |
| [Examples.lean](Qleisli/Examples.lean) | Exact accepted boundaries and rejection theorems, including zero-width ownership |
| [Kraus.lean](Qleisli/Kraus.lean) | Five matrix lemmas for singleton/isometry completeness, output transport, and adaptive composition |
| [SemanticContract.lean](Qleisli/SemanticContract.lean) | Exact encoded relations, composition/reference/qualified-transform and zero-return lemmas; separate from implementation adequacy |
| [QftUnitary.lean](Qleisli/QftUnitary.lean) | Both inverse laws for the actual accepted QFT graph matrix |
| [Qpe.lean](Qleisli/Qpe.lean) | Actual accepted plan, controlled powers, Fourier branches and arbitrary reference maps |
| [QpeComplete.lean](Qleisli/QpeComplete.lean) | Fourier orthogonality, conditional Kraus completeness and joint trace preservation |
| [ControlledPowers.lean](Qleisli/ControlledPowers.lean) | Actual coherent iteration as a complex block operator, conditional unitary laws and arbitrary reference maps |
| [HierarchicalSemantics.lean](Qleisli/HierarchicalSemantics.lean) | Actual rule preservation and accepted derivation/entry equations, conditional on interpretation of actual table bodies |
| [HierarchicalOperators.lean](Qleisli/HierarchicalOperators.lean) | Complex operator, matrix and reference-map instantiation; literal repetition as matrix power; provider equations obtained from actual derivations |
| [HierarchicalEvaluation.lean](Qleisli/HierarchicalEvaluation.lean) | Constructed successful, unique actual-body denotations; accepted entry operator/matrix/reference equations without an assumed interpretation environment |
| [Schema.lean](Qleisli/Schema.lean) | Actual component dispatch implies the QFT, single-power and QPE conclusions; external binding remains open |
| [Audit.lean](Audit.lean) | Transitive axiom audit of all declarations in imported project modules |
| [Preserved external probe](../research/quantum-libraries/PhyslibAudit.lean) | Optional historical Qleisli/QuantumInfo integration audit; requires explicitly reintroducing Physlib in a separate experiment, excluded from the current build/CI |

`Config` in the resource model erases lexical names and spent markers.
The separate `Scope` model retains those distinctions through function-based
lookups and takes entry/current environments plus a rebound-name set as
inputs. Its scope-exit theorem covers mixed values and `Q<Unit>` without a
bound on value size or the number of names. It does not prove how source
execution constructs the snapshots or rebound set. Its universal approval
predicate is noncomputable; equality with Rust's finite-map scan is a paper
correspondence supported by finite implementation checks, not a mechanized
compiler-correctness theorem. See the
[scope definitions and theorems](Qleisli/Scope.lean)
and Rust lowering-state refinement.

The build treats warnings as errors. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound`; it rejects `sorryAx`, native-evaluation
axioms, and project-specific axioms. It checks dependencies of all project
declarations, including generated declarations and private helpers. Finite
examples use kernel reduction (`decide`), not `native_decide`.

From the repository root, `python3 scripts/check_docs.py` also checks local
Markdown targets and that every `Qleisli/*.lean` module is reachable from
`Qleisli.lean`, so new proof modules cannot silently miss the audit.
The coverage scanner reads the import header and skips ordinary comments,
including nested block comments. Commented imports and import-like text in
declarations or strings do not count as dependencies.

## Component registry review

[schema-registry.json](schema-registry.json) binds the internal QFT, controlled
power and QPE IDs to exported theorem types, including universes and every
explicit/implicit binder. [SchemaExport.lean](SchemaExport.lean) exports the
rebuilt structural expressions and actual dispatcher signature. The manifest
also fixes parameter domains, template versions and a content revision over
runtime/proof sources, locks, toolchains and audit tools.

`python3 scripts/check_schema_registry.py` rebuilds both packages, audits compiled
declarations, replays the runtime kernel and compares actual exported types.
`--write` refreshes the registry only after those checks; `--source-only` is a
weaker archive identity check and cannot refresh or validate theorem types.
The [mutation suite](../scripts/test_check_schema_registry.py) rejects changed
types, checker identities, IDs, domains, versions, source hashes and enablement.
All entries remain `external_enabled: false`. An internal receipt or matching
provider index does not establish the intended provider operator. Complete
external IR/port/provider binding, exact finite reconstruction and decoder/native
correspondence remain required before external enablement.

The [actual dispatcher](../lean-kernel/QleisliKernel/Schema.lean) and
[semantic bridge](Qleisli/Schema.lean) define the checked component domains:
QFT width 1–8, single controlled power exponent 0–12, and QPE n,m in 1–8 with
n+m≤16. Coherent-power and QPE completeness/unitarity statements explicitly
require a whole-space isometric provider. The original weaker power theorem
remains available; the registry binds the coherent operator/reference theorem.
These domains do not establish accepted capacity for a composed production case.

CI runs the build and audit separately from Rust tests. A passing Lean job
establishes the statements in this model; a passing Rust job does not prove
that every compiler execution implements the model.
