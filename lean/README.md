# Lean ownership and Kraus algebra proofs

This directory contains the **ownership-accounting projection** of the finite
core resource rules and a small exact-matrix development for **Kraus
completeness under composition**. It does not formalize the complete source
language, the Rust compiler, positivity/trace, or the full quantum soundness
theorem. The English
[theorem ledger and scope](../docs/lean-resource-proof.md) is the status record.

Lean and Mathlib are pinned to `v4.30.0`. The committed
`lake-manifest.json` pins transitive dependencies. With `elan` installed, run:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

Run `lake update` only when intentionally changing dependency resolution.
The initial cache download needs network access; subsequent builds can use
the installed toolchain and cached dependencies. Julia is not a dependency.

| File | Role |
| --- | --- |
| [Resource.lean](Qleisli/Resource.lean) | Basis trees, mixed values, typed ownership occurrences, registers, validity, structural lemmas |
| [Transition.lean](Qleisli/Transition.lean) | Explicit resource events, disjoint frame extension, linear execution |
| [Phi.lean](Qleisli/Phi.lean) | Complete injective renaming, resource phi agreement, branching execution |
| [Examples.lean](Qleisli/Examples.lean) | Exact accepted boundaries and rejection theorems, including zero-width ownership |
| [Kraus.lean](Qleisli/Kraus.lean) | Five matrix lemmas for singleton/isometry completeness, output transport, and adaptive composition |
| [Audit.lean](Audit.lean) | Transitive axiom audit of all declarations in imported project modules |

The build treats warnings as errors. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound`; it rejects `sorryAx`, native-evaluation
axioms, and project-specific axioms. It checks dependencies of all project
declarations, including generated declarations and private helpers. Finite
examples use kernel reduction (`decide`), not `native_decide`.

From the repository root, `python3 scripts/check_docs.py` also checks local
Markdown targets and that every `Qleisli/*.lean` module is reachable from
`Qleisli.lean`, so new proof modules cannot silently miss the audit.

CI runs the build and audit separately from Rust tests. A passing Lean job
establishes the statements in this model; a passing Rust job does not prove
that every compiler execution implements the model.
