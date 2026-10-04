# Actual routed hierarchy-body exchange (#303)

This is a bounded proof and checking experiment under [the recorded contract](contract.md).
It adds ordinary mathematical evidence; it does not admit a guarantee or grant
source reordering permission. The original consume/return programs and emitted
artifacts were saved before the new proof module was written.

## Original programs and actual routes

`sources/ab` and `sources/ba` apply controlled H and controlled T in opposite
orders. Their ordered owners are `(a, r, c, b)`: target A is physical axis 0,
the untouched owner is axis 1, the shared control is axis 2, and target B is
axis 3. The generated root is the actual five-child sequence
`[enter, tensorA, middle, tensorB, leave]`, with the stage order reversed in BA.
The stages retain their original providers, control nodes, owner-changing
identity renames, tensor bodies and complete interfaces.

| Artifact | Enter map | Middle map | Leave map |
| --- | --- | --- | --- |
| AB | `[2,0,1,3]` | `[0,3,1,2]` | `[2,3,0,1]` |
| BA | `[2,3,0,1]` | `[0,2,1,3]` | `[1,3,0,2]` |

These are distinct actual routes. Both composites are the identity. Fresh
`Wiring.inspect` summaries are checked against these maps and their computed
two-sided inverses; a successful wiring inspection alone is insufficient.

The historical filenames `unit-ab` and `unit-ba` contain **`Q<Bits<0>>` owners**,
not `Q<Unit>`. Two of their four logical owners have zero physical axes. The
other owners supply the control and the T target, so their matrices are 4 by 4.
The zero-axis provider in these programs is identity. These examples neither
identify the two source types nor exercise every possible zero-axis scalar;
the general theorem retains exact scalar coefficients for widths including zero.

## What is proved

`Qleisli.RoutedControlCommutation` connects the existing executable
`HierarchicalFiniteEvaluation.physical` and `HierarchicalOperators.apply`
definitions to the same ordered coordinate frame `(control, A, B, rest)`.
Its 17 public theorems culminate in `actual_exchange` and
`actual_exchange_reference`: the two original entry evaluations have equal
complex matrix entries, and equal action on amplitudes with an arbitrary
external reference. No normalization or separability assumption is used.

`Stage.Bound`, `Spine.Bound` and `Premises` retain the original records and
dependency indices. The hypotheses include the same artifact's successful
`NodeTyping.checkAll`, full interfaces and owner order, fresh wiring summaries,
computed two-sided permutations, final inverse composition, and evaluations
of the original providers with their dimensions. `Frames` contains literal
bit-list coordinate equations, not an assumed desired operator equality.
The typing prerequisite does **not** itself imply these coordinate equations.

`Examples.lean` embeds both complete saved artifacts and instantiates the frame
equations for their distinct maps. Its `emitted_entry_exchange` is a
**conditional corollary**: the leaf environment, original provider evaluations,
remaining `Premises`, matching provider matrices and original entry evaluations
remain explicit. It is not a closed proof that native acceptance of these bytes
implies exchange. Separate runtime checks of typing, wiring, conditional and
finite-leaf checkers must not be mistaken for discharging those hypotheses.

No executable acceptance rule, protected semantic definition or existing proof
body was changed. The source comparison records 208 unchanged preexisting Lean
files, excluding the root module's new import. There is no new project axiom,
unsafe definition, temporary proof, optimization, codec/compiler correspondence
claim, preservation of success/failure or work count, or source access contract.

## Bounded evidence and counterexamples

All seven programs passed native whole-artifact inspection. Their original
payload, precursor, request and runtime matrix are retained. `Generate.rs`
uses the public parse/instantiate/elaborate/lower path and independently asks
the native kernel to inspect the emitted payload before obtaining the runtime
matrix. The isolated final replay built Rust from its saved source archive,
including all actual standard-library inputs, then reproduced all **28 files
byte for byte**. Its 135-file input inventory was unchanged across execution.
Binary hashes are local observations, not a proof of compiler correspondence.

`check_examples.py` compared **1,312 coefficients** to direct analytic formulas;
the maximum absolute floating-point error was `1.5700924586837752e-16`.
It also checked exact equality of the two saved positive matrices, all route
composites, retention of zero-axis owners, literal Lean/artifact parity, and
a correlated reference input whose relative factor `i` is retained with T's
phase. These are bounded numerical checks, distinct from the general theorem.

Two negative comparisons retain independently valid native artifacts:

- `overlap-ab` and `overlap-ba` put H and T on the same target. The matrix
  difference at row 14, column 15 is `0.5411961001461969`; disjoint-factor
  hypotheses do not apply.
- `wrong-output-route` returns `(r,a,c,b)` instead of `(a,r,c,b)`. Every
  individual map is bijective, but the composite is `[1,0,2,3]`, and a matrix
  entry differs by `1`. It is a wrong inverse relative to the intended common
  output frame, not an invalid standalone artifact. Three closed Lean examples
  check the bijection, this composite and its inequality to the identity.

The parent reviewer independently compared all 544 positive coefficients with
separately derived analytic formulas, verified both negative differences, and
reviewed the full conditional proof and its premises without a concrete defect.
That review is numerical and conditional-proof review, not a completed native
acceptance theorem instantiation.

## Validation and reproduction

The command records retain exact arguments, working directories, exit status,
output and elapsed time. `Review.lean` prints all 17 public types and their
axioms. `Examples.lean` also prints the emitted-artifact corollary's axiom
dependencies. Their axiom sets are limited to `propext`, `Classical.choice`
and `Quot.sound`.
Compilation uses `-DautoImplicit=false -DwarningAsError=true`.

From `lean/`:

```sh
lake build Qleisli.RoutedControlCommutation
lake env lean -DautoImplicit=false -DwarningAsError=true ../tests/fixtures/constitution_v030/routed-control-commutation/Review.lean
lake env lean -DautoImplicit=false -DwarningAsError=true ../tests/fixtures/constitution_v030/routed-control-commutation/Examples.lean
lake env leanchecker --fresh Qleisli.RoutedControlCommutation
```

From the repository root:

```sh
python3 tests/fixtures/constitution_v030/routed-control-commutation/check_examples.py
```

`root-registry-validation.json` preserves the coordinated official rebuild of
both Lean packages, both audits, native fresh replay and schema type export.
The audits covered 11,578 native declarations and 3,649 Mathlib-package
declarations, using only the same three axioms. This record binds the completed
source revision; it is not a new semantic approval. The final manifest records
the separate fresh replay of the new mathematical module.

`first-attempt` preserves the rejected `controlled(ua,c,a)` spelling;
`second-attempt` preserves the missing `std::quantum::t` import diagnostic.
`negative-authoring-attempt` preserves an unsuccessful source-text replacement
that initially left the intended negative programs unchanged. Those observations
are not claimed as counterexamples; the corrected negative sources and results
are the active files described above. No maximum-size case was generated.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
