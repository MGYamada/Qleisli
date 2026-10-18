# Current conditional-checker regression

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

[Current.lean](Current.lean) is the live CI successor to the immutable
[v0.2.5 factoring fixture](../releases/v0.2.5/kernel-refactoring-equivalence.lean).
The old file remains SHA-256
`ab0924a83a31a4836bcd572c0240bc40e014f71f052e904d07868958f303f4f6`,
as pinned by the unchanged [historical validation](../releases/v0.2.5/kernel-refactoring-validation.json).
Its original source reference is `7bfcd36916199b05d5ab11851d38d53375ccf71e`.
The post-refactor literal definitions come from
[Conditional.lean at 8ee77a2defadf13f304a69f7b822c92864f6da32](https://github.com/MGYamada/Qleisli/blob/8ee77a2defadf13f304a69f7b822c92864f6da32/lean-kernel/QleisliKernel/Hierarchical/Conditional.lean),
SHA-256 `2c6ae1ebfde3d329c2893d77c78bde062bb1fcbda26154a039d8091bd36b4bdb`, also pinned by that validation.
Historical sources, results, copyrights and expected hashes are unchanged.

The successor checks three distinct claims:

- All seven old literal conditional helper bodies equal the frozen post-refactor
  literal factoring, universally over their inputs, including malformed states,
  failure, visits and ordered requests. Both snapshots use the same imported
  subordinate definitions. This does not replay an old release environment or
  assert old/current complete-native acceptance or binary equality.
- Seven separately copied current helper bodies equal the actual production
  definitions, including the current paid accounting and PreparedContext.
  The indexed ordinary predicate is connected to its original predicate only
  through the actual complete typing pass on the same artifact. The finite
  branch still calls the same Finite.inspect with the same complete result.
- Complete current success retains original Rule.Matches, bounds, state
  invariant, finite-request binding and root derivation under every genuinely
  discharged finite predicate. No opaque leaf is assumed valid or erased.

Old and current typed helpers have different proof-context types and ordinary
fees. The old whole checkAll is not claimed equal to current whole checkAll.
Maximum visits remain 2,000,000; other existing ceilings, complete ordered field
accounting and generated declaration names remain checked. This fixture grants
no production handle, primitive, guarantee or release credit. Broader
source/runtime/target, QS, PR, quantitative RS and EXACT duties remain.

From the already built Lean 4.30.0 lean-kernel directory, the live command is:

```sh
lake env lean -DwarningAsError=true ../tests/fixtures/hierarchical_prepared_v030/Current.lean
```

The first 47716d0a hosted failure was the old fixture's Context/PreparedContext
mismatch and false current definitional-equality expectation. This fixed command
must pass before accepting changes to its live fixture; a source hash or this
description is not compilation or proof evidence.

[First local compile](first-local-compile/event.json) retains the complete first
source and actual failure streams as inert history. Its explicit Lean 4.30.0
selection is a command label, not a separately observed version. Unqualified
`State` resolved to the ancestor kernel state in the copied nested bodies; the
current fixture qualifies `Conditional.State`. This record contains no later
pass and never imports or executes its archived `.lean.txt` source.
