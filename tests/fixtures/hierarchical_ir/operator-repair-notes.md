# Actual operator-interpretation repairs

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This is an informed proof-development record, not a controlled model study.
The first source and complete first failing build are retained separately.
The following are summaries of subsequent real Lean diagnostics and repairs;
they are not represented as verbatim terminal transcripts.

- The first build could not destruct a Boolean equality of structured sides,
  could not turn an empty `mapM` result directly into a membership implication,
  and could not rewrite the array-to-list Option map. Explicit derived
  `ReflBEq`/`LawfulBEq` proofs for type atoms and port/interface structures,
  the actual `Array.toList_mapM` equation and empty-list substitution repaired
  these cases. The first attempt to derive only `LawfulBEq` exposed the missing
  reflexivity instances; those were proved, not assumed.
- `Interface.ext` and `Array.toList_toArray` were not available with the
  initially used names. Explicit interface cases and concrete list-map goals
  replaced those references. Option case splits had already rewritten some
  lookup goals, so their equality proofs use `rfl` in those branches.
- The direct-power proof exposed unused simp arguments after a failed lookup
  short-circuited its Option computation. Removing the redundant arguments
  preserved the warning-as-error gate.
- The first complex interpretation used the square-only `Qpe.outcomeMap` with
  a rectangular matrix. The final `referenceMap` explicitly tensors a
  rectangular matrix with the reference identity and forms the full joint
  output. It does not silently identify input and output dimensions.
- An over-eager simp set unfolded `power` before its width and induction
  lemmas could apply. Explicit width rewrites followed by the single successor
  reduction prove correspondence with independent matrix exponentiation.
- A multiline `using` expression inside an existential tuple needed explicit
  parentheses. The final theorem also binds the equation to the actual
  artifact entry checked by preparation.

Both implementation and meaning interpretations read actual body fields.
The interpretation environment does not read the proof table. The actual
derivation induction supplies premise equations; the concrete complex algebra
proves its only special primitive law, identity rewiring. Construction of that
environment for the full profile and whole-space unitary soundness remain
separate work. None of these proofs enables an external schema or transfers
production authority from Rust.
