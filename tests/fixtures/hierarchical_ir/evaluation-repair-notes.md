# Constructed evaluation: observed repairs

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The first saved implementation and build contain the evaluator, successful
`mapM` helpers, depth stability and uniqueness. That build passed. The following
are summaries of actual subsequent diagnostics, not claimed terminal transcripts
or a controlled authoring experiment.

- Local-rule existence proofs left unconstrained tag metavariables, including
  `Tag.sequence = ?m.460`. Supplying the actual constructor, ordered children
  and Boolean success functions explicitly repaired elaboration.
- `Bool.and_eq_true.mp` was not a declaration. Rewriting with
  `Bool.and_eq_true` before projecting the resulting conjunction repaired the
  control/repetition cases.
- An Option lookup split had already replaced the lookup with `some premise`
  in the later goal. Using the actual resulting equality avoided composing it
  with an equality whose left side no longer matched. A now-unused simp
  argument was removed instead of weakening warning checks.
- `opaque` is a reserved Lean token. The negative finite-payload fixture was
  renamed `opaqueData`. In the impossible `Except.error` example branch,
  explicitly reducing the Boolean `isOk` condition exposed the contradiction.

No accepted-input restriction, runtime checker change, axiom, admission,
native proof shortcut, elaboration-limit increase or audit exemption was used.
The successful actual-body evaluation theorem replaces an interpretation
premise; it does not assert full-profile unitarity, native simulator adequacy
or any still-disabled external schema.
