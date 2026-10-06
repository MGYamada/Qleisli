# Additional CHANGELOG wording clarification

LOCAL CANDIDATE ONLY. Apply this small diff after the original proposed.patch,
only when root approves applying the documentation after final code review
and actual validation. The original frozen proposal remains unchanged.

Replace `reject all self-imports and static binder shadows` with
`reject all self-imports and runtime bindings that shadow active static names`.
Static formals remain permitted to shadow global declarations; this wording
restricts only runtime bindings that hide active Nat, Basis, Op or fold-index
binders, as the recorded ordinary contract and proposed Reference already state.

Actual normative documents and CHANGELOG remain unedited. No build/check/test,
CLI/native/Lean execution, proof, adoption, guarantee or validation success is
reported by this clarification.
