# Basis lift in an inline coherent arm

This informed probe for #215 uses a coherent Boolean negation in the zero arm
of `qif`. The first native check at
`628127e0caeabf7ca6c5b81d9575976c22dd4b93` rejected the source because its lift
was absent from the enclosing declaration's active basis events.
The probe has a [project manifest](attempt-01/Qargo.toml "attempt-01/Qargo.toml")
and a [recorded refusal](attempt-01.before.json "attempt-01.before.json").

The regression in `tests/selected_runtime_execution.rs` checks the unchanged
source. It then replaces the arm's literal lift table and changes the
corresponding controlled and parent permutations to the same identity.
The table derived from the written `not b` still rejects that proposal.

The first static-branch probe is retained in
`coherent_block_arm_checks_the_original_static_continuation`. At draft head
`7fb68b833d8d3ee9f3f7aca12166326e0338dcf3`, `n=0` selected the basis lift and
returned `invalid_ir` with the native source comparison error at bytes
`24..167`. The same source passed at `n=1`, which selects the identity arm.
The regression checks both bodies and rejects a mismatched specialization.

The first computed-predicate probe is retained unchanged in
`coherent_block_arm_checks_the_original_computed_predicate` in the same Rust
test file. At the original compiler baseline it refused byte range
`138..185` with category `unsupported` and message
`operation is outside the finite static unitary subset`. The regression
checks that inverting the predicate in both literal scratch passes and
updating both controlled presentations still fails the native source check.
