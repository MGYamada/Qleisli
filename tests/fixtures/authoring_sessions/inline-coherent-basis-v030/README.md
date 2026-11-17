# Basis lift in an inline coherent arm

This informed probe for #215 uses a coherent Boolean negation in the zero arm
of `qif`. The first native check at
`628127e0caeabf7ca6c5b81d9575976c22dd4b93` rejected the source because its lift
was absent from the enclosing declaration's active basis events.

The regression in `tests/selected_runtime_execution.rs` checks the unchanged
source. It then replaces the arm's literal lift table and changes the
corresponding controlled and parent permutations to the same identity.
The table derived from the written `not b` still rejects that proposal.
