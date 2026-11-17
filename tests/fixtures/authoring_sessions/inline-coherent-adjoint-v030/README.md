# Adjoint in nested coherent arms

This informed probe for #215 combines a named arm with an inline arm in a
`qif` nested inside an inline `qmatch` arm. It uses the adjoint of the built-in
Hadamard in the named helper. The first check at `3375c50cbd4f0783f7178b3b8427648cc266fc82`
reached the native v5 gate and returned the retained diagnostic. The emitted
helper's source context omitted the primitive adjoint.

The regression in `tests/selected_runtime_execution.rs` checks the unchanged
first source with the native kernel and rejects a wrong source position in the
arm's Raw context.
