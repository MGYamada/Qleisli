# Adjoint in nested coherent arms

This informed probe for #215 combines a named arm with an inline arm in a
`qif` nested inside an inline `qmatch` arm. It uses the adjoint of the built-in
Hadamard in the named helper. The first check at `3375c50cbd4f0783f7178b3b8427648cc266fc82`
reached the native v5 gate and returned the retained diagnostic. The emitted
helper's source context omitted the primitive adjoint.
The first probe has a [project manifest](attempt-01/Qargo.toml "attempt-01/Qargo.toml")
and a [recorded refusal](attempt-01.before.json "attempt-01.before.json").

The regression in `tests/selected_runtime_execution.rs` checks the unchanged
first source with the native kernel and rejects a wrong source position in the
arm's Raw context.

The second probe uses `if static n == 0` in an inline `qif` arm. The native
v5 check on the first specialization at
`3aa970e58353962879eb5c2c35e4e0fd95a627c6` rejected the original source.
The regression checks both specializations and rejects the first
specialization's artifact with the second one's request. The selector remains
live in the source history outside the isolated arm Raw frame.
The second probe has a [project manifest](attempt-02/Qargo.toml "attempt-02/Qargo.toml")
and a [recorded refusal](attempt-02.before.json "attempt-02.before.json").

The first whole-owner `excl` statement probe is retained unchanged as the
binary source in `coherent_block_arm_replays_excl_and_returns_the_original_binding`.
The compiler at draft head `7fb68b833d8d3ee9f3f7aca12166326e0338dcf3` reported
the following at bytes `119..120`.

```text
type or tuple/size shape mismatch: expected `Q<Bit>`, found `Unit`
```

An explicit target return got through source typing and
then received the native source comparison error. The regressions also cover
the original target's lifetime, named arm calls and ordered multi-owner access.
