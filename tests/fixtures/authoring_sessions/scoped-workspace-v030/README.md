# First clean and dirty scopes

These are informed first programs for [#70](https://github.com/MGYamada/Qleisli/issues/70)
using the proposed scope grammar. All four original projects are retained
with their manifests. The existing local CLI rejects the scope's opening
brace in all four `check` and `doc` commands. The
[first transcript](first-observations.json) preserves both commands and
their output, with the local executable hashes. The commit in
[the session](session.json) identifies the Reference and source reviewed for
the experiment. The installed CLI and native checker have separate binary
identities. The parser refusal occurred before a native decision.

| First project | Expected result if the proposed scope is implemented |
| --- | --- |
| [clean-restores](attempt-01/clean-restores/main.qli) ([manifest](attempt-01/clean-restores/Qargo.toml)) | Two controlled flips restore the scratch to zero and act exactly as identity on the data. |
| [clean-leaks](attempt-01/clean-leaks/main.qli) ([manifest](attempt-01/clean-leaks/Qargo.toml)) | One controlled flip sends a data superposition and zero scratch to an entangled pair. The clean-return obligation fails. |
| [dirty-restores](attempt-01/dirty-restores/main.qli) ([manifest](attempt-01/dirty-restores/Qargo.toml)) | With ordered input bits `(data, scratch)`, the body acts as `(data xor 1, scratch)` on every basis pair with coefficient +1. Its linear extension preserves arbitrary scratch-reference correlations. |
| [dirty-alters-reference](attempt-01/dirty-alters-reference/main.qli) ([manifest](attempt-01/dirty-alters-reference/Qargo.toml)) | The scratch receives a phase of −1 on input 1. A maximally mixed scratch marginal can stay fixed while its Bell-reference correlation changes. The dirty identity obligation fails. |

The [retained dirty-restoration study](../dirty-restoration-v030/session.json)
exercises the existing exact function contract for that identity and its
phase counterexample. These proposed programs record the separate surface
syntax gap. Historical commands are inert.

The first register follow-up on `623d1edc537e5003261ec6c8826d72921061f3fb`
uses a two-bit `Bits<2>` data owner, one scratch bit, and the identity
workspace body. The [clean source](bits-register-before/clean.qli) and
[dirty source](bits-register-before/dirty.qli) are saved with their
[manifest](bits-register-before/Qargo.toml). Each was originally run as
`qleisli interop emit-qasm <project> --input=qli --resources` with its source
as `main.qli`. The actual [clean response](bits-register-before/clean.json) and
[dirty response](bits-register-before/dirty.json) both record the generic
native contract refusal. The native executable SHA-256 was
`2d1a3af3bef143dbd4dc40c0d122e1f5ac886f1d94ad1f5f37be6869aa986ddc`.
The same check accepted both scopes with a `Bit` or `(Bit, Bit)` data owner.
