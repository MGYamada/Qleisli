# Native-contract proof bridge

This fixture records ordinary proof work under the adopted QS interpretation.
It is not a new semantic primitive, guarantee admission, or discharge of any of
the three broad QS/PR/RS obligations.

`Protocol.NativeContract.check_acceptance` derives a witness from the actual
success of `Protocol.NativeContract.check bytes` for arbitrary initial and
remaining work. The witness retains the original QLV1 body and request bytes,
UTF-8/JSON decoding, request format/version/kind, decoded signature, ordered
ports, exact matrix or encoded contract, and continuous work states for the
actual decoder and checker calls. It gives necessary success facts rather than
a converse characterization of every decoding constraint.

`Qleisli.NativeContract.check_sound` gives the existing `RootMeaning` for both
request kinds. For decoded `leaf` requests it additionally gives original-body
instrument meaning for the closed, unitary, bounded fragment, exact requested
matrix equality, preserved signature/ports, and both whole-space inverse laws.
`leaf_reference_laws` extends those inverse laws to any finite reference without
a separability or normalization premise. The verified output-port witness is
bound to the actual original program's verification.

For `encoded`, this bridge retains `checkContract` success and common root
meaning. It does **not** identify the matrix reconstructed for the original
root with the result of the one-step finite contract wrapper. Accordingly it
does not yet conclude the encoded equation for the original root operator.
It also does not establish source/compiler preservation, compiled binary
correspondence, Rust rematerialization correctness, general CPTP/EffectSound,
clean release, target emission/execution, synthesis completeness, or quantitative
resource bounds. New theorem declarations are not automatically admitted claims.

`original-native-contract.lean` preserves the executable module before this
proof addition. `validation.json` records a byte-for-byte comparison of that
module's prefix through the end of `check`, source identities, and the command
that generated `review-types.stdout.txt` and `review-types.stderr.txt` from
`Review.lean`. All six printed theorem axiom sets must be contained in the
existing Lean foundation set (`propext`, `Classical.choice`, `Quot.sound`).
Hashes identify source and output bytes; they do not decide mathematical
adequacy or attest a deployed binary. The repository's separate current
guarantee registry report records full build, audit and fresh replay validation.
