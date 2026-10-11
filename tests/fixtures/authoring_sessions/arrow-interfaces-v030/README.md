# First arrow-interface boundary study

The [context](context.md) and [session](session.json) retain six complete first
sources before changes to operation typing. There are no source repairs.
All six observations used the same CLI bytes before and after each command
and an explicitly selected native checker. They are informed development
observations, not a blind model benchmark.

| First source | Actual check | What it establishes |
| --- | --- | --- |
| `direct-unitor.qli` | Success, hierarchy | Direct `(Unit,Bit) -> Bit` can retain distinct exact input/output trees. |
| `direct-preparation.qli` | Success, hierarchy | Direct `Unit -> Bit` preparation has a supported selected transport. |
| `endomorphic-control.qli` | Success, hierarchy | The existing endomorphic static provider route remains available. |
| `endomorphic-unitor-refusal.qli` | Type refusal at `strip` | Equal physical dimension does not permit this provider to inhabit `Op<(Unit,Bit)>`. |
| `desired-unitor-arrow.qli` | Parse refusal at second `Bit` | The candidate comma slot collides with the current Meaning grammar. |
| `desired-preparation-arrow.qli` | Same parse refusal | No downstream preparation/capability result follows from this attempt. |

The three successes report producer consistency, producer-origin requests and
`source_meaning_verified: false`. They are not independent expected-Meaning
checks. The two proposed arrow spellings are not adopted syntax. The negative
endomorphism example remains invalid even after general arrows are implemented:
`Op<A>` must still have exactly the same input/output tree.

The bounded regression in `tests/operation_parameters.rs` separately checks
direct/control principal effects and the exact-tree provider refusal at both
public source entry points. It does not freeze parser rejection of the desired
future arrows. Existing independent unitor and preparation tests are in
`tests/quantum_tuple_unitors.rs` and
`src/frontend/specialize/lower/preservation/isometry_tests.rs`; those tests do
not prove general source preservation or this unimplemented static-arrow route.

Remaining work is tracked in #83 and #46: separate exact domain/codomain in the
shared operation representation; specify pure effect/law requirements and
capability transformations; resolve Meaning grammar and identity; and connect
the actual emitted artifact to independent native requests. A preparation's
mathematical adjoint annihilates `|1>` and cannot be exposed as an unrestricted
total inverse. No Issue closure, new guarantee or proof discharge is claimed.
