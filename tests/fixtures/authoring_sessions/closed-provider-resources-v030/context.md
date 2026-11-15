# Closed providers in terminal resource checking

The first study uses a [schema-2 manifest](Qargo.toml) with each standalone
source. The inputs use one data qubit and, where applicable, one clean
scratch. The identity provider and `h(h(q))` implement the same exact action.
They have different emitted costs when the target retains both H gates.

The first sources call a statically selected operation inside `clean` with
[identity](attempt-01/identity/main.qli), [double H](attempt-01/double_h/main.qli)
or an [unresolved actual](attempt-01/unresolved/main.qli). The closed sources
are rejected by the native source check. The unresolved name fails earlier.
All three commands return an error and emit no resource report.

The next [ordinary call](attempt-02/plain-generic/main.qli) passes the source
check. It has no workspace and the bounded resource exporter refuses it.
In a clean scope, the [direct identity](attempt-02/direct-light/main.qli) and
[direct double H](attempt-02/direct-heavy/main.qli) providers pass and report
respectively zero and two emitted gates, with two reserved qubits in both cases.
When a generic specialization precedes the clean scope, [identity](attempt-02/before-light/main.qli)
and [double H](attempt-02/before-heavy/main.qli) both pass the source check.
The placement verifier rejects both before returning any target counts.

The [recorded observations](session.json) use the `af310678` Rust and native
checker candidate on PR #585. To replay one case, copy its source and the
recorded manifest into a separate project directory as `main.qli` and
`Qargo.toml`. The saved commands are evidence only. The bounded counts cover
only the checked terminal profile. The two generic-call refusals still need
diagnosis and support before closing #162.
