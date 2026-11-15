# Closed specialization and terminal target diagnostics

The two small projects share one const-specialized definition. The zero case
emits H; the other applies an exact global phase. The probe used the native
checker built from the #583 integration and the local #585 candidate before
the diagnostic change. The [first manifest](attempt-01/n1/Qargo.toml.rejected)
used an invalid key. Its original bytes are restored as `Qargo.toml` in the
temporary project for the rejection replay. The enclosing
[schema-2 manifest](attempt-01/Qargo.toml) declares the edition of the
stored source. The second attempt uses canonical manifests for
[the H specialization](attempt-02/n0/Qargo.toml) and
[the scalar-phase specialization](attempt-02/n1/Qargo.toml). It retains the
two successful source checks, successful H export and unsupported scalar-phase
export. The latter reported the Raw operation index with an empty primary
location.

The third attempt exercises OpenQASM with checked resource reporting on
`46bfd893b17172b3a570f37d9d034d33bef365a2`. Each project uses the same
one-qubit generic definition in a clean workspace and varies the closed
natural argument. The first two runs report one gate and two physical qubits,
with different T counts for H and T. The exact scalar case passes source
checking and fails target export with an empty primary location. The
out-of-domain natural argument fails source checking at the call site.

The fourth and fifth attempts use the reviewed #601 tree merged at
`df968ad1c8fdd8a63f668f9b6ddcc5482cdba210`. The [first ordered-basis program](attempt-04/main.qli)
uses the [edition-2026 manifest](attempt-04/Qargo.toml) and
creates and consumes a `Q<Unit>` inside `clean`. The original source checker
rejects it during workspace body discovery. In a separate local reduction,
adding `finish(unit(()))` also caused a plain Bit workspace to fail. A tuple
data owner with its Unit factor created and consumed outside the scope passed.

The [two-live-input program](attempt-05/ordered/main.qli) keeps ordered
`(Unit, Bit)` and `Bit` owners of the same physical width. The emitted T and
adjoint-T gates and the measured bits keep that order. The [swapped type program](attempt-05/swapped/main.qli)
fails with the provider type mismatch at the original call. Two separate
bounded native replays used the accepted placement request. Replacing the
written basis order while retaining the previous Raw artifact was rejected
with `contract`. Changing only the target operands while preserving both gate
counts was rejected with `clean_workspace`. The native replies record the
packet hashes and have no operation location. The regression checks the live
programs and reruns the changed target through the actual placement checker.
