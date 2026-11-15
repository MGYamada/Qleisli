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
