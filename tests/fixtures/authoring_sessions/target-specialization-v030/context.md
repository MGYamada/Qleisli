# Closed specialization and terminal target diagnostics

The two small projects share one const-specialized definition. The zero case
emits H; the other applies an exact global phase. The probe used the native
checker built from the #583 integration and the local #585 candidate before
the diagnostic change. The [first manifest](attempt-01/n1/Qargo.toml.rejected)
used an invalid key. Its original bytes are restored as `Qargo.toml` in the
temporary project for the rejection replay. The adjacent schema-2 manifest
declares the edition of the stored source. The second attempt uses canonical manifests for
[the H specialization](attempt-02/n0/Qargo.toml) and
[the scalar-phase specialization](attempt-02/n1/Qargo.toml). It retains the
two successful source checks, successful H export and unsupported scalar-phase
export. The latter reported the Raw operation index with an empty primary
location.
