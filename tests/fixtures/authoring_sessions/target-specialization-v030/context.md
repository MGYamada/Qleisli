# Closed specialization and terminal target diagnostics

The two small projects share one const-specialized definition. The zero case
emits H; the other applies an exact global phase. The probe used the native
checker built from the #583 integration and the local #585 candidate before
the diagnostic change. The first attempt used an invalid manifest key. The
second changes the manifest and retains the actual successful source checks,
successful H export and unsupported scalar-phase export. The latter reported
the Raw operation index with an empty primary location.
