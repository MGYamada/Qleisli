# Active 109-Issue scope correction

The maintainer's latest correction is **「109 issuesです」**: the original 108
selected Issues plus #311 form the active 0.3.0 release scope. The root reports
four completed Issues (#138, #139, #140 and #149), so the progress denominator is
109 and the reported completion is **4/109 = 3.67%**. Live GitHub completion and
scope are recorded as a root report; this packet did not independently fetch them.

[scope.json](scope.json) records that provenance and the exact active groups.
The release checker now includes #311 in G02. Its synthetic adversarial suite
passed 29 tests, including rejection of old 108-only groups, absent #311 reviewed
criteria, and absent #311 acceptance. The other 108 IDs and their existing
criterion scopes are retained. [The actual test record](code-results/result.json) binds separate
stdout/stderr and unchanged checker/test hashes; its simulated hosted receipts
are not real release authorization.

The local documentation checks use the repository's source checker, the existing
pinned mdBook 0.5.4 binary and the rendered-book checker. Their exact commands,
streams, durations and input hashes are retained under `documentation-results/`.
`files.json` inventories this packet, excluding itself.

Earlier 108-Issue records, including their actual validation inputs and hashes,
remain unchanged historical evidence. This correction creates no new Guardian
act, constitutional interpretation, guarantee admission or discharge, release
approval, publication, Rust build or Lean build.
