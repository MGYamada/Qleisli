# Hosted distribution failure, run 37218876223

This packet preserves actual hosted evidence from distribution job
`111485304488`, not a local replay. The pull-request head was
`bfceca338a1dfc07b9501758afcd00675b88733d`; CI tested the synthetic merge
`392f403434557e5644e7641a1f86170cb9f1a5dd`, tree
`39be7c8d319df112eb9b88ad758336daeae57796`.

Command 14, `cargo test --offline --all-targets`, failed with exit 101.
The `native_roundtrip` target reported three passed and one failed:
`compiled_programs_reencode_exactly_and_caches_match_implementations` panicked
at `tests/native_roundtrip.rs:141:74` after its source collector reached
`corpus/migrations/predicate-domain-v030/sources/pennylane_demos/phase_lock/main.qli`.
That historical source contains the retired `CBit` type; the actual diagnostic
was `parse error: CBit/CBits types were removed; use Bit/Bits<n>` at line 14,
column 26. The exact failure starts at line 533 of `14.stdout` and is also
retained in `failure-excerpt.txt`. This identifies the same historical-source
collector failure observed in the Rust lanes; it does not establish another
distribution-tool defect.

The report records commands 0 through 13 as successful, including package
verification, packaged-source documentation checks, installation and the
installed quickstart. Overall distribution validation **failed**. No success
is claimed for subsequent checks, a release, publication or theorem admission.
The report records internally owned work as `removed` despite the failure,
with `keep_requested: false`; the Cargo target directory was caller-owned.
The durable report, command logs and archive identities remained available in
the uploaded artifact. Internal crate/source-archive bytes were not separately
extracted or revalidated for this investigation.

## Retained bytes and provenance

- `provenance.json` records the run, job, tested source identity, artifact API
  metadata, exact download command, size limit, digest and selected ZIP entries.
- `report.json.gz` is a deterministic, lossless gzip of the complete original
  `qleisli-distribution.json` entry. Its uncompressed size and digest are in
  `provenance.json`.
- `14.stdout` and `14.stderr` are the exact corresponding ZIP entry bytes.
- `report-summary.json` selects report fields and numbers its command records;
  the compressed original remains the authoritative captured report.
- `manifest.json` binds all other files in this packet by byte count and SHA-256.

Artifact `11309589083` was inspected before download. The download was capped
at its reported 32,244,929 bytes and matched its reported SHA-256
`05e11d77201b351ef58eac9c367bcbdc826b3964497504199ab7faccc3a860ac`.
Only the report and two logs were read from the ZIP; no source, crate, Git
snapshot, Cargo build or Lean build was produced. The temporary ZIP is not a
dependency of this retained packet.

The report can be inspected using Python's standard library without extracting
the artifact or rebuilding anything:

```python
import gzip
import json
from pathlib import Path

packet = Path("tests/fixtures/review_v030alpha/hosted-distribution-37218876223")
report = json.loads(gzip.decompress((packet / "report.json.gz").read_bytes()))
print(report["status"], report["work"], report["commands"][14])
```
