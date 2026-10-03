# Local 0.2.9 maintenance validation

Development version 0.2.9 is unpublished. [Changes](../../../../CHANGELOG.md)
cover synchronized agent instructions, the trust-policy rename, nine new corpus
translations and the documentation cleanup requested on 2026-10-03.

[Maintenance results](maintenance-validation.json) record performed and skipped
checks. The [corpus session](../../../../corpus/authoring/v029-small/README.md)
retains first sources, diagnostics and the negative-fixture calibration. All 87
cases pass 15,889 complex-entry/protocol probes, four source rejections and 63
semantic faults; the nine additions account for 646 probes and nine faults.
The three upstream pins, licenses and earlier 78 contracts are unchanged.

At the initial maintenance checkpoint, the verification migration plan and
imaginary-v1 remained in `docs/`. The later approved cutover removed that plan;
only imaginary-v1 and `docs/lean-backend-plan-v0.3.md` now survive the cleanup.
The other 27 document/metadata files are temporarily in `docs-old/`, scheduled
for deletion at v0.3.0. Active links and checker dependencies were removed;
metadata and source/proof/semantic checks remain. The old generated status views
and prose-only template/pilot linter were retired with their document inputs.

[Source review](documentation-source-review.json) records the ten version/comment
hash updates to the VM-22 inventory, without changing executable bodies or
behavioral comparison artifacts. [Quickstart](quickstart-after-docs.json) uses
the rebuilt local CLI, not a registry installation. The earlier
[registry audit](schema-registry-validation.json) belongs to this version's
metadata selection; this follow-up changes no Lean definition. Full release
CI, publication and new maximum-size experiments were not performed.

The subsequent [maintenance follow-up](debt-repayment/README.md) records failure
reporting, repository-wide Markdown discovery, shared native dependency builds,
version/source-binding tooling and the checked VM29 coverage audit. Its complete
local native comparisons and fresh kernel replay extend the earlier validation
above; hosted release CI and publication remain separate.
