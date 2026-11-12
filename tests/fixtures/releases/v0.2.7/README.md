# v0.2.7 release evidence

`publication.json` binds the authorized crates.io/GitHub publication to clean
commit `7844a10d63880a2b6984c093e2dc7a75033d1e1e` and annotated tag `v0.2.7`.
Publication completed on 2026-10-03 (Asia/Tokyo); candidate selection was October 2.

The exact-source full CI selection, all successful jobs, native coverage and
complete command logs are retained in `ci-selection.json`, `native-ci/`,
`native-coverage.json` and `publication-command-results.json`. Raw logs use
lossless gzip so their output whitespace is preserved without treating it as
source formatting; `publication.json` maps original names to stored paths and
records both raw and compressed hashes. The distribution
reports preserve both hosts' full source inventories and command results;
`local-distribution-logs/` and `linux-distribution-logs/` preserve their logs.
Original temporary paths remain in reports as execution evidence, not reusable
paths. Copies here are bound by hashes in `publication.json`.

Downloaded registry bytes, VCS metadata and notices match the checked package.
GitHub tar and ZIP contain every tagged source file with matching bytes; tar
allows only GitHub's additional group-write bit. ZIP omits POSIX mode metadata,
so permissions are independently checked in tar; all Git files are non-executable.
Fresh registry installation, shipped README examples, live pinned links, rendered
registry README, GitHub Latest/body and the actual hosted docs.rs build passed.

The original `validation.json`, `documentation-reduction.json` and
`schema-registry-validation.json` remain unchanged historical development
records, not claims about this later exact-source candidate. The tag/artifact
is immutable; publication evidence and status updates are committed afterward.
No PyPI/custom binaries or new maximum-size cases were generated. Existing CI
capacity regressions were retained. General theorem and authority-transfer gates
remain open.

The historical branch-function packet is retained in
[native-ci/lean-branch-function.tar.gz](native-ci/lean-branch-function.tar.gz),
with the complete original inventory and hashes in
[its archive manifest](native-ci/lean-branch-function.archive.json).
The four original paths, bytes and modes are recoverable from that archive
or [the immutable Git snapshot](https://github.com/MGYamada/Qleisli/tree/b76fbc6702648fd5612af0814bbd6f13034a4d61/tests/fixtures/releases/v0.2.7/native-ci/lean-branch-function).
Existing publication records retain their original path/hash identities.
The archive checker compares every member against that snapshot; it does not
execute historical commands or supply a new successful validation result.
Current branch-function tests generate their own inputs and do not consume
this historical packet.
