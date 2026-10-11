# Archived historical validation records

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

The 61 original files from commit `f73551fdb8257fd06d5d6fc615095a54962df40d` are preserved in
[the lossless archive](../validation.tar.gz), with full original paths, byte
lengths, executable modes and SHA-256 hashes in [the manifest](../validation.archive.json).
The original README, if present, is an archive member too. This is historical
command evidence, not a current executable fixture or a claim of new validation.

Run `python3 scripts/check_fixture_archives.py --git-baseline` from the repository
root to compare every member with the complete original Git inventory. This
existing bounded checker neither extracts nor executes the records. To inspect
a member, use its exact repository-relative path from the manifest with
`tar -xOf ../validation.tar.gz MEMBER_PATH` from this directory.

The maintainer requested fixture consolidation on 2026-10-10. Current inputs,
first-source authoring sessions, counterexamples, constitutional evidence and
licenses remain outside this consolidation. No historical result is regenerated,
no acceptance rule changes, and no size or expansion ceiling is raised.
