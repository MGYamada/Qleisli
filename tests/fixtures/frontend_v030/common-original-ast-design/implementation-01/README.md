# Historical common-AST implementation packet

The original 946-file packet is preserved without byte or executable-mode changes
in [the lossless archive](../implementation-01.tar.gz). Its
[manifest](../implementation-01.archive.json) binds every original path, size,
mode and SHA-256 to Git commit `842b1457af6577275acefb9453b12b3b195c75c5`.
The original README, first sources, failures, diagnostics, empty success logs,
source snapshots and validation tools are included. Historical references to
paths below this directory identify archive members using their full original
repository-relative paths; they are not current executable tests.

Run `python3 scripts/check_fixture_archives.py --git-baseline` from the repository
root to compare the complete archive with that immutable Git source. The checker
reads records without extracting or executing them. Parent design records remain
in place. This consolidation was explicitly authorized by the maintainer after
preflight; it changes no acceptance rule, proof status or historical observation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
