# Historical VM-22 inputs after the ordinary type cutover

The active language adopts `Bit`, `Bits<N>`, `Unit`, and `0` / `1` in the
0.3.0 migration tracked in issue #27. The VM-22 historical corpus and comparison
pins still identify the exact original bytes. They must not be refreshed to the
new spelling and presented as the original experiment.

`relocations.json` maps the 23 affected original paths to preserved copies.
All 23 historical SHA-256 values are unchanged. Most copies already belong to
the ordinary type cutover fixture; `before/` preserves the five original Python
clients that were not in that fixture. `inventory-before.json` records the
inventory at the stated baseline commit. The current inventory pins this
relocation record and the original inventory as well.

The active Rust tests, Python clients, and corpus sources keep their original
working paths with current language spelling. Their validation is recorded in
the ordinary type cutover and independent comparison fixtures, not retroactively
in the original VM-22 observations. Relocation proves byte identity only; it
does not establish semantic preservation or replace a test run.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
