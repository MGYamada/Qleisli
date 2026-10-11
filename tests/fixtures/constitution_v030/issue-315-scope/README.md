# Issue 315 scope expansion

The maintainer explicitly added Issue 315 to the active plan on 2026-10-05.
The selected scope is now the original 108 Issues plus 311 and 315: 110 total.
GitHub #142 remains the progress/decision tracker. This packet preserves the
actual criterion source and bounded release-gate regression result; it is not
an implementation of effect inference or a completed release acceptance index.

The checker now requires Issue 315 in G10, in the reviewed requirements, and in
the acceptance evidence. Synthetic tests reject prior 108/109-Issue packets that
omit new groups, requirements or acceptance. Their hosted context and success
receipts are deliberately fabricated test inputs, not release/proof evidence.
No constitutional text, interpretation, admission or guarantee is changed.

`tool-observations.txt` transcribes the actual three command-output chunks from
this run. The tool combines process output; these are not asserted to be an
independently captured stdout/stderr pair. The source map identifies the exact
checker and test bytes used. No Rust/Lean test is needed for this scope change.

The original Issue body remains unchanged in this snapshot. Its fourteen actual
criteria remain pending implementation and verification. #283's post-v1 external
realization problem is not included or implemented by adding this Issue.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

