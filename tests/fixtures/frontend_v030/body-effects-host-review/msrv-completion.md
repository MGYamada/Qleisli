# Completed minimum-version validation

The actual Rust 1.85.0 run completed the same source/native-bound all-target
suite as Rust 1.98.1: 788 passed, zero failed and 52 existing default ignores
across 90 reported groups. All-target Clippy with warnings denied also passed.
The 184-source and native maps are byte-identical between both complete runs.
msrv-completion.json retains the actual ignored test names/reasons; none is
relabeled as executed. summary-retry-01.json summarizes both terminal results.

The 258 members of the initial packet-files.json remain byte-identical,
including its then-pending MSRV notice. These additional results complete that
local observation rather than rewriting the historical notice or first failures.
Current-head hosted CI and whole-plan completion remain separate. No fresh local
Lean replay, optional-lane completion, new guarantee or release is claimed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
