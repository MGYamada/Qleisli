# First integration-run test repairs

The first actual integrating run passed four of the eight new tests and failed
four. `repair.json` binds the retained failure log and validation record. These
were test-input and expected-diagnostic errors; they did not identify a
production parameter-binding defect.

`source-map.json` links six untouched originals to separately named current
derivatives. Static declarations require `static`, and the existing operation
requirement syntax is `Apply(U)`. The original `static-mixed` and
`static-collision` first observations therefore rejected before reaching their
parameter patterns. Their old diagnostics cannot isolate a parameter-pattern
limitation. The corrected sources are checked separately in the Rust target.

The original unitary `main` effect case rejected at entry validation. Its new
derivative uses a valid observing entry and a unitary `leak` helper to reach the
intended effect check. Separately, both `check_project` and `compile_project`
already reject a non-nullary `main`; the test now expects `InvalidEntry` from
both. No entry rule changes.

The test helper explicitly selects only these six derivatives. It never repairs
source text while loading it. `test-repair.patch` retains the semantic test edit
before rustfmt; the repair manifest binds the final formatted test. The first
source manifest, actual failure, earlier validation inputs and observation bytes
remain unchanged. A later rerun must be recorded separately.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
