# Explicit access vocabulary

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed maintenance study preserves three complete sources before the
#71 diagnostic change and six actual before/after CLI observations. No external
model was invoked and no blind benchmark is claimed. Source and edition-manifest
hashes remain unchanged; the baseline commit and executable hashes are recorded.

Unsupported `borrow q` originally reports an expected closing brace. It now
reports at `borrow` that there is no builtin resource form, distinguishes
explicit `excl`/`ctrl` access from clean/dirty restoration contracts, and states
that general clean/dirty source forms remain unsupported. The Rust `&mut`
candidate retains its reference refusal. The ordinary first-order function
named `borrow` passes both checks. These are source-check observations, not
execution or source-preservation evidence.

Separate regression tests cover both public source paths with an absent native
checker, Unicode/CRLF locations, ordinary and quantum-containing input types,
normal declarations/bindings named `borrow`, and text/JSON diagnostics. No
access mode is inferred and no workspace obligation is discharged. First
observations are retained rather than regenerated; no constitutional guarantee
is added or weakened.
