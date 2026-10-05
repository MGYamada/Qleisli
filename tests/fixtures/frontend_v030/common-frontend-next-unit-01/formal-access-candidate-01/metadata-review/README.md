# Checked formal source bindings

Root reviewed the six existing Rust changes and new private `formals.rs`
before executing the fixed [driver](driver.py). The actual
[attempt record](attempt-01/results.json) retains the original source plan,
before/after metadata snapshots and every command's separate raw output.

The initial inventory check really failed on the old source hashes; the initial
coverage check passed. `maintain_release.py --write` then refreshed only the six
explicitly reviewed existing bindings. The new private source row was added
with the existing inventory scanner. All 254 resulting source hashes were
checked. Other parsed inventory fields remain unchanged; coverage changes only
its derived `surface_sha256`. Both final checks passed.

The source plan contains no product or dependency version changes. The bounded
surface scan includes methods on private types and does not establish a public
API, source preservation, new acceptance authority, proof discharge or release
readiness. Routes, criteria, proof statuses, edition and constitutional records
remain unchanged. This driver is a one-shot historical maintenance record, not
a generally rerunnable metadata migration command.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
