# Exact matrix transport: first source and repair

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The five `*.rs.txt` files are the first implementation and test sources, saved
before running the targeted tests. `first-build.txt` retains their real compiler
failure. This is informed implementation work, not a controlled model study.

The test incorrectly treated the existing total `Exact::phase` constructor as
a `Result`. Removing the unnecessary `unwrap` repaired compilation. No scalar
semantics, capacity, public enum or trust policy changed. Subsequent validation
is recorded in the packet's validation report.
