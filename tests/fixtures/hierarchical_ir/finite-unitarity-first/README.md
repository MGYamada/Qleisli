# Conditional finite unitarity: first source and repair

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

`HierarchicalFiniteUnitary.lean.txt` is the first source, saved before its first
build. `first-build.txt` is the actual compiler output. This is informed proof
development, not a controlled model experiment.

The first build exposed an ambiguous `physical` name from two opened
namespaces and singleton-list membership used as equality without first
eliminating membership. The final module opens only the required names from
the semantics namespace and explicitly derives the singleton equality.
No axiom, admission, runtime exception or budget change was introduced.

The repaired module builds. The packet's registry report records the full
package builds, declaration audits and independent kernel replay; the existing
conditional native suite remains a regression for the unchanged runtime path.
