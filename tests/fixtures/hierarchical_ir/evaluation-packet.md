# Construct denotations from actual supported bodies

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The previous operator theorem assumes a global `Interprets` environment.
Replace this premise for the supported derivation language with a constructed
partial mathematical evaluation of actual definition and meaning bodies.
Read the actual child lists; fail on unsupported nodes, absent references or
unresolved children. A zero repetition must still evaluate its body.

Use decreasing fuel to define a total partial evaluator, prove successful
results persist at larger fuel and are unique, then prove that actual accepted
finite derivations supply sufficient fuel and equal successful values. The
direct-power schema must account for both actual control and repeat/power
nodes. Obtain shared-DAG acceptance from the actual empty-cache checker and
bind the conclusion to the selected entry, not a duplicate witness graph.

This is a mathematical denotation constructor in the separate proof package,
not the reference simulator or an expansion-based verifier. Concrete complex
evaluation may use large finite sums; no such sums enter the executable Lean
checker or its shared verification budget. Keep the remaining full-profile
rules, finite reconstruction, unitarity, external binding and source/runtime
integration explicit. Preserve the existing native phase/power semantic
counterexamples and first implementation/diagnostics. Do not enable schemas
or mark v0.2.0 complete on this result alone.
