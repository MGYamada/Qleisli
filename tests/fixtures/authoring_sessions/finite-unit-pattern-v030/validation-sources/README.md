# Explicit integration-test sources

These thirteen additional inputs were saved after the frozen baseline and
before the new Rust target was run. They are separately named validation inputs,
not revisions to any first attempt. `sources.json` hashes their exact bytes.

`tests/unit_patterns.rs` reuses these and the original sources. It checks exact
ordinary pattern identity and rejected owner/effect/arity cases, compares
retained Discard/Init0/Observe operations to a named-binder control, and requires
the actual native-checked function matrix to equal the independent scalar
`exp(i pi/4)`. The scalar multiplication loop is an algebraic consequence of
that equality, not three further native reference executions. Controlled
interference independently expects `(2 - sqrt(2))/4` for that phase, and `1`
for the computed Z phase. The sized cases separately execute native-accepted
proposals with two-dimensional references and unequal complex coefficients.

A same-width shape is never the oracle for source type equality. The Bit,
Unit product, quantum Unit, Bits<0> and Q<Bits<0>> counterexamples retain their
separate roles. General runtime parameter-pattern grammar remains rejected.
A private compiler unit test covers manually constructed public AST parameters;
no new public compilation API is introduced merely to test that guard.

The owning integration task records actual build/test/lint commands separately.
No successful Rust validation is claimed by this input inventory alone.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
