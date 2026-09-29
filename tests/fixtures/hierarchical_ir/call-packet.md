# Shared call expansion through existing rules

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The resumed 0.2.1 corpus goal needs shared calls with complete typed adapters.
Use the existing specified interpretation: caller inputs are permuted into
callee inputs; the shared callee executes; callee outputs are permuted into
caller outputs. Preserve phase, all owner slots (including zero width), tuple
shape and the single fresh renaming across both endpoints.

Implement this as an untrusted producer of two rewires and one three-child
sequence. The middle child remains a reference to the existing definition,
including large repeats. Do not add a convenience-only trusted rule or extend
an existing public enum. Meanings and proof premises must be independently
bound, and the resulting artifact must pass the existing derivation checker.
Prove the generated action equals the direct coordinate interpretation of a
typed call and preserves child unitarity and arbitrary reference maps.

Exercise actual expanded artifacts with independent monomial oracles and
phase/axis/provider mutations. Include nontrivial input/output permutations,
fresh IDs, zero-width owners, malformed types/maps and shared repeated bodies.
An adapter alone does not establish complete external call acceptance or
arbitrary translation adequacy; record the remaining integration gates.
