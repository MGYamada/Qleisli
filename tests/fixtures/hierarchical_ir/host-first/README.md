# Fresh hierarchy host: first source and diagnostics

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The initial Rust host/bridge and Lean protocol/main sources were saved before
their first checks. The Rust all-target check succeeded. The Lean build failed
because the unqualified `Artifact` resolved to the older phase-word protocol's
type, and positional cursor construction omitted fields with defaults.
`first-lean-build.txt` preserves the actual compiler diagnostics. Qualifying
the hierarchy artifact and using named cursor initialization repaired the
build. No acceptance rule, axiom, policy exception or existing capacity changed.

The first host tests were preserved before execution. During review before
native execution, an encoding-index mutation was changed from index zero to
index one: index zero described the same identity endpoint and was not a
semantic counterexample. The original source remains intact. The first four
native tests all passed; `../host-native-first.json` retains that run.
Tensor, symbolic phase and structural/inverse cases then extended the suite
to six native tests. Their executed results and the independently handwritten
binary/truncation cases are in `../host-native.json`.

This is informed implementation and adversarial regression work. It is not a
controlled model study, a proof of native transport correspondence or evidence
that the complete sized-source corpus is finished.
