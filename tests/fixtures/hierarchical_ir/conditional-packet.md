# Conditional whole-artifact derivation with reconstructed finite obligations

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Xor/GHZ/QFT need finite H/CNOT leaves inside checked structural composition,
tensor, inverse, coherent control and repetition. The existing ordinary entry
must continue rejecting unsupported opaque leaves. Add a separate pure entry
that traverses the same actual artifact and accumulates every finite request
from `Finite.inspect`, while checking all other rules with `Rule.check`.

The entry starts with an empty cache and request list, invokes full artifact,
node, meaning and encoding typing, and shares the existing structural budget.
Check each actual premise before a consumer. A count-zero repetition still
retains and requires its body; no supplied cache, request list or success flag
is accepted. Store complete requests once per checked finite proof, without
expanding calls or repetitions. Keep existing artifact byte/reachability and
capacity checks; exact finite work remains a separate shared Rust budget.

Prove that success constructs an actual finite derivation conditional on
discharging every returned bound request, with exact original rule/premise
matching. Prove that every returned request came from successful inspection on
that artifact and that every cached result has this conditional derivation.
The theorem must quantify the remaining finite predicate explicitly. A pending
artifact is not a production semantic seal and cannot be executed as verified.

Native checks should combine independently supplied meanings with finite H-like
opaque leaves, typed compositions and powers through count 4096; exercise
multiple shared leaves and different table order. Reject wrong premise order,
counts, endpoints, encodings, cycles and limits, including invalid zero-repeat
bodies. Program/meaning mutations must remain in the returned obligations and
must be discharged by fresh finite reconstruction, not accepted because their
headers match. Keep first source and actual diagnostics. Complex interpretation
and the transport/Rust connection must follow without assuming a producer's
claim or changing the complete v0.2.1 corpus goal.

For the mathematical bridge, extend the separate partial evaluator with leaf
readers over actual interface/payload bytes. The implementation and meaning
readers are independent; equality for every returned request is an explicit
remaining premise. Recursively construct a common successful denotation from
the conditional derivation, including both ordinary rules and direct controlled
powers. Prove uniqueness and exact complex matrix/reference equality without
an assumed whole-graph environment. Leaf-reader correspondence to the Rust
decoder and complete finite-unitarity integration remain separate obligations;
these mathematical readers are not an execution adapter or an authority flag.
