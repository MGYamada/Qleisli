# Contract counterexample first observations

[Issue #270](https://github.com/MGYamada/Qleisli/issues/270) records these
observations against v0.2.8, commit
`18020190b1c80037442be29d74e90fd9e07253e0`. Its source excerpt was:

```qli
unitary fn swap_by_cnots(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)> {
    let (a, b) = split(q);
    let (a, b) = cnot(a, b);
    let (b, a) = cnot(b, a);
    join(a, b)
}
unitary fn swap_spec(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)> {
    do (a, b) <- q;
    pure (b, a)
}
// ... apply_contract(swap_by_cnots, swap_spec, q)
```

The original reported permutation diagnostic was:

```text
main.qli:19:5: invalid_ir: function semantic contract: exact equation U E_in = E_out u does not hold; input column 2, output row 1 (zero-based): actual 0, expected 1
```

For the phase case, the issue reports the following detail from replacing
`z` with `s` in a CZ specification:

```text
input column 3, output row 3 (zero-based): actual -1, expected 1*i
```

The saved projects are separate edition-2026 reproductions. The two-CNOT
case replaces the removed coherent syntax with the standard structural
permutation. The one-bit case isolates the same `-1` versus `i` coefficient.
The native-backed CLI test checks both current text and JSON. The historical
excerpts above are the observations reported in the issue. The full v0.2.8
projects, their manifests, command arguments, timestamps, exit status and
structured output are unavailable. The phase report preserves a diagnostic
excerpt but does not give the original source.

[Session record](session.json) indexes the complete edition-2026 projects
by their source and manifest hashes. The [permutation manifest](attempt-01/permutation/Qargo.toml)
and [phase manifest](attempt-01/phase/Qargo.toml) preserve the exact bytes
written for the initial reproduction. Both project snapshots also preserve
the unchanged CLI test sources.

## Observed edition-2026 baseline

Both reproductions exited 1 with no stderr under the existing beta CLI
(using `check PROJECT --lean-kernel=PATH --format=json`). The CLI SHA-256
was `ce61a87617b2730e220604948df33c153f6cb92620580b420ad1ebc69171ac8f`
and the kernel SHA-256 was
`0b86efa7c112cbecd1ca31c2fa619b94428806a9a975203dfe8997c6c096af3d`.
These are prior binaries with the original diagnostic behavior. The session
baseline identifies the source checkout for this work, while the executable
identities are the two hashes above.

The initial project directory came from a temporary directory that was
removed. Its randomized path and the time of that invocation were not
recorded, so the initial stdout below has no synthetic timestamp or command.
The separately recorded [permutation replay](replay-permutation.json) and
[phase replay](replay-phase.json) have actual commands and UTC timestamps.
Both used the same executable hashes and reproduced the initial stdout
byte-for-byte, including its final newline.

Permutation stdout:

```json
{"format":"qleisli.result","version":1,"command":"check","outcome":"error","diagnostics":[{"code":"contract","severity":"error","message":"function semantic contract: exact equation U E_in = E_out u does not hold; input column 2, output row 1 (zero-based): actual 0, expected 1","primary":{"path":"main.qli","start":446,"end":489,"line":17,"column":5},"related":[]}],"result":null}
```

Phase stdout:

```json
{"format":"qleisli.result","version":1,"command":"check","outcome":"error","diagnostics":[{"code":"contract","severity":"error","message":"function semantic contract: exact equation U E_in = E_out u does not hold; input column 1, output row 1 (zero-based): actual -1, expected 1*i","primary":{"path":"main.qli","start":251,"end":286,"line":7,"column":5},"related":[]}],"result":null}
```

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
