# Exact instrument contract experiment

This bounded #46 study investigates an **unadopted** observing overload of
`apply_contract`. The [concrete packet](proposal.md) states its scope, expected
programs, native boundary, equality limits and remaining proof obligations.
It is ordinary language design under the existing adopted interpretations.

Run the independent host algebra, optionally with fresh VM-26 reconstruction:

```sh
python3 experimental/instrument-meaning/check.py --record /tmp/instrument-host.json
python3 experimental/instrument-meaning/check.py --native --record /tmp/instrument-native.json
```

The [first source study](../../tests/fixtures/authoring_sessions/instrument-contract-v030/README.md)
retains four original projects, their current refusals and the actual native
experiment record. Native compilation uses the existing shared harness; its
temporary driver is removed on exit. No results or acceptance decisions are
cached. The CP comparison here is untrusted experimental Python, not a new
production semantic gate or constitutional discharge.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
