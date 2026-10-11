# Ordinary Bits source transport: informed first attempts

Task: bug #342, prerequisite work for #32/#250/#44. Context includes current
Reference, issue acceptance criteria and code inspection; this is not a blind
model benchmark. Edition 2026 and both protected guarantees stay unchanged.

Before implementation, preserve eight complete projects: singleton copy/drop,
closed Nat identity, nested Unit/Bit/Bits products, four ordered two-bit rows,
and measured correlated Bits results. Packing order is first bit then tail;
expected closed outputs are independently specified in expectations.json.
Native validity alone is not source correspondence. The experiments distinguish
finite project support from selected Raw transport and actual execution. Failures
before semantic checks do not establish owner/effect or type rejection rules.
No generic QFT, maximum-size quantum case or new guarantee is included.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
