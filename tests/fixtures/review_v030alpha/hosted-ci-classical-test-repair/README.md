# Classical declaration integration test repair

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

CI run 37426898081, Rust job 112148931401, failed its library suite on the
positive parameter-pattern reader still using `basis fn`. The exact decoded
failure excerpt is retained here. Original test source is immutable at commit
fd0d88dc48ee428905d5fa448e5aca338eef11ac, `src/frontend/parser/tests.rs`;
its source SHA-256 is dbaa96f9b74cfb468274490de5068d06fab5d7d6760adcb097f3e434ca3a0e87.
The repair changes that positive declaration spelling to `classical fn`;
argument-count, pattern-tree and source-span assertions remain unchanged.

The new distribution failure preview exposes the same parser refusal in job
112148931430 of run 37426898081, during the offline source-production all-target
test. Its exact decoded excerpt is retained separately. This establishes the
cause of that run's distribution failure; it does not establish the unobserved
inner cause in earlier run 37422505870.

Root's first local all-target run also found the older body-effects test
assuming total finite functions have no ordinary runtime effect report.
The current classical-function contract requires their pure bodies to participate
in inference. The repaired test requires inferred Unitary and no asserted effect;
it does not remove an assertion or confer inverse/control access.

That first local library run additionally failed the inherited-pipe test because
the sandbox denied its `ps` subprocess. The same unchanged test passed outside
the sandbox. This is a separate environmental observation, not the hosted
parser failure's cause. No full first-run success or release is claimed.

Only the changed test-file hash and its derived VM29 fingerprint are refreshed;
public surfaces, capacities, groups, acceptance routes and proof gates are unchanged.
