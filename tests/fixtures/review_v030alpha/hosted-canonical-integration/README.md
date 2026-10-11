# First hosted canonical-type integration failures

GitHub Actions run 37217706111 belongs to PR #307 head
`cc114298d29293f0f1550656c89af5d15951120e`. The actual pull-request checkout is
merge commit `2f03b7c1b9c34210f62abb7f5ae800d9d4c4d2df`, not the head SHA.
These are exact selected failure excerpts from the job logs, not complete logs.

- Job 111481619958: the external-format test still selected the original
  `tests/fixtures/interop/terminal` source after canonical-type migration.
- Job 111481620109: the missing-context release CLI test inherited the hosted
  GitHub environment and reached a different legitimate rejection first.

These failures remain failures. Local test success did not establish the
hosted environment or all external-client paths. Repairs and rerun results
must be recorded separately; neither expectation weakening nor rewriting
historical source bytes is a valid repair.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
