# Read-only audit discovery error

The first local metadata audit exited 1 before writing `audit.json`. This was
a reviewer path-base error: `first-files.json` names its 15 members relative
to the authoring session, whereas the other input maps use repository paths.
The audit initially resolved those 15 paths from the repository root. This
does not report changed candidate inputs or an adapter/native failure.

Actual tool-result transcript (the tool returned it; no separate raw log was
created by that attempt):

```text
Traceback (most recent call last):
  File "<stdin>", line 29, in <module>
AssertionError: ('/Users/masa/git/Qleisli/tests/fixtures/authoring_sessions/qft-exact-request-v030/first-files.json', ['README.md', 'attempt-01/Qargo.toml', 'attempt-01/transform.qli', 'capture-first.py', 'commands-before.json', 'context.md', 'identity-before.json', 'native-sentinel.py', 'preparation-checks.json', 'request-contract.json', 'requests/n0.json', 'requests/n1.json', 'requests/n2.json', 'requests/n3.json', 'session-before.json'])
```

Only the read-only audit's map resolution is corrected for its later attempt.
No candidate script was imported or executed, and no frozen input was edited.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
