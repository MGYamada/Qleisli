# Release CLI test environment isolation

GitHub Actions run
[37217706111](https://github.com/MGYamada/Qleisli/actions/runs/37217706111),
docs job `111481620109`, reported a failure in the missing-context CLI test.
The PR #307 head was `cc114298d29293f0f1550656c89af5d15951120e`; the actual hosted
pull-request checkout was merge commit
`2f03b7c1b9c34210f62abb7f5ae800d9d4c4d2df`. The original hosted excerpt is retained
separately in
[the hosted integration record](../../review_v030alpha/hosted-canonical-integration/README.md).

`before.json`, `before.stdout` and `before.stderr` record the first local
reproduction before editing the test. A representative PR environment was
explicitly simulated, including `GITHUB_ACTIONS=true` and
`GITHUB_EVENT_NAME=pull_request`. Its local `GITHUB_SHA` and illustrative
`refs/pull/1/merge` are recorded as supplied; they are not the actual hosted
checkout identity or PR reference. The local failure exactly matched the hosted
diagnostic mismatch: the test expected missing trusted context, but inherited
context caused the CLI to reject the PR event instead.

The test had first removed hosted variables, but its CLI helper then rebuilt
`os.environ` and restored them. The helper now removes ambient `GITHUB_*` and
`RELEASE_*` variables before adding the context explicitly supplied by the
individual test. OS/tool lookup variables are retained. Passing an empty context
now means no hosted provenance, independent of whether the suite itself runs
inside GitHub Actions. The existing regression injects PR-job variables even
during a local run, so this dependency stays exercised. Other cases still pass
their explicit synthetic context through the real subprocess CLI.

Only `scripts/test_check_release_ready.py` changed. The production gate,
diagnostic expectations, trusted-context rules, acceptance rules and workflow
are unchanged. `before-test_check_release_ready.py.txt` preserves the original
test source. Production checker hashes in `before.json` and `after.json` are
identical.

`after.json` records the full **22-test** run under the same representative
hosted PR environment, with raw stdout/stderr, source hashes, Python identity,
argv and exit status. To repeat, apply its `environment_overrides` to the caller
environment and execute:

```sh
python3 scripts/test_check_release_ready.py -v
```

These are local synthetic-repository tests, not an assertion that the hosted
run or a release candidate has passed. They use real Python, local Git and CLI
subprocesses but simulate proof/build receipts; no Cargo/Lean build, publication,
large source snapshot or new guarantee admission occurred. Previous fixtures
were not rewritten.
