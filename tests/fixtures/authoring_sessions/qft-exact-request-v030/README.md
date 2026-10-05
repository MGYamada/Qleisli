# Bounded local QFT exact-request preparation

This is an informed follow-up to the retained
[local QFT family study](../qft-family-v030/README.md). The
[ordinary source](attempt-01/transform.qli) is an unchanged byte copy of its
licensed first translation: SHA-256
`12753179c20a3a45bb8420e5a4c6a41157b493dcf3f47314b4f41658b4644cfc`.
It retains Google LLC's 2023 attribution, Masahiko G. Yamada's 2026 translation
attribution and Apache-2.0. The pinned upstream is Qualtran `QFTTextBook`, commit
`8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`; the
[retained upstream file](../../../../corpus/upstream/qualtran/qualtran__bloqs__qft__qft_text_book.py),
[license](../../../../corpus/upstream/qualtran/LICENSE) and
[original translation context](../../../../corpus/sized/qualtran_qft/README.md)
remain separate inputs. No upstream material was fetched or modified.

[Context](context.md), [independent contract](request-contract.json),
[requests](requests/n0.json), [source/dependency identity](identity-before.json),
[fixed command plan](commands-before.json) and `first-files.json` are prepared
before this stage's first output observation. All four complete requests are
independent inputs; producer meanings do not supply the expected contract.
The explicit schema-2 manifest keeps edition `2026`.

The positive requests for widths 1–3 specify
`F_n[y,x] = exp(+2*pi*i*x*y/2^n)/sqrt(2^n)`, with axis zero of weight one,
fixed global phase and included real output reversal. Width zero has a
separately chosen **single identity-rewire** request on one owner0 `Bits<0>`
port, empty axes and no classical values. This choice precedes FIRST emission.
An unexpected emitted header or shape will remain a failure against that frozen
request; it cannot select a new request shape. `Bits<0>`, `Unit` and zero
logical owners remain distinct. Native named `qft(0)` is not requested.

The [first driver](capture-first.py) is prepared for root review and execution:

```sh
python3 tests/fixtures/authoring_sessions/qft-exact-request-v030/capture-first.py
```

It constructs exactly four existing CLI `emit-proposal` calls for widths
0,1,2,3. It records ordered argv, cwd, timing, raw stdout/stderr/status and
untrusted output hashes. It makes no native request, inspection, adapter,
coefficient/reference probe or Cargo/Lean build. Source, dependency, request,
CLI and native-byte hash barriers surround each call. A fixed rejecting
[sentinel](native-sentinel.py) logs unexpected kernel attempts without
forwarding; zero attempted calls are a prediction until its actual logs exist.
The monitor covers the two fixed kernel environment variables, not a
system-wide process trace.

`first-emissions/` is a one-shot capture directory and is absent before actual
execution. Even a failed directory must remain intact. `session-before.json`
is immutable first metadata; the driver creates `session.json` separately as
an observation index only after actual completed process observations. No
empty live authoring session is installed before checking.

First-stage outputs remain untrusted. Successful emission establishes neither
native acceptance nor exact meaning. A later separately authorized experiment
must retain actual first failures and independently review any adapter and
fresh-native-valid negatives. General analytic Fourier/source preservation,
fixed-specialization equivalence, canonical std API exposure, constitutional
guarantee admission, Issue completion and release readiness remain separate.
