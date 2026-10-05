# Independent preparation-only native capture review

Status: local, non-normative advisory review by `/root/isometry_docs`, separate
from capture author `/root/review_isometry_adapter`. The five announced frozen
candidate hashes match. All 61 selected frozen packet files and 233 FIRST
identity rows still match; the selected client is `683b2974...03d8294` and native
is `39effde0...53c90c85`. `inputs.before.json` retains the full identities.
No driver/helper/forwarder, client, QFT/native command or build was executed.

I read all of `capture-originals.py`, `log-native.py`, `bounded_process.py` and
the current implemented client source. No blocking defect was found for this
fixed eight-command original-payload capture. This is source review, not a
successful capture, timeout test or process-behavior certification.

The driver chooses widths 0, 1, 2, 3 and inspect then request at each width.
Its executable, wrapper, payload and request paths are fixed source constants;
record metadata is used only for byte/mode/inventory barriers, never to choose
commands. The explicit client and capture-map hashes, native/CLI hashes,
complete selected FIRST identities and inventories are rechecked before and
after every observation. Original payloads and independent requests are not
rewritten, adapted, normalized or replaced. Unique output directories and
exclusive JSON creation preserve prior records, including partial failures.

The client retains its 1 MiB regular-file/read limits and calls only the existing
explicit-path native APIs. On success it checks exact retained payload/request
bytes, no candidate and no instrument. Its API errors intentionally combine
decode, pairing, transport and native stages; the outer recorder does not treat
that JSON alone as evidence of native execution or acceptance.

The forwarder permits only the three exact existing hierarchy modes paired
with `0.3.0-alpha`, invokes the fixed native path and checks its before/after
file identity. Input reception has a five-second deadline and 1 MiB limit;
an excess sentinel byte is retained as a labeled prefix without native spawn.
The streaming helper never invokes a shell. It concurrently writes bounded
stdin and drains stdout/stderr, with separate 1 MiB caps. It records actual
stdin bytes written, spawn errors, signed child status, timeout/overflow reason
and retained raw prefixes; no synthetic native response is manufactured.

The native deadline is 45 seconds, the client deadline 55 seconds, and kill/reap
grace at most two seconds. Separate process groups are explicitly disclosed.
The ordering `5+45+2<55` is intended to let the inner forwarder finish first;
it is not an all-descendant kill guarantee or a wall-clock bound on Python
startup, hashing, filesystem work or scheduling. If the outer group is killed
before the inner recorder finishes, missing/incomplete inner records remain
operational uncertainty, not semantic rejection. The reviewed files make no
claim that an outer process group traces or kills every descendant.

Actual native counts come from a record written after successful native spawn.
Wrapper-only attempts and absent wrapper/process records stay distinct. Only
the exact current child-arity diagnostic with no observed wrapper receives
the Rust-pair-construction label. A started native process by itself is not a
native semantic rejection: retain its raw frame/status and distinguish native
responses from timeout, cap, spawn, identity or wrapper failures.

`eight-fixed-original-calls-captured` denotes recorder completion and identity
barriers. It does not require eight accepted calls, infer wrong-target semantic
checks, or repair real first failures. No mutant, canonical wrapper, compaction,
source repair, phase/axis adjustment or expectation change is included here.

The earlier request review's complete one-owner Bits0/Unit/zero-owner distinctions
and unchanged positive QFT requests apply. Existing conditional Lean Fourier,
unitary and finite-reference results retain their original finite/H premises;
native/decoder/source/general-family correspondence remains separate. Both
admitted ordinary QLV1 scopes and broader QS/PR/RS/EXACT duties are unchanged.
All 111 targets and all 24 #317 criteria retain their required scope; this
capture earns no Issue closure, new guarantee, canonical std API or release claim.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
