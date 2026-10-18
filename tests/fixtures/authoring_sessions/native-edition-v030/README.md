# Native edition first study

This informed manual study precedes implementation of [#255](https://github.com/MGYamada/Qleisli/issues/255)
and the related [edition/release boundary #137](https://github.com/MGYamada/Qleisli/issues/137).
No external model was invoked. The immutable [archive](first.json.gz) preserves
791 original files, 1,566,434 expanded source/log bytes, including the unchanged
757-member `SESSION.pending.json` and 33 later native-study records. The old
index's pending status remains historical; it is not rewritten into approval.

The archive has SHA-256
`80df6cba3f022d8b2aafe4824c468d034309d100f61e5cbbc784b83f6e11483b`.
Gzip and base64 are storage only. The fixed integrity reader hashes and decodes
in memory, verifies every original byte/mode and index member, and never runs
captured scripts, commands, binaries or packets.

- Attempt 01 used unsupported `--json` in all ten commands. These usage
  refusals establish no source-edition or native behavior.
- Attempt 02 corrects only the CLI option to `--format=json`. Seven manifest
  problems reject before native invocation; explicit 2026 initialization
  succeeds with 76 recorded native calls. The scalar's quantum-valued `main`
  separately gives `invalid_entry`; its diagnostic exists, but an assertion
  interrupted separate per-case command metadata retention.
- Attempt 03 changes that function name to a library declaration. Scalar
  checking succeeds with 76 native calls; a nested 2027 manifest rejects before
  native invocation. First sources and failures remain separate from repairs.
- The thirteen-mode inventory is a static reading of the original Main source.
  Only seven native queries on the existing one-bit ordinary identity were run:
  QLV2 accepts, wrong product rejects, proposed QLV3 editions 2026/2027/0 all
  reject as `format`, and an external QLV1 or trailing QLV2 also rejects.

The actual old QLV2 header and native response lack requested-edition context.
This records the missing implementation; it is not a native edition proof.
The observed head is `c6a95e8488ad44bc398f9cfa97def807058436e5`.
Captured source windows and CLI/kernel digests identify the observed prior
bytes, not a fresh clean build or compiler/runtime preservation theorem.
The two direct local windows (1.601 and 1.583 seconds) are not CI benchmarks.

No QLV3 implementation, new accepted API, general QLT, maximum-size quantum
case, new guarantee, Issue completion or release is claimed. The existing two
scoped QLV1 guarantees and broader pending QS/PR/RS/EXACT duties remain.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

The later [context-source archive](context-source-first.json.gz) retains eight
pre-change source files at `8dde351ce8c19d091bdae01c3e9ea49d5e34b368`, before
typed edition selection and immutable filesystem manifest capture. Its SHA-256
is `9393bc8b48d43ca3d45b6ed729ce5528593366004650a793b699a878cc208cfb`;
192,671 expanded archive bytes are checked passively by the same reader.
This source record claims no native edition check, proof, CI or completion.
The [first capture-test record](context-tests-first.json.gz), SHA-256
`1c619586c16e5732311717333591e5d7a2c7424be6dfa98565bd67feb685db61`,
retains five source/report/log records (37,249 expanded archive bytes).
Three tests failed in setup because their parent directories had not been
created. Those refusals are not native/checker failures; the repair creates
the intended directories without changing the asserted contracts.
The [first validation record](context-validation-first.json.gz), SHA-256
`e9f8a889bd773390d4e86d7b3fc915374069aabf9a2c609134528f2aae5f6948`,
retains eight source/report/log records (124,306 expanded archive bytes): four
needless-borrow lint errors and an unrelated sandbox process-syscall denial.
The latter test passed when rerun outside the sandbox; neither is native proof.
The [first migration record](context-migration-first.json.gz), SHA-256
`228aaa63263873bbdb101f56da047859595b0c5d0687bf364db94364687e8e85`,
retains 13 source/report/log records (1,039,731 expanded archive bytes).
It preserves the later MSRV lint, source/route inventory refusals and the
old source-only capacity diagnostic expectation. That native attempt passed
51/52 cases and stopped before MSRV; its partial result is not completion.
