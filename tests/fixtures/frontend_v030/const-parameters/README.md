# Current corpus parameter headers

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Issue [#33](https://github.com/MGYamada/Qleisli/issues/33) adopts contextual
`const` parameter headers. Baseline: `fff7296c9c8eef270b1ae8914a11d7db0b356979`.
The source map adds one stage after the existing quantum-fold migration.
It binds thirteen previously selected sources to complete current copies.
Only `static` parameter markers become `const`; bodies, loop binders and
licenses remain unchanged. The two excluded generic QFT sources are not copied.

The repository selection test checks the independent corpus file inventory,
the exact marker transformation and every selected source hash. Synthetic tests
check retained predecessors, stale destinations and refusal when the stage is
missing. Rust and Python current-source clients use the same selector;
their independent semantic expectations and native acceptance remain separate.
Original corpus bytes, manifest hashes and all prior migrations are retained.

An initial uncommitted attempt changed the original corpus files and refreshed
their corpus-manifest hashes. Rust correctly rejected this because those files
are also historical predecessors in the quantum-fold map:

```text
sized_cli_emits_only_an_untrusted_proposal_without_a_kernel ... FAILED
source fixture selection failed for corpus/sized/qualtran_qpe/estimation.qli
ValueError: source fixture identity changed: corpus/sized/qualtran_qpe/estimation.qli
```

Those edits were restored byte for byte before this stage was created. No
historical migration hashes were changed to accommodate the failed attempt.

`validation.json` records exact equality for thirteen parsed declarations and
32 small pure/instrument proposals. Instrument source-hash maps are checked
independently and excluded from semantic-object equality. Five current-source
Python/native/oracle checks passed. These are bounded checking experiments,
not a proof of preservation or completion of QS, PR or RS.

The related Rust targets (`sized_cli`, `sized_corpus`, `sized_source`,
`sized_linear_seeded`) passed on Rust 1.98.1 and MSRV 1.85: 45 tests passed,
eight existing ignored tests retained per toolchain. The Python selection
suite passed 50 tests and local resolution passed 19. Both ignored native CLI
tests were also run explicitly and passed on each toolchain; both all-target
Clippy checks passed. Source-integrity passed all five shared checks, docs and
corpus integrity passed, and constitutional continuity passed against the
previously verified `3e3128c6153df40eb8c6f8fbffeb6bce35a6085a`.
That continuity check is not a fresh Lean replay. Full CI and the unchanged
4,000-case ownership suite are not claimed by this record.

The prior host CI's MSRV 64-dimensional identity timeout is a separate open
investigation. The unchanged test passed locally alone in 25.80 seconds and
within its complete 16-test suite in 27.40 seconds. The timeout policy and
required case remain unchanged; local success does not explain the host failure.
