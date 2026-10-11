# Retained generic QFT attempts

The maintainer removed QFT implementation completion from v0.3.0 and
entirely from the current goal, then requested that the attempts remain under
`experimental/`. These files are retained experiments, not an available
canonical stdlib API or an active implementation task. No future target is
selected; [#317](https://github.com/MGYamada/Qleisli/issues/317) records the scope.

- [attempt-01/transform.qli](attempt-01/transform.qli): the first ordinary generic
  family candidate, including the zero-width identity branch.
- [attempt-02/transform.qli](attempt-02/transform.qli) and
  [reference.qli](attempt-02/reference.qli): the retained candidate and its
  bounded reference-client extension.

[Current retention](retention-02.json) binds these byte-identical files to their original
authoring inputs. The original family session, exact-request study and associated
trial tooling are retained only in [history archives](history/relocation.json).
Every original member path, byte hash and mode was checked before removing the
old fixture directories. Historical maps now identify archive members rather
than live checkout paths; recorded commands have not been replayed.
Copying files here executes no compiler or native checker and proves no source
preservation, exact specialization correspondence or general-family theorem.

The source adapts the pinned [Qualtran Fourier translation](../../corpus/sized/qualtran_qft/fourier.qli).
Its [corpus attribution and provenance](../../corpus/sized/qualtran_qft/README.md)
remain applicable. Google LLC's copyright and Masahiko G. Yamada's modification
notices are retained in every translated source. These files use Apache-2.0;
see the repository [LICENSE](../../LICENSE) and [NOTICE](../../NOTICE).

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
