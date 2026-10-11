# Frozen prose whitespace check

The actual staged whitespace check rejected final empty lines in two frozen
review reports and the earlier Issue checkpoint README. Their exact bytes are
already bound by retained review/input/file maps. Preserve those historical
bytes rather than changing the recorded reports after their checks.

The parent fixture .gitattributes lists those three exact prose paths only.
Other maintained Markdown, source and fixture paths retain whitespace checking.
The existing six exact patch/libtest attributes are unchanged. This uses no
hidden Git override or global whitespace setting. Raw failing output and exit 2
are retained separately from the following successful staged check.

The first additive final map remains unchanged. The second map additionally
binds this whitespace record; neither rewrites an earlier frozen packet.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
