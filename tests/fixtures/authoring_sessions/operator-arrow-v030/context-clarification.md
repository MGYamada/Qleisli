# Context chronology clarification

The original context.md overstates the order of the Issue reads. Issues 83/89,
the parser and existing source/effect contracts informed the initial drafting.
The fresh reads of Issues 45, 46 and 57 occurred after drafting, but before the
first CLI observations. All six design questions were reviewed before checking.
The original context, first sources and observed failures are preserved; this
clarification does not relabel the study as a blind benchmark.

The first executed observation driver omitted recorded_utc. The actual authoring
record checker rejected that missing field. Separate before/*.record.json
companions add the later normalization clock and the immutable raw-event path
and hash. That clock does not authenticate the time of the original command.
The originally executed driver and raw events remain unchanged.

The first summary reader mistakenly expected a flat raw_event_sha256 field.
Its actual KeyError and unchanged first script are retained separately. The
reader repair uses the existing raw_event path/hash object and changes no
original command or observation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
