# Policy aborted-count reporting repair 01

The original driver and README bytes are preserved as text snapshots before
this root-authorized repair. No prospective policy map existed at preparation;
no previous map or observed result is refreshed. The exact patch changes only
the wrapper-aborted reporting branch.

Concurrent pool.map can raise before records.extend completes while other
workers already launched commands or wrote command records. Therefore the
old in-memory list length is not a trustworthy actual launched-command count.
The repaired branch reports retained command-record file names and their count,
and explicitly reports the actual launched-command count as null/unknown.
Retained files themselves are not asserted to be complete or successful.
Startup rejection's zero commands and the success path's 17 fixed checks and
regression criteria remain unchanged.

This is an authored, unexecuted preparation repair. No import, syntax check,
freeze, validator, test, build, CLI or native execution was performed. The
independent reviewer will reread the exact patch and final hashes before root
executes. No CI, proof, adoption, guarantee or Issue result is claimed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
