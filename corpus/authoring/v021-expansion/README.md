# 0.2.1 corpus expansion: first-source record

The [session](session.json) records six informed translations, two per approved
source. All `attempt-01` files were saved and hashed before the first QLI check.
The [initial checks](check-initial.json) accepted all six projects; there was
no source revision. The author had repository, upstream and known-workaround
context. No controlled model-performance claim follows from this observation.

The [semantic observation](semantic-validation.json) records the actual command,
exit, transcript and hash of the [full 30-case result](../../validation-v0.2.1.json).
It passed 11,849 probes and the existing four rejection cases, and detected six
type-correct algorithm faults. These faults were deliberately written separately
under [semantic_faults](../../semantic_faults/README.md); they are not first-attempt
failures. Upstream frameworks were not executed.

The older [24-case session](../session.json) and its snapshots remain unchanged.
The corpus checker checks each observation against its own snapshot projects,
then checks that both latest snapshots cover every current `.qli` file.
MIT/Apache-2.0 notices remain attached to each source; the external source set
is unchanged.
