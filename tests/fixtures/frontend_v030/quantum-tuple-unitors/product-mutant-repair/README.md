# Product-mutant test construction repair

The first actual library run rejected the newly constructed mutant at native
composition-instrument checking, before the intended source-event rejection.
The original run and full formatted pre-repair source are retained.

The test copied the phased helper circuit and its own request, but left the
original instrument wrapper in place. Unlike the earlier zero-wire Unit-map
example, split/join helpers can change the fresh owner identities referenced by
readout and preparation. The native rejection therefore did not test a valid
same-interface semantic impostor.

The repair transfers the complete helper instrument, graph, request and
preparation/event data while retaining the original direct split/join source
and its source-event locations. The test still requires fresh native acceptance,
actual omega coefficients, and then rejection by the canonical structural-tag
source check, for both join and split. No production behavior changes.

No build, test or formatting command was run by the repair author. The recorded
source hash identifies the input awaiting root validation; later formatting may
change it. See `record.json` for the first failure and exact before/after hashes.
