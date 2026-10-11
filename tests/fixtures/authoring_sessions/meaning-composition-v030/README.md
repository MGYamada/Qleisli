# Exact finite Meaning composition study

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed #46 study preserves four first sources: Z followed by X, its
wrong-order provider (differing by global minus), ordered Z tensor X, and a
wrong-axis provider. All first baseline checks fail at the new constructor's
parser boundary; those failures do not test the intended negative rules.

After implementation, attempt-01 reaches private entry visibility errors.
Attempt-02 changes only entry visibility; its selected CLI checks hit the
existing observing/Raw-Meaning profile boundary. Attempt-03 is an explicit pure
entry adapter for the same targets and provider bodies. Both correct clients
pass real native checking and both wrong providers reject. Original sources,
actual CLI JSON and integration failures remain in [session.json](session.json)
and `observations/`. No command is loaded from a record and executed.

`tests/operation_parameters.rs` checks the observing attempt-02 through the
finite route and the pure attempt-03 through the selected route. Both must
actually check provider Meanings, and the selected proposal subsequently needs
fresh hierarchy acceptance. Separate internal target tests use literal expected
permutations/phases, including forward references, scalar phase wrap and the
ordered Unit/Bit product; their expectations do not call composition helpers.

CLI success still reports producer consistency at the hierarchy boundary; the
explicit refined provider checks do not make the whole source preservation or
QS/PR/RS obligations proved. General arrows, nonmonomial/reference/instrument
Meanings, QFT2/QFT3 specifications and general native extensional equality remain
open. This is not generic QFT implementation or a blind model benchmark.
