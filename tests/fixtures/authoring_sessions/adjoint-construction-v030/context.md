# Adjoint construction access probes

Informed minimal source-contract probes for Issue #45, created after reviewing
the existing common checker, retained controlled-only constructor test and the
2026-10-07 decision that adjoint(U) requires Adjointable(U). Both temporary
complete source trees were preserved before the first CLI check and before any
production repair. This context/session metadata was transcribed afterward;
it is not falsely described as a pre-check manifest or a blind model benchmark.
No external model was invoked; exact deployed model/sampling is unavailable.

Expected contract: both unused generic declarations must reject for the missing
Adjointable path even though main is a separately valid zero measurement.
Actual baseline observation: both complete project checks returned ok. This is
a known source-contract gap, not evidence of an invalid native quantum circuit.
No run/algorithm oracle or source-preservation theorem is claimed. Subsequent
checks will be appended separately without replacing the first observations.
