# Checked-operation migration: after-code expectations

This is an informed, bounded continuation of the unchanged first sources in
`attempt-01`. It is authored before any after-code command. The ordinary
[naming decision](https://github.com/MGYamada/Qleisli/issues/82#issuecomment-6009162442)
and its [lexical clarification](https://github.com/MGYamada/Qleisli/issues/82#issuecomment-6009306100)
change the source spelling to `checked_op(implementation, Meaning)`, retaining
the existing Bind AST and obligations. Runtime values and open formal providers
do not become closed checked declarations. No source repair is authorized by
these observations; any later repair needs a separate preserved attempt.

## Expectations stated independently of the new implementation

For the supported providers, the exact one-qubit actions are
`Z = diag(1,-1)` and `T^4 = diag(1,-1)`. Their equality retains the scalar phase.
The three-qubit client prepares, in `c,r,q` order,
`|+>_c tensor (|00> + omega |11>)_r,q / sqrt(2)` with
`omega = exp(i*pi/4)`. Candidate Z and controlled Z are followed by the explicit
sealed inverse actions, not by a second use of the candidate evidence. The
independently specified unpreparation must yield `000` with probability one.
The nested client has the exact action
`controlled(inverse(Z then Z^3)) = controlled(I) = I`, and must yield `00`.
These are literal mathematical expectations preserved before checking, not a
claim of a separate executed numerical oracle or a general preservation proof.

The unchanged desired negative cases must now reach their existing semantic
boundaries: `XZX = -Z` fails exact Meaning equality; equal-width nested and flat
three-Bit trees fail type compatibility; ordinary and quantum runtime provider
captures fail static-operation checking; an open formal provider fails finite
closed-declaration materialization; a consumed quantum owner cannot be reused.
The public desired `main::probe` selected entry must continue to refuse the
unsupported static operation constructor. Success of finite whole-source
checking must not be confused with selected concrete projection eligibility.

Every unchanged legacy source must receive a located parse/migration refusal
that identifies `bind_op` and teaches `checked_op`. It must not execute the old
spelling as an alias. JSON checks cover all sixteen sources; real default-text
checks cover the supported provider and wrong-phase pairs. Text is selected by
omitting the JSON flag: the four original `--format=text` usage failures remain
unchanged in the before record.

## Artifact comparison and limits

The two saved legacy QIRFs have `root_interface: null`. Their actual root ports
are empty quantum/classical inputs, empty quantum outputs, and ordered classical
outputs `[0,1,2]` or `[0,1]`, respectively, with effect `observe`. Each retained
provider/Meaning program has a one-bit input at wire zero, one quantum output,
and unitary effect. Both evidence signatures are `Bit`. The after study compares
these ordered actual ports and signatures against the saved artifacts. Neither
equal width nor the absent root-interface annotation establishes a full source
tuple-tree contract. The explicit wrong-tree refusal is a separate source check.

Source/evidence identities legitimately change with spelling. Whole QIRF byte
equality is not required, and no identity fields are edited to manufacture it.
Emitted artifacts and raw streams are retained with their actual hashes. The
small run results test the prescribed phase/reference/control interference;
their probability checks do not replace an all-input or source-runtime theorem.

The initial README overgeneralizes the unknown-name parser punctuation. The
original nested-constructor JSON control actually says `expected ','`, found
`'('`; the other finite desired controls say `expected ']'`, found `'('`.
Every one has code `parse`. This clarification preserves all original sources,
README bytes, observations and actual diagnostic strings.

## Institutional and recording scope

The constitutional continuity base is the previously reviewed commit
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; the first-source checkout
`a6e09a5960d9615b1f4356dcbf32bc33fd608e1f` is a separate source/build baseline.
The independent continuity check passed after the context reset. QS, PR, RS and
EXACT broader obligations remain pending; the two admitted ordinary QLV1
ownership/classical-scope guarantees retain their premises and exclusions.
No Guardian act, guarantee admission, fresh Lean build/replay, compiled-HEAD or
native child-start attestation, general theorem, Issue completion or release
approval follows. External qlippy integration is maintainer-excluded; actual
Qleisli text/JSON results remain required.

The appended pending record freezes expectations and before-record hashes.
The capture driver requires a separately supplied after-code CLI digest and
verifies the selected CLI, native kernel and immutable baseline before and
after every call. It authors its own bounded command list; saved observation
commands remain data and are not replayed. It preserves any real after-code
failure, then separately registers actual observations without rewriting the
first pending record, sources, diagnostics, usage errors or metadata failure.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
