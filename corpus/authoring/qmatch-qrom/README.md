# Issue #521 authoring record

This is an informed translation using the current Reference, the frozen approved
Qualtran QROM source, issue #521 and its linked #195 audit. It is not a blind
authoring benchmark. `attempt-01` preserves the complete first positive source
from this session; `first-faults` preserves the two first semantic mutants.
Subsequent attempts, if necessary, retain separate sources and actual diagnostics.
`session.json` binds the current source to the observed attempt.

`prior-audit.json` retains the exact retrieved issue body and audit comment,
including the three historical source hashes, reported parser diagnostics and
the repaired check result. The earlier study's actual source files and complete
logs were not present at the paths available in this checkout. They have not
been reconstructed or relabeled as this session's originals. Preservation of
those external-only bytes remains an outstanding provenance item; the recorded
hashes and reports alone do not replace them.

The new kernel uses actual qmatch syntax and `put_bit`/`take_bit`, explicitly
consuming the empty remainder. Its contract is a full phase-fixed 16-by-16 matrix,
not merely the zero-input closed driver's result. The deliberately wrong sources
remain valid programs: rejection concerns their independent requested QROM
meaning, not their syntax, ownership or unitarity.

The current change follows QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01.
It changes no acceptance rule, trusted definition, production limit, protected
ownership/scope guarantee, or proof status. The initial constitutional identity
check passed. No previously reviewed base was supplied for constitutional
continuity checking. General source preservation remains unproved.

[Local validation](validation/summary.json) records the performed and skipped
checks, exact source/accepted-IR identities and local binary identities. The
adjacent logs retain the normal/MSRV exact-regression results and native audit.
They are observations from the recorded base, not stored acceptance receipts,
native binary attestation, hosted CI results or a source-preservation proof.
