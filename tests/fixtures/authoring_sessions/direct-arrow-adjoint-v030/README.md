# Direct general-arrow adjoint study

The unchanged first source applies an opaque `Op<(Unit,Bit) -> Bit>` through
`adjoint(U)(q)`. Its `Adjointable` requirement promises the reverse implementation:
the input is `Q<Bit>` and output is `Q<(Unit,Bit)>`. The common checker previously
forced equal ports for this direct form, although the equivalent static adjoint
passed through another operation parameter was already supported.

The observer initially wrote the wrong manifest key `schema`; that actual
project failure is retained in attempt-01. Attempt-02 changes only the key to
`schema-version` and preserves the genuine type rejection at `U`. Four appended
checks/runs use unchanged attempt-02 bytes: both output columns retain their
identity action, and hierarchy and Raw checks succeed. Native acceptance and
source-step checks do not establish general source preservation.

Regressions separately cover direct constructed adjoints, inverse eighth-root
phase with an untouched reference, Raw interference, missing access, wrong
port trees, a genuinely Isometric provider and a false nested Meaning. Initial
test failures from an unavailable selected `t` spelling and incorrect JSON
field assertions remain in temporary test logs; the test uses the existing
`phase[1,3]` and accounts for floating-point execution residue. No original
source, diagnostic or numerical output is rewritten.

Ordinary named runtime-group restrictions, finite general-arrow limitations,
rectangular Meaning work, #83/#46 and broader proof obligations remain open.
This is informed conformance work, not a blind authoring benchmark or a new
constitutional guarantee.
