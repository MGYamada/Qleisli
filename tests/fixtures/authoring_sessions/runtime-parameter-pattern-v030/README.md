# Ordinary runtime parameter-pattern study

The first 18 informed sources were saved in `projects.json` before execution:
six desired parameter forms, nine counterexamples and three named-binder
controls. Three separately recorded let/fold wildcard contexts were added
before the first observation. `first-files.json` freezes those 21 complete
projects, their Qargo editions, context and session metadata. None of these
source bytes was repaired after a diagnostic.

The actual baseline uses the existing CLI with SHA-256
`74857d08147f27d919021c4eda54b0f7d7edeccba35fa2c17a1bdb19c57e05bd`.
`identity-before.json` links its prior Unit-pattern MSRV validation and source
manifest. The recorded implementation and embedded stdlib source hashes matched
the inspected working tree before observation. No executable was newly built
for this study; no whole source snapshot or binary was copied.

`observe-baseline.py` ran 39 small checks: 21 finite JSON checks and 18 explicit
sized checks. All six desired parameter sources reject in the existing parser.
The three finite named controls pass, as do the two selected sized named
controls. Ordinary wildcard `let` passes finite checking and rejects in the
existing sized projection. The other two added wildcard contexts reject. The
original stdout, stderr, return codes, argument vectors, input hashes and
executable hashes remain in `observations/`; unsuccessful cases were not
normalized into later expected diagnostics. Successful sized checks report
producer consistency, not source-meaning verification.

`followup-projects.json` separately preserves two closed named controls and two
additional ownership counterexamples requested during independent review. Their
six actual finite/sized checks are in `followup-summary.json`. The two controls
pass finite checking; the zero-fold quantum wildcard and nested quantum wildcard
reject. Three successful `emit-ir` calls retain the exact unchanged named-control
artifacts under `baseline-artifacts/`, including effectful Unit argument
evaluation. Their commands and artifact digests are in the corresponding
follow-up observations. Concurrent implementation edits may begin during these
follow-ups; the record binds the unchanged prior executable and inputs, without
asserting that it executed the changing working tree.

The later `validation-sources/` files are separately named, bounded integration
oracles saved before their Rust target ran. They extend the desired source matrix
with explicit call arity, static operation collision, two-argument ownership
ordering, source/provider identity, and controlled scalar phase. They do not
replace any first source or baseline diagnostic.

The independent Rust target `tests/runtime_parameter_patterns.rs` checks:

- one source parameter remains one exact input tree even when it binds several
  leaves, and duplicate names across parameter trees remain errors;
- ordinary Unit and classical leaves may copy/drop, while recursively quantum
  wildcard loss and zero-iteration fold loss reject;
- static substitutions and actual providers retain their declaration and source
  identities, and unused declarations are checked;
- native two-bit SWAP acts on every supplied coefficient with a two-dimensional
  reference, using an independently indexed expected permutation;
- effectful arguments retain actual Discard operations and left-to-right owner
  consumption, and controlled `Q<Unit>` phase has probability
  `(2 - sqrt(2))/4`, independently of the named-source comparator.

Sized ordinary classical entry lowering and product-basis limitations remain
separate from preparation. No arbitrary-reference theorem, general source
preservation, new native rule, guarantee discharge or maximum-size validation
is claimed. The study author ran no Cargo or Lean build. Implementation test
results are recorded by the integrating task separately from these original
baseline observations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
