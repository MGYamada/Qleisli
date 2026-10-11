# Selected VM22 source-baseline integration

This disk-safe follow-up invokes only the existing
`test_verification_baseline.source_comparisons(binary, False)` function.
At the observed revision, the script has no `--source-only` argument and its
`main()` always invokes Cargo. The driver does not call `main()`, finite/native
word comparisons, Cargo, a Lean build, or capture mode. It does not change
historical source snapshots or baseline artifacts.

`run.py` adds observation wrappers around subprocess execution and the existing
frozen-byte comparison. The actual source function and comparison result stay
unchanged. The wrapper only records argv, cwd, process exit, bounded streams,
and expected/actual artifact hashes; a mismatch would retain its actual bytes
and preserve the failure rather than delete or normalize fields.

The existing independent after CLI and audited native checker are bound by
SHA-256. The compiled Rust and embedded stdlib inputs match the independent
build archive, except the specifically reviewed module documentation changes
in `src/lib.rs` and `src/frontend/types.rs`. All non-documentation lines of
those two files were compared directly to the original compiled sources.
Relevant current source, test, script and frozen-artifact hashes were unchanged
between the beginning and end of this run. The later root-coordinated Rust
formatting is a separate integration delta; this record is not silently
rebound to it.

The selected function passed:

- Eight positive projects each passed source checking, produced the expected
  distribution, emitted the exact frozen QIRF bytes, and passed raw verification.
- All eight complete emitted artifacts are byte-identical to their VM22
  baselines. No field was erased or ignored. No mismatch file was needed.
- Four negative projects (`duplicate_owner`, `measured_owner`,
  `measurement_adjoint`, `dirty_auxiliary`) returned rejection diagnostics.
- All 36 CLI processes have actual command, exit and stream records.

`result.json` binds the full observations and explicitly does not claim that
the entire VM22 script passed. These are bounded source/IR regression checks,
not general source preservation or new guarantee admission.

The two repaired Rust tests were inspected without rebuilding:

- `finite_v0_type_shapes_and_zero_wire_ownership` now accepts ordinary
  `Bit -> Bit` identity and rejects `Bit -> Q<Bit>`, preserving the distinction
  between an ordinary value and a quantum owner. Its other exact-tree and
  zero-width ownership counterexamples remain.
- `generic_bodies_cannot_borrow_undeclared_access_from_concrete_providers`
  uses canonical `if 0` in its dead-branch example. Its expected `Capability`
  failure still tests the unchecked adjoint permission in an unused branch;
  no production capability check was changed.

Those two Rust targets still require their separately coordinated execution.
The successful source-baseline run is not a substitute for that execution.
