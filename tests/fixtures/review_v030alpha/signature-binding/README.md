# Exact function-signature attachment (#265)

The public `FunctionEvidence::check_binding` previously accepted only identity
and implementation/specification snapshots. `before.rs`, run against the fixed
`0605d716c2a79e2b6776476981c3e25cdfa1709b` source archive, retains a native-checked
three-bit flat tuple while the caller expects a nested pair of the same width.
The old method cannot express that expectation and reports `Ok(())`.

The new API takes the expected `BasisType` as its first argument and rejects
that attachment with `EvidenceMismatch`. `after.rs` checks the rejection and
the correct-tree positive control. The JSON records bind the actual commands,
probe sources, selected native executable and output files. The after record is
a local API observation during concurrent frontend development, not an exact
whole-commit release certificate. Both raw functions, source identity and native
receipt construction keep their existing checks and authority.

Rust regressions cover flat/nested three-bit trees, Unit versus a pair of Units,
and Bit versus a Unit/Bit pair, plus the existing identity/source/body changes.
The function-evidence, Meaning and source-snapshot suites passed 25 tests;
three existing maximum-depth/receipt stress tests remained ignored. No new
maximum-size case was generated or run.

The migrated generated Rust callers now pass each independently supplied binding
signature into the method. Their old separate signature comparisons are removed.
The full retained completion harness passed 146 native cases, 31 Rust comparisons
and 79 independent matrices (at most three semantic qubits). The branch harness
passed 51 native cases, 45 Rust comparisons and 69 exact operators (at most two
semantic qubits). Existing wide cases inspect metadata only. Results and exact
generated inputs are retained here; large JSON files use deterministic gzip.
`harness-files.json` binds compressed and original bytes.

An independent review checked all active call sites, the bounded exact tree
comparison and native-authority separation, with no remaining finding. The
old-signature `before.rs` is deliberately historical and is not a Cargo target.
This host attachment repair does not prove source preservation or discharge a
new constitutional guarantee.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
