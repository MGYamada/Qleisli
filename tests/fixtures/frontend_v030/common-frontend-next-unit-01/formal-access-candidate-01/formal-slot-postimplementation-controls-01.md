# Formal-slot post-implementation controls 01

Prepared by `/root/isometry_cli_tests` as four additional integration tests in
`tests/sized_declarations.rs`. These are **unexecuted post-implementation
controls**, not the first forty before-code observations. No Rust test, CLI,
native checker, Cargo/Lean build, lint or artifact generator was executed while
preparing them. Root owns execution and must retain actual failures/results
separately. Existing sources, drivers, frozen packets and production files were
not edited by this preparation.

## Desired programs and actual consumers

The test file contains the exact desired ordinary `.qli` strings and fixed
bindings. Its hash is recorded in the companion subset map. Ordinary public
`main()->Unit{()}` stays valid while private unused generic declarations are
checked; no call or entry selection makes them disappear.

- `direct_formal_adjoint_and_controlled_slots_are_usable`: the provider-free
  direct inverse formal with only Adjoint(U) passes the finite public
  `check_project` and selected public `ParsedProgram::parse` routes. Finite
  control uses its existing qif spelling with only Controlled(U). The selected
  direct controlled spelling is explicitly expected to remain finite
  Unsupported at its complete expression, before formal judgment. Selected
  inverse/control entries bind the ordinary private `main::rotate` provider,
  `phase[1,3]`, then instantiate, elaborate, lower, request a fresh actual
  native check via the existing integration helper and execute with one
  reference qubit. All selected source bytes and the provider definition
  identity are retained by the proposal and asserted by the test.
- `private_unused_formals_cannot_borrow_adjoint_or_controlled_access`: only
  Apply(U) cannot authorize private unused direct inverse/control bodies.
  Direct Adjoint uses identical source through both public checkers. Finite
  Controlled uses qif, selected Controlled uses direct controlled application.
  The tests assert exact code/message and original failing access-use span.
- `selected_unused_dead_arms_and_zero_folds_check_both_missing_access_slots`:
  private unused inverse/control uses remain checked in the dead static arm
  and zero-iteration fold. These four bodies are selected-only; an earlier
  finite unsupported-profile refusal would not validate the access judgment.
- `duplicate_adjoint_and_controlled_slots_keep_each_profile_diagnostic`:
  identical unused generic declarations with repeated Adjoint or Controlled
  reject even when their bodies return the owner unchanged. Finite highlights
  the second target U with Capability/duplicate access constraint; selected
  highlights the second access keyword with access/duplicate operation access
  requirement. Exact source-derived positions are asserted, not normalized.

These expectations are source-inspection predictions until root runs the tests.
The scalar primitive phase_eighth is not substituted for T. Selected current
phase[j,k] is diag(1,exp(2*pi*i*j/2^k)); the finite t catalog and selected phase
catalog remain distinct. No primitive, profile, grammar or API is expanded.

## Independent bounded coefficient equations

The selected private provider is T = diag(1,exp(i*pi/4)). For inverse, odd basis
coefficients multiply by cos(pi/4)-i*sin(pi/4); even coefficients stay fixed.
For controlled-T, only basis index 3 changes by cos(pi/4)+i*sin(pi/4), with the
first owner on the low control axis and the second on the target axis. Each
formula is applied separately to both reference slices. Unequal real/imaginary
coefficients expose phase/order/reference errors; these expected values are
not read from producer normalization or artifact meanings. System sizes are
one/two qubits, plus one reference qubit, at most eight coefficients. Numerical
tolerance 1e-11 is a bounded regression comparison, not an EXACT obligation
replacement, arbitrary-input theorem or source-preservation proof.

## Validation boundary

Root should run the existing sized_declarations target using the fixed shared
target directory, on both coordinated Rust toolchains with the real selected
native checker. Formatter/build/Clippy output and any genuine failure must be
recorded by root; this record reports none as performed. The map is only an
inspected source/reference/helper subset, not compiled-HEAD or full closure.
The two admitted ordinary QLV1 guarantees and pending QS/PR/RS/EXACT are
unchanged. These controls give no #32/#317 close credit, release readiness or
new guarantee.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
