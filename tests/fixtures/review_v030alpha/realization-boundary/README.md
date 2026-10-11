# Realization boundary regression replay

This record re-runs existing small regressions while the 0.3.0 realization and
resource Reference is written. It introduces no target, synthesis algorithm,
maximum-size case or certification claim.

The source is commit `44e23e4d0a6302eff17f3b39c42b735fcee7583d`, isolated from
the subsequent common-type work. `validation.json` records the exact source
files, native binary, added test/example archive, actual commands, exits,
timings and output hashes. The baseline source/Cargo/stdlib files were not
edited. The selected native binary is the existing matching 0.3.0-alpha build.

The exact determinant regression passes for the existing four-bit C3X table
and the phase-fixed three-qubit Fourier operator, without reclassifying them
as non-unitary when same-wire synthesis is obstructed in the stated profile.
The existing independent export oracle then decodes the emitted terminal gates
and checks complete small-system complex columns, output axes and clean-zero
workspace. Original sources and prior validation records remain unchanged.

These are exact finite determinant checks and bounded numerical export checks,
respectively. They are not a general synthesis theorem, proof of the actual
exporter's preservation, optimal workspace result, or quantitative Resource
Safety certificate. They do not validate uncommitted shared-type changes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
