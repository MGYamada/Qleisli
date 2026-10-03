# Canonical reshape experiment

Prepared before implementation checking, 2026-09-29. See the
contract and adoption boundary.

1. Preserve a desired explicitly typed `.qli` first attempt and its actual
   compiler diagnostic. Do not describe the draft as an implemented API.
2. Implement a bounded single-owner helper on existing prefix-tree/port data,
   binding an independently required source and target. Erase only Unit and
   grouping constructors for the leaf comparison, never sized atoms.
3. Prove that accepted requests preserve low-axis-first encoded labels,
   physical axis order, ownership and arbitrary reference coefficients. The
   encoding theorem must use induction rather than finite label enumeration.
4. Check native execution against a recursive tree oracle, including malformed
   input, changed atoms, identical-type axis swaps, zero-width owners, limits
   and wrong independent endpoints. Keep first Lean source/diagnostics.
5. Keep production dispatch and schemas unchanged. A future producer must emit
   existing independently checked structural operations and pass source/API
   compatibility review before `reshape` becomes a public API.
