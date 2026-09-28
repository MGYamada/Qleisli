# Iterative QPE source regressions

[iterative_qpe.rs](../../iterative_qpe.rs) copies the example modules into a
temporary project and runs these clients against iterative and coherent QPE.
The harness changes only the imported `phase3` provider for that comparison.

- Eight `phase_t*` clients cover the exact 1/8 grid; `x_plus` and `x_minus`
  check a different eigenbasis and retention of the target.
- `identity_reference` checks coherence in a degenerate phase subspace.
- Nine `tilted_bell_*` clients measure X/Y/Z pairs after QPE on half a Bell
  state for U = H T. A Rust oracle directly computes the Fourier polynomial,
  independently of the compiled QFT and feedback recurrence.
- `faults` holds deliberate, type-correct replacements of the iterative
  module. These are semantic sensitivity tests, not failed authoring attempts.

Run `cargo test --test iterative_qpe`. This directory mixes independent clients
and intentionally faulty modules; it is not one executable source project.
