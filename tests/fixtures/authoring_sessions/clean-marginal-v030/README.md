# Clean auxiliary, different live action

This informed two-qubit study preserves the complete original packet under
`first/`, including its pre-execution status and independent equations. The
canonical `attempt-01/` source/manifest bytes are identical copies. A separate
observer captured all six first checks/runs with unchanged source and binary
hashes; no source repair was made. Historical commands and the observer are
inert and must not be executed by CI.

Coherent uncompute checked and ran, reporting `(0,0)` with probability 1 and
retaining the tiny floating-point `(1,0)` residual in its original output.
Explicit reset also checked, but returned `(0,0)` and `(1,0)` with weights
approximately 1/2. Both auxiliaries are clean; the live actions differ.
Falsely declaring the reset helper Unitary failed both check and run with the
actual `effect` diagnostic: its body is Observe.

The CLI reports producer consistency and `source_preservation_verified=false`.
The existing executable identities are recorded, but are not attested builds
of the observed repository HEAD. These numerical observations do not prove
all-input cleanliness, the fixed-pure-state CPTP equivalence, exact source
correspondence, controlled access or quantitative Resource Safety. The observer
explicitly measures both remaining owners; it invents no release operation.

Fresh regression source is authored separately in
`tests/source_ir_correspondence.rs`; it does not execute this retained history.
Issue #157 remains open for its full acceptance criteria.
