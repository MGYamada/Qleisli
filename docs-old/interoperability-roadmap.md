# Interoperability direction

Bounded OpenQASM3/QIR2 Base, structured CLI/Python and optional LLVM input are shipped. Frozen contract. Adaptive coverage and compiler-free bundled wheels remain open; current Python needs Rust executable. Target one tested install per Python/OS/architecture and fresh notebook use without credentials/rewriting. Platform evidence and format coverage differ.

Terminal export permits moving allocations that already precede observation to the
initial allocation block; an `init0` after the first measurement or discard is
unsupported, even for a fresh owner. This clarifies the frozen contract's
ambiguous “Fresh init” sentence ([#240](https://github.com/MGYamada/Qleisli/issues/240));
physical qubit IDs are never reused. It preserves the existing terminal profile.

## Compiler layers and translation obligations

Foreign builders/importers and QLI produce untrusted IR. Independently check before capability lowering/execution/export. Python/LLVM/MLIR add no semantics; required checker absence/unsupported input rejects. Each pass preserves operator/instrument and rebinds or invalidates evidence; accepted output alone proves no source preservation. Retain phase/types/axes/owners/encodings/cleanup, initialization/results/reset/hidden outcomes. Physical IDs are not logical owners. Terminal disposal is Observe; reuse requires a fresh postmeasurement owner and complete reference instrument.

Never execute externs/calibrations/LLVM while reading. Bound traversal before allocation; validate pinned gate/QIS meanings and reject unknown/redefined operations. Scalar Rz/phase distinctions survive control; decimal rounding is no exact evidence. Dynamic allocation, unbounded loops, arbitrary externs, pulses and unsupported capabilities reject. Adaptive/open outputs/domains/approximation/noise need separate contracts.

## IR reduction and the trusted boundary

Convenience desugars without new meanings/acceptance. Public raw forms/capacities remain supported until MINOR migration. Current source emits Gate/Cnot/Toffoli; static operations emit ApplyUnitary; QuantumIf remains raw-only with verified numerical adapter. Protected compute source emits empty targets and Z/T auxiliaries; broader raw forms remain compatibility debt, not a reason to expand source acceptance. Certified/function/M1 producers retain exact body/logical/dependency equations. Init/observation/structure/lift/classical/phi producers retain complete instrument/frame obligations.

Reduction requires versioned old→new correspondence covering types/empty owners/phase/effects/branches/cleanup/dependencies/limits/diagnostics, independent checks and migration of every consumer. Reject malformed aliases; moving files or sharing simulation does not reduce trust. [VM](../docs/verification-migration-v0.2.md) changes implementation while retaining raw APIs. General LiftBasis synthesis remains open; [#132](https://github.com/MGYamada/Qleisli/issues/132) targets v0.4 NCT search behind exact table/workspace/phase/layout checking. Same-wire parity obstructions prove no general impossibility. PyQIR/LLVM/wheels require explicit version/platform/redistribution contracts and no implicit user LLVM build.
