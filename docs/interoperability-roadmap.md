# Interoperability direction and acceptance debt

[M1.1-A](interop-m1.1.md) ships bounded OpenQASM3 input/output, QIR2 Base text output,
structured CLI/Python and optional LLVM-backed input. Full adaptive coverage and
compiler-free bundled wheels remain open; current wheel needs a separate Rust executable.
Target one tested install per Python/OS/architecture and fresh notebook use without
credentials/source rewriting. Package/platform evidence is distinct from format coverage.

## Compiler layers and translation obligations

Foreign builders/importers and .qli produce untrusted IR; independent verification
precedes target-capability lowering and execution/export. Python orchestrates; LLVM/
MLIR supplies no Qleisli semantics. [Lean migration](lean-kernel-migration.md) retains
Rust authority until gates pass. Required checker absence/unsupported input rejects.
Every transform must preserve operator/instrument and rebind evidence or invalidate/
recheck it; valid output alone does not establish original meaning. Preserve phase,
full types/ordered axes, ownership, encodings and exact cleanup.

Do not execute foreign externs/calibrations/LLVM while reading. Validate pinned gate/
QIS definitions, reject unknown/redefinitions, bound traversal before allocation.
Physical IDs are not logical owners; no aliases or desired outputs infer ownership,
types or requests. Scalar Rz/phase differences matter under control; decimal rounding
is not exact evidence. Domains, approximation and noise require separate contracts.
Retain initialization, result order, reset and hidden outcomes; terminal disposal is
Observe. Future reuse must reconstruct fresh postmeasurement state/owner and whole
reference instrument, not revive tokens or unconditionally replace with zero.
Dynamic allocation/unbounded loops/arbitrary externs/pulse timing and unsupported
capabilities reject explicitly. Open outputs/adaptive extensions need new contracts.

## IR reduction and the trusted boundary

Convenience belongs in [untrusted desugaring](terminology.md#desugaring-layer), with
no new primitive/rule. Visitor/tests are not frontend producers. Current finite
constructors retain QIRF support; public removal/reduced capacities requires MINOR.

| Vocabulary | Current producer and disposition |
| --- | --- |
| Gate/Cnot/Toffoli | [Primitive lowering](../src/frontend/compile/lower/primitives.rs) emits them; verifier/extractor/simulator accept. Future shared-unitary desugaring must preserve distinct owners/order/locations/limits. |
| ApplyUnitary/CircuitStep | [Static lowering](../src/frontend/compile/lower/mod.rs) emits qif/inverse/repeat; M1.1 importer emits selected H/monomial subset. Existing shared controls/exact monomial/contract actions need no foreign-gate rule. |
| QuantumIf/UnitaryStep | No current source constructor; raw API/tests remain supported by independent verifier/extractor. [Private adapter](../src/ir/compat.rs) shares post-verification numerical execution with retained cost/polarity/phase; compatibility debt remains. |
| ComputeUseUncompute/ProtectedUse | Source emits empty targets and auxiliary Z/T only. Broader raw target/protected/phase/layout forms remain debt; do not expand for hypothetical importers. Cleanup migration needs checked evidence, not unitarity/name. |
| CertifiedCompute/Contract | [Certified](../src/frontend/compile/lower/certified.rs)/[function](../src/frontend/compile/lower/function_contract.rs)/[M1](../src/frontend/compile/operations.rs) producers retain exact body/logical/dependency equations; convenience removal requires another checker for all obligations. |
| Init/observe/structure/lift/classical/phis | Primitive/expression/[branch](../src/frontend/compile/lower/branch.rs) producers; M1.1 selected Init0/Join/Split/MeasureZ/Discard. Preserve resource/instrument/ordered frame obligations. |

A smaller core requires an explicit versioned old-to-new migration with independently
checked full types, empty owners, phase/effects/branches/cleanup/dependencies and
limits/diagnostics; reject malformed aliases rather than repair them. Prove or validate
original correspondence, migrate every consumer, then record removed acceptance rules.
Moving files/shared numerical code is no trust reduction. [VM plan](verification-migration-v0.2.md)
keeps raw APIs while changing checker implementation. General LiftBasis target synthesis
remains open; [#132](https://github.com/MGYamada/Qleisli/issues/132) targets v0.4 NCT search
behind exact table/clean-workspace/phase/layout checking. Same-wire parity obstruction
is not general non-realizability. Optional PyQIR/LLVM/wheel tooling needs explicit
version/platform/redistribution contracts; no implicit user LLVM build.
