# Interoperability: Python, OpenQASM 3 and QIR

Adopted direction; [M1.1-A](interop-m1.1.md) implements bounded OpenQASM3 input/output, QIR2 Base text output, structured CLI/Python orchestration and optional LLVM-backed QIR input. No source/checker/capacity change. Adaptive/full format coverage and bundled compiler-free wheels remain open; current Python wheel requires a separate Rust executable.

## Goal and user benefit

Bring existing circuits through the same independent checking boundary, then execute/export the declared supported subset. Target one install command per explicitly tested Python/OS/architecture, prebuilt wheels without user Rust/LLVM compilers, a fresh notebook with diagnostics/local execution and no credentials/rewrite. Record platform/package/install evidence; format coverage, capacities and device setup are separate.

## Compiler layers

Architecture below separates untrusted frontend IR, independent checking and capability/target lowering. Current finite RawProgram is the bridge; [hierarchy](hierarchical-ir-spec.md) preserves shared calls/repetition/meanings/encodings/evidence later. LLVM/MLIR alone supplies no such semantics; MLIR adoption requires separate feasibility/compatibility. Python orchestrates, not a new quantum semantics. Staged Lean migration leaves source/diagnostics/adapters/numerics outside acceptance; Rust remains authoritative. A required checker must reject unavailable/unsupported and bind the exact executed/exported bytes.

Transformations must preserve operator/instrument and rebind evidence, or invalidate/recheck; mere IR validity does not prove original meaning. Exact phase/ownership/encodings/cleanup cannot be stripped by LLVM metadata survival. Terminal exporter lacks general LiftBasis decomposition. [Issue132](https://github.com/MGYamada/Qleisli/issues/132) targets v0.4 untrusted NCT synthesis with exact table/clean-workspace/phase/layout validation; same-wire parity obstruction is not general realizability. Unsupported IR still rejects.

```text
.qli frontend     OpenQASM importer     QIR importer     Python circuit builder
       \                 |                  |                    /
                 untrusted typed IR and source locations
                                  |
                     independent IR/evidence checker
                                  |
                  checked semantic IR and transformation passes
                                  |
                   target capability and lowering checks
                     /                 |                 \
            reference execution     OpenQASM output     QIR output
```

## IR reduction and the trusted boundary

Convenience belongs in [untrusted desugaring](terminology.md#desugaring-layer), adding no primitive/rule. Preserve ownership/effects/full phase/ordered interfaces/cleanup; foreign angle spelling cannot justify exact rounding. [Domain note](coefficient-domains.md) requires separately bound exact/approximate/device contracts. Table distinguishes constructors from visitors/tests; raw-only support is compatibility debt, not desired targets.

N-ary source now retains immediate tuple fields/BasisType:: Tuple under [type contract](type-system.md); typed layout/call/phase components and QIRF decoder are experimental or transport producers, with no trust reduction. All frozen finite constructors retain QIRF support. [Private compatibility adapter](../src/ir/compat.rs) maps verified UnitaryStep to CircuitStep; simulator adds outer control/common execution, in-place monomial/scalar actions retain limits. Independent exact extractor stays separate. This removes duplicate numerical semantics only.

Core reduction needs a versioned smaller vocabulary and explicit old→new ownership/phase/effect/layout/limits/diagnostics migration. Independently check untrusted legacy adapter; reject malformed rather than repair aliases/indices/owners. Rebind evidence and prove/check original correspondence with full types, empty owners, branches, cleanup/dependencies, exact operators/reference/negative fixtures. Remove verifier cases only after consumer migration, record actual acceptance rules removed. Public removal/reduced capacities requires MINOR; moving files/deleting tests does not reduce trust. [VM plan](verification-migration-v0.2.md) preserves raw APIs while replacing implementation.

| Representation | Current production emitter / acceptance consumer | Reduction disposition |
| --- | --- | --- |
| `Gate`, `Cnot`, `Toffoli` | [Primitive lowering](../src/frontend/compile/lower/primitives.rs); raw verifier, exact extractor and simulator | Emitted today. Candidates for later desugaring into the shared unitary vocabulary; preserve separate owners, output ordering, source locations and limits. Do not remove them in a PATCH. |
| `ApplyUnitary` and `CircuitStep` | [Static lowering](../src/frontend/compile/lower/mod.rs), including source `qif`, inverse/control and repetition, plus [M1.1 OpenQASM lowering](../src/interop/profile.rs); raw verifier, exact circuit checker and simulator | Existing common finite unitary vocabulary: controls, Hadamard, exact monomial actions and retained contract calls. The internal compatibility adapter and M1.1-A importer use this vocabulary; the importer emits only the selected Hadamard/monomial subset. No foreign gate requires a new verifier rule. |
| `QuantumIf` and its `UnitaryStep` arms | No current source-lowering constructor; raw Rust callers/tests can supply them. Verifier, evidence preflight/extractor and simulator still accept them. The frontend function-contract size visitor only inspects them. | Explicit compatibility debt. First replace the dedicated numeric interpreter with an adapter to `CircuitStep`; then specify legacy desugaring and migrate this convenience variant out of the core in a MINOR. |
| `ComputeUseUncompute` / `ProtectedUse` | [Restricted source lowering](../src/frontend/compile/lower/mod.rs) emits an empty target list and only Z/T `ProtectedGate` on its single ancilla. Raw verifier/extractor/simulator also support target gates, controlled phase, source protection and broader layouts. | Emitted subset has a cleanup obligation; the larger raw-only vocabulary is additional debt. Do not expand it for hypothetical importers. Investigate migration to explicit circuits with checked cleanup evidence, without treating a name or unitarity as zero-return evidence. No equivalence or migration is implemented yet. |
| `CertifiedCompute` and retained `Contract` actions | [Certified lowering](../src/frontend/compile/lower/certified.rs) and [function contracts](../src/frontend/compile/lower/function_contract.rs), and [M1 operations](../src/frontend/compile/operations.rs) with the [meaning adapter](../src/contract/meaning.rs); independent evidence checks | Keep exact actual/logical binding and dependency checking. A convenience form may disappear only when these obligations are represented and checked elsewhere. |
| Preparation, observation, ownership structure, lifts, classical operations and branch phis | [Primitive](../src/frontend/compile/lower/primitives.rs), [expression](../src/frontend/compile/lower/mod.rs) and [branch](../src/frontend/compile/lower/branch.rs) lowering; M1.1-A emits Init0/Join/Split/MeasureZ/Discard; raw verifier and execution/extraction where applicable | Emitted today. Retain their resource, instrument and ordering obligations; external physical IDs or LLVM control flow alone do not establish them. |

## Initial implementation slices

Every shipped row needs English signature/format/limit/diagnostic/migration contract; [bounded current contract](interop-m1.1.md) governs actual support. Remaining rows are future requirements. PyO3/wheel tooling and optional PyQIR are candidates, outside default core; Python/LLVM versions/platforms/redistribution need review. No user LLVM build should be silently required.

| Slice | Initial scope and obligation removed | Evidence and acceptance boundary |
| --- | --- | --- |
| Python host binding | Wrap the existing Rust compiler, verifier and exhaustive reference executor with immutable checked handles and structured exceptions. Later expose X4 sampling/trials. Users need no Rust caller or CLI-output scraping. | Calls use the same Rust checks; no Python Boolean or unchecked constructor creates a verified handle. Distinguish a distribution from sampled shots. Test FFI ownership, error translation, limits and wheel installation. |
| OpenQASM 3 import/export | Start with fixed registers, a declared exact gate set and terminal measurements. Load an existing circuit rather than rewriting its gates in `.qli`. | Specify a versioned subset, standard-gate definitions, initialization, wire/result ordering and terminal disposal. Reconstruct ownership and verify every imported operation. Reject unsupported source with locations. |
| QIR Base import/export | Start with a declared Base Profile/QIS combination. Export first to establish target conventions, then import independently produced fixtures in the same slice. | Pin a QIR revision and compatible LLVM reader/writer versions; check profile flags, entry points, instruction/call signatures, resource IDs, QIS meanings and output records. LLVM verification and Qleisli verification are both needed. |
| Adaptive interoperability | Later support the selected finite measurement, reset, Boolean feedback and post-measurement reuse fragment. | Specify instrument-preserving resource translation and target capabilities first. Test entangled references and selected/unselected branch behavior. A bounded subset is not full Adaptive Profile or full OpenQASM 3 support. |

## Translation obligations

Treat foreign artifacts as untrusted raw input; never execute LLVM/extern/calibration while reading. Pin and validate gate/QIS declarations/definitions, reject unknown/redefined meanings; bound parsing/expansion/traversal before allocation. Track physical IDs separately from fresh logical owners; no alias creates ownership or infers type/encoding/request from desired output.

Terminal measurement avoids foreign reuse mismatch. Future reuse requires fresh conditional postmeasurement owner/state and reference instrument correspondence, never resurrect consumed token or always replace with zero; prepare |b> is only a separately checked candidate. Preserve scalar phase under controls/modifiers; Rz≠phase without correction, decimal rounding grants no exact evidence. Bind domain/profile/approximation explicitly. Preserve initialization/basis/output order/reset/hidden outcomes; terminal disposal is observing discard, never clean release. Open quantum outputs require their own interface.

Reject unsupported dynamic allocation, unbounded/data-dependent loops, arbitrary arithmetic/external calls, pulse/timing, or backend capability mismatch. Report separately IR validity/requested meaning/translation correspondence. Companion evidence must bind exact output and be checked; hashes only identify bytes and edited IR invalidates binding. QIRF means qleisli.finite-ir JSON, distinct from QIR Alliance LLVM IR with distinct names/version fields.

## Required evidence and scheduling

Finite Python/OpenQASM, then QIR Base, then independently specified adaptive instruments; none closes N/X/H/R14 gates. Require independent imports/target parsers, not just round trips. Cover Bell/reference correlations, controlled scalar, bit/result reversal, unknown gates/calls, wrong attributes/IDs, malformed/limit/stale evidence; adaptive adds reset/discard/conditional reuse/reference maps. Histograms alone prove no open phase/residual semantics. Python errors/results match Rust; fresh sampling and clean wheel install must be checked. Record local versus device execution. License/redistribution/MSRV1.85 review precedes dependencies; toolchain change needs compatibility decision.

## External semantic references

Primary target specifications below; pin actual revision/profile on implementation. QIR measured reuse obeys the instrument contract; M1.1-A OpenQASM is terminal3.0/3.1 with explicit initialization. [Producer inventory](#ir-reduction-and-the-trusted-boundary), actual modules/fixtures and [rule inventory](rule-inventory.md) carry current coverage, never production hierarchy/schema authority.

[QIR specification](https://github.com/qir-alliance/qir-spec), [Base](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Base_Profile.md), [Adaptive](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Adaptive_Profile.md); OpenQASM3.1 [instructions](https://openqasm.com/versions/3.1/language/insts.html), [modifiers/phase](https://openqasm.com/versions/3.1/language/gates.html).
