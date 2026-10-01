# Implementation boundaries and maintenance

Map of current finite implementation, not an acceptance or compiler-correctness theorem. [Language](language-spec.md), [trust partition](../TRUST_BOUNDARY.md) and [pipeline policy](lean-kernel-migration.md) are authoritative. Experimental research/hierarchy paths retain their own gates.

## Responsibilities and dependency direction

Raw IR/evidence is untrusted. The independent verifier constructs private immutable VerifiedProgram; any raw mutation requires checking again. Simulation consumes accepted IR but its numerical outputs are not an equality oracle. Frontend flattening and the independent function extractor stay separate. Convenience belongs outside acceptance; runtime sharing is not trusted-core reduction.

| Component | Responsibility | Dependency boundary |
| --- | --- | --- |
| [IR](../src/ir.rs) | Raw program data, ownership IDs, effects, and certificates | Independent of source syntax, the frontend, and execution. Raw data is untrusted. |
| [Verifier](../src/verify.rs) | Validate raw IR and construct `VerifiedProgram` | Depends on IR, not frontend acceptance or simulator results. |
| [Semantic contracts](../src/contract/mod.rs) | Check exact circuit/encoding equations and compose immutable evidence | Uses sealed circuit validation and bounded exact arithmetic, never frontend acceptance or numerical simulation. Raw `CertifiedCompute` invokes this independent boundary. |
| [Function evidence](../src/contract/function.rs) | Independently extract and compare verified raw functions, retaining their complete binding | Does not call frontend flattening. Opaque checked dependencies carry a cached exact meaning and are shared in final IR under transforms. |
| [Frontend](../src/frontend/mod.rs) | Parse and resolve source; check declarations and lower to raw IR | Uses IR and the independent verifier. Source-only obligations, such as declared effects and exact type trees, stay here. |
| [Source documentation](../src/frontend/documentation.rs) | Attach comment metadata to parsed items and render Markdown | Uses lexical spans and syntax only. Keeps the public AST shape unchanged; has no dependency on evidence issuance or the verifier and cannot grant acceptance. |
| [Simulator](../src/sim.rs) | Numerically interpret a closed `VerifiedProgram` | Uses IR and the verified wrapper, not the source checker. Enforces its own execution limits. |
| [Host utilities](../src/host.rs) and [CLI](../src/bin/qleisli.rs) | Classical postprocessing and user-facing orchestration | Keep host I/O and algorithm-specific success conditions outside the verification core. |
| [Lean development](../lean/README.md) | Check the recorded ownership and matrix lemmas | Its model and theorem scope are recorded separately from Rust acceptance. |

```text
source root -> frontend -> RawProgram -> verify -> VerifiedProgram -> simulator
handwritten or externally generated RawProgram -----^
```

## Checked lowering

Lowering evaluates once in source order and preserves ownership, classical values, work charges, locations, declared effects and fresh IDs. Callee lexical scope excludes caller bindings while the register store retains caller/pending owners. Branch restoration never rewinds global freshness; complete phi includes Q<Unit>. Certified bodies mask outer resources and retain actual/independent logical circuits; source hashes prove binding, not source adequacy.

| Module | Responsibility | Invariants to preserve |
| --- | --- | --- |
| [Values](../src/frontend/compile/lower/value.rs) | Mixed values, lexical environments, slots, and register metadata | `Q<Unit>` still owns a slot. A consumed binding remains as a tombstone until scope exit and continues to hide function names. Register ownership does not imply a product state. |
| [Scope projection](../src/frontend/compile/lower/scope.rs) | Reject leaked local owners and restore entry bindings using snapshots and rebound names | Value equality alone is insufficient for binder identity. The [refinement contract](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/lowering-state-refinement.md) and Lean lookup model preserve the entry domain and current quantum footprint on success. |
| [Branches](../src/frontend/compile/lower/branch.rs) | Branch snapshots and complete result/frame phi merging | Match returned resources by result position and every remaining frame resource by slot. Include suspended callers and pending arguments. Keep ID allocation fresh across both arms. |
| [Primitives](../src/frontend/compile/lower/primitives.rs) | Sealed signatures, ownership transitions, effects, and emitted raw operations | Observation consumes or replaces ownership explicitly; emitted operations still pass independent verification. |

## Traceability and verification

Use actual source/module/test references, independent analytic expectations and source/status inventories. Link checks establish existence only; retain separate paper-model, Lean component, native comparison and complete-implementation claims. Split modules for real responsibilities/interfaces, not length alone.
