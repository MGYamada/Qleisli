# Implementation boundaries and maintenance

Status: **implementation structure and maintenance policy** (2026-09-26).
This is a map of the current finite implementation, not a new language
specification or a proof of compiler correctness. The [v0 specification](language-spec.md)
and [Stage 1 obligations](formal-core.md) remain authoritative for language
behavior and proof status.

The subsequent [symbolic-contract system design](symbolic-contract-architecture.md)
and [independent research package](../research/semantic-kernel/README.md) explore
composition without whole dense operators. They do not replace the production
path mapped below. Raw-IR binding in a research adapter and mathematical Lean
rule lemmas are separate from a proof of source/compiler adequacy.

The [2026-09-28 interoperability direction](interoperability-roadmap.md) proposes
Python bindings and QIR/OpenQASM import/export around this independent boundary.
Those adapters and their extension specifications remain pending; the current
component and execution map below describes implemented code only.

The adopted [pipeline migration policy](lean-kernel-migration.md#pipeline-migration-with-a-stable-ir-verification-boundary)
moves passes in sequence from either end while preserving an independent IR
check at the Rust/Lean boundary. A proved pass can extend the verified segment;
remaining Rust transformations still require validation before their output
enters that segment. This is a migration direction, not a change to the current
finite execution map or a claim that the backend is already verified.
[Candidate search remains external where appropriate](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker):
rotation synthesis can propose circuits and norm-equation witnesses to a
proved Lean `LeafRealizer` checker. That planned role does not yet expose an
API, and the oracle's implementation need not migrate to Lean. A substantive
Lean backend remains required; its [execution policy](lean-kernel-migration.md#backend-execution-must-match-kernel-definitions)
forbids unsafe/partial definitions and implemented-by/extern runtime replacement
through source and compiled-declaration CI, including generated helpers.

## Responsibilities and dependency direction

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

The execution path is:

```text
source root -> frontend -> RawProgram -> verify -> VerifiedProgram -> simulator
handwritten or externally generated RawProgram -----^
```

Keep `VerifiedProgram`'s fields private to the verifier. Consumers may inspect
its immutable raw program; constructing or changing raw IR requires verification
before execution. Future backend entry points should require the same checked
boundary and separately diagnose unsupported capabilities. There is no backend
implementation or hardware guarantee in this policy.

Share data representations when useful, but keep the verifier's acceptance
checks independent of frontend bookkeeping. Reusing the frontend's decision
would remove the second check. Numerical agreement on examples does not prove
either implementation correct.

The [small trusted-core boundary](design-philosophy.md#keep-the-trusted-core-small)
requires convenience features to stay in desugaring outside the checker.
**[Desugaring](terminology.md#desugaring-layer)** means meaning-preserving
translation of convenient representations into already specified core operations,
producing raw IR and proposed evidence for independent checks. It adds no new
primitive meaning or acceptance rule. Source typing and evidence checking remain
separate even when they share a frontend module. The current implementation has
no standalone universal desugaring module; the runtime adapter below acts after
verification and is not that producer layer.
Maintain the [constructor/emitter and compatibility-debt inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary),
especially raw variants not emitted by a production frontend. The private
[legacy unitary adapter](../src/ir/compat.rs) now routes verified `QuantumIf`
arms through the simulator's existing `CircuitStep` execution path. It does not
replace raw verification or the independent exact extractor; this runtime
consolidation is not a reduction of the evidence-acceptance trusted base.

The [coefficient-domain note](coefficient-domains.md) describes future
parameterization and exact/approximate/device contracts. Current exact scalars
and matrices remain concrete R8 types. Any future domain arithmetic, equality
or embedding used for evidence belongs to the reviewed trusted base; generic
type parameters must not open an arbitrary user-defined proof oracle.

## Checked lowering

The private [lowering module](../src/frontend/compile/lower/mod.rs) evaluates
expressions in source order, handles lexical scopes and calls, and constructs
IR. Its supporting modules have these responsibilities:

| Module | Responsibility | Invariants to preserve |
| --- | --- | --- |
| [Values](../src/frontend/compile/lower/value.rs) | Mixed values, lexical environments, slots, and register metadata | `Q<Unit>` still owns a slot. A consumed binding remains as a tombstone until scope exit and continues to hide function names. Register ownership does not imply a product state. |
| [Scope projection](../src/frontend/compile/lower/scope.rs) | Reject leaked local owners and restore entry bindings using snapshots and rebound names | Value equality alone is insufficient for binder identity. The [refinement contract](lowering-state-refinement.md) and Lean lookup model preserve the entry domain and current quantum footprint on success. |
| [Branches](../src/frontend/compile/lower/branch.rs) | Branch snapshots and complete result/frame phi merging | Match returned resources by result position and every remaining frame resource by slot. Include suspended callers and pending arguments. Keep ID allocation fresh across both arms. |
| [Primitives](../src/frontend/compile/lower/primitives.rs) | Sealed signatures, ownership transitions, effects, and emitted raw operations | Observation consumes or replaces ownership explicitly; emitted operations still pass independent verification. |

The complete register store and fresh ID supply belong to `Lowerer`. A callee's
lexical environment contains only its own bindings, while the register store
also contains caller and pending-argument resources. Branch snapshots restore
registers and effects, not the global ID counters. Preserve work-budget charges,
evaluation order, source locations, and declared-effect checks when moving code.

These modules are private implementation details within the existing crate.
The [certified-scope lowerer](../src/frontend/compile/lower/certified.rs)
constructs an isolated data/auxiliary body with all outer values masked.
It retains both physical and explicit logical circuits for independent
equation checking; it does not authorize cleanup merely by recognizing gates.
The [function-contract lowerer](../src/frontend/compile/lower/function_contract.rs)
resolves a fixed specification and implementation after input evaluation.
It reuses immutable evidence from the compiler's frozen source project;
source snapshots are provenance, not a proof of source/Rust adequacy.
The independent function extractor is intentionally separate from frontend
circuit flattening so the latter's output is not its own equality oracle.
Split further when a responsibility acquires a useful interface; file length
alone is not a reason to introduce another abstraction. Consider separate crates
when independent consumers or dependencies need an enforced package boundary.

## Traceability and verification

Maintain the existing [resource audit](source-resource-rules.md#8-implementation-audit-and-regression-evidence)
and [syntax coverage table](source-typing-rules.md#9-constructor-coverage-and-implementation-audit)
when a rule or implementation location changes. Link to the relevant rule,
implementation item, and finite acceptance/rejection evidence; preserve the
distinction between paper proofs, Lean results, tests, and open obligations.
The [checked reference convention](source-typing-rules.md#9-constructor-coverage-and-implementation-audit)
lets CI detect missing references. It checks existence, not whether a test
actually establishes a rule or whether a compiler transformation preserves meaning.

Shared [test support](../tests/common/mod.rs) handles temporary source projects
and cleanup. Keep analytical distributions, exact operators, and rejection
expectations independent of production algorithms so a common implementation
mistake cannot determine both the result and its expected value.

For Rust refactoring, run the affected regression suites, all Rust targets,
formatting, and Clippy. Run the documentation checker and its tests when changing
reference conventions or implementation paths. The existing [CI](../.github/workflows/ci.yml)
also builds Lean and audits its axioms; changing Rust organization alone does
not extend the scope of those proofs.
