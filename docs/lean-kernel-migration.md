# Rust frontend and Lean 4 verification kernel

Adopted Rust frontend/Lean kernel direction. Existing production acceptance remains Rust; [VM-22–29](verification-migration-v0.2.md) schedule implementation and S05-C1–C5 govern authority transfer. The Mathlib-free executable package is separate from [mathematical bridges](../lean/README.md).

## Architecture and authority

Keep the fixed [trust partition](../TRUST_BOUNDARY.md). Rust produces untrusted IR/evidence and retains parsing, diagnostics, transport, simulation and search. The Lean checker reconstructs complete data against independent requests; reference semantics import neither checker nor transport. Exact phase, ownership, effects, entry encodings and cleanup remain public obligations.

\[
\operatorname{verify}(p,C,\pi)=\mathrm{true}
\quad\Longrightarrow\quad \llbracket p\rrbracket\models C.
\]

## Algorithm contracts and pipeline consolidation review

Consolidate actual algorithm contracts around one checking boundary. A component proof or Rust success flag does not prove full source/IR/instrument binding. [R14](imaginary-v1/requirements.md#scaling-prerequisite-for-r14) and H1–H5 stay required for generalized hierarchy/source integration.

| Current path | Proposed consolidation duty; not yet implemented |
| --- | --- |
| Finite Rust | Published production compatibility profile during VM migration. |
| Hierarchical interchange / Rust sized | Converge on the shared source path and checked profile boundary. |
| Python sized compiler | Independent differential oracle, not production authority. |
| Research semantic kernel | Experimental oracle, not a second production checker. |
| Mathlib-free `lean-kernel/` | Executable generic acceptance and actual-definition proofs. |
| Mathlib `lean/` | Independent intended-meaning specifications and library/semantic bridges. |

## Pipeline migration with a stable IR verification boundary

Migrate passes in sequence from backend or frontend while independently checking each boundary IR. Extend the verified downstream segment only with proofs of actual transforms or independent translation validation. Record boundary IR, direction, coverage and transitional assumptions. Remaining Rust passes still produce untrusted output; moving code changes no trust partition.

```text
Rust upstream + pass P -> IR check -> verified Lean downstream
Rust upstream -> earlier IR check -> proved Lean P -> verified Lean downstream
```

The [VM-25 pure component](../tests/fixtures/verification_v025/README.md) moves
ownership/effect checking and bounded extraction before VM-24's finite-circuit
boundary. Lean receives original raw operations and retained body pairs; Rust
decisions/extracted circuits are not premises. [The completed VM-25 profile](../tests/fixtures/verification_v025/completion/README.md)
proves actual extraction against an independent original-operation trace and
complex action for all eleven pure constructors and final output order. It also
proves original compute/use/compute cleanup for arbitrary correlated inputs,
with protected coefficient evaluation that does not construct an auxiliary-space
matrix, and binds fresh function graphs to retained inputs and source identities.
Observing raw IR, hierarchy and production integration remain VM-26–VM-29;
Rust retains production authority.

## External search and the LeafRealizer checker

Apply the de Bruijn criterion per pass. Rotation-synthesis norm-equation search may be external and untrusted; the future Lean LeafRealizer must bind actual circuit/witnesses to an independent operation, gate/domain/interface/error request. A solved auxiliary equation alone proves no circuit realization. Search exhaustion is not impossibility. Certified approximation uses its declared metric/reference/composition bound and never substitutes for exact cleanup. LeafRealizer is not a current API.

## Backend execution must match kernel definitions

By v1 implement a substantive proved Lean backend, including correctness-critical transformations, realization checking and emission. Ban unsafe def, implemented_by, extern and partial def in project executable code. Source/import checks and compiled declaration metadata by origin must cover private/unreachable/generated helpers; axiom allowlists alone miss runtime replacements. Separate development Audit metaprogramming from runtime closure. Any future backend package must inherit these gates before integration.

| Forbidden construct | Why the backend policy rejects it | Compiled audit check |
| --- | --- | --- |
| `unsafe def` | Bypasses Lean's safe-definition discipline. | `ConstantInfo.isUnsafe` |
| `@[implemented_by]` | Substitutes a runtime implementation for the definition seen by the logical kernel. | `Compiler.getImplementedBy?` |
| `@[extern]` | Supplies an external implementation outside the checked Lean definition. | `getExternAttrData?` |
| `partial def` | Does not expose its recursive implementation as a total definition whose execution is covered by the intended theorem. | `ConstantInfo.isPartial` |

## Staged migration

K0–K4 are integration boundaries alongside M0–M5, not release deadlines or permission for public breaks. VM-22–29 brings K1/K2 implementation earlier; v0.3 types, v0.4 review preparation, v0.5 Soundness/authority and later PR/RS preservation retain their gates. Preserve Rust-only installation/APIs in compatible PATCH.

| Stage and intended boundary | Implementation | Gate before advancing |
| --- | --- | --- |
| **K0 / shipped 0.2.0 foundation, 0.2.2 inventory** | Reuse the separate Mathlib-free package, actual component theorems, experimental protocols, Rust launcher and audits. VM-22 inventories every existing acceptance path and fixes the next boundary contracts. | Shipped components remain reproducible. New M2 rules stay disabled until actual-checker proofs, binding and H1–H5 pass; hierarchy closure is assigned to VM-27, not inferred from K0 or the 0.2.2 version. |
| **K1 / 0.2.3–0.2.4: exact meanings and contracts** | VM-23/24 migrate canonical exact scalars, bounded matrices/leaves, contract equations and evidence reconstruction, with separate complex interpretation proofs over the same definitions. | Equality and operations agree with interpretation; phase/type/axis/source mutations reject. Preserve public arithmetic/capacity failure behavior and aggregate work limits. Raw-program evidence also requires K2 extraction. |
| **K2 / 0.2.5–0.2.9: complete checking and dual integration** | VM-25/26 migrate pure/observing raw IR, ownership, effects, SSA, complete phi/frames and cleanup. VM-27 closes supported hierarchy/finite/root obligations; VM-28/29 integrate and audit the complete opt-in dual path. | Individual-rule proofs cover every migrated variant with no substitute Rust-checker premise. Both checkers receive the same immutable artifact/request; either failure or disagreement rejects that path. Complete native/adversarial/platform checks and record remaining full-theorem/review obligations for S05. Preserve compatible Rust-only installation and APIs in 0.2.x. |
| **K3 / 0.5.0: Qleisli Soundness Theorem and production authority** | Prove the named theorem for the complete declared production IR profile, integrating K1/K2 results. Transfer acceptance to Lean after fresh serialized reconstruction; Rust becomes a producer/oracle. Prepare the community development foundation. | Complete [S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050), including independent review, proof reproduction, full coverage and artifact binding. Package the audited kernel on supported platforms; validate failures, parity and capacity migration. No unproved Rust-checker premise or silent fallback. |
| **K4 / 0.6.0 onward, through v1: translations, realizability and resource preservation** | Validate Rust source lowering; implement correctness-critical backend lowering, optimization, gate-realization checking and emission in Lean with proofs about those actual definitions; retain external synthesis search behind the proved `LeafRealizer` checker. Derive CPTP semantics from soundness, construct its isometric dilation and synthesize it for the target profile. Retire duplicated Rust acceptance code through versioned migration, with broader contributors and reviewers. | Preserve S05-C1–C5 and complete [PR-C1–C4](release-milestones.md#physical-realizability-theorem-v1) and [RS-C1–C5](release-milestones.md#resource-safety-theorem-v1) by v1 alongside V1-C1–C5. Bind emitted artifacts to checked meanings and resource contracts under explicit cost models; distinguish exact synthesis, certified approximation and device assumptions. Retain reproducible audits, native compiler/runtime assumptions, diagnostics and migrations. |

## First executable slice

The initial phase256 word profile proves cyclic X/phase normalization and actual acceptance against separate summaries. Both phase entries remain, including global phase. It is not full IR/ownership/instrument or native/compiler/source soundness. Later layout/DAG/phase/hierarchy/finite/QPE components have explicit narrower scope in [kernel README](../lean-kernel/README.md) and [rule inventory](rule-inventory.md).

| Contract | Implementation/proof status | Adoption boundary |
| --- | --- | --- |
| Valid word and canonical summaries | `wordValid_iff`, `verify_conditions`, `normalize_valid` proved. At most 4096 gates; phases in 0..255. | Experimental `phase256-word-v1`; not a general circuit format. |
| Normalized meaning equals execution | `normalize_correct` proved for every word, bit and initial natural phase. | Cyclic phase semantics only; complex interpretation bridge pending. |
| Actual acceptance implies requested action | `verify_sound` proved for `verify word claimed expected`; both the computed claim and separate expected summary must match. | Does not prove transport parsing, native compilation, source adequacy or full quantum soundness. |
| Native transport and Rust launch | Bounded parser/process adapter with independent positive, mutation and failure tests. | No `VerifiedProgram`, QIRF receipt or standard-library API is issued. |

### Experimental wire contract

Exactly two file paths: artifact and independent requirement. Canonical printable ASCII plus LF only, single ASCII spaces, unsigned decimal without leading zeros, final LF required; no CR/tab/BOM/NUL/extra fields/lines. Flip 0/1, phases 0..255, count 0..4096 matching every gate. Each input <=65536 bytes, numeric tokens <=4 digits, at most one excess byte read before UTF-8 decoding. Exit 0 accepted; 1 rejected/syntax/limit/io with artifact/requirement/verification stage; 2 usage. Canonical JSON/exit agreement, bounded output and five-second Rust child timeout are checked with no fallback. This experimental protocol is separate from QIRF and hierarchy.

```text
qleisli.phase-word 1 phase256-word-v1
Bit->Bit
claim 0 0 32
2
phase 16
phase 16
```

```text
qleisli.phase-word 1 phase256-word-v1
Bit->Bit
expect 0 0 32
```

```json
{"format":"qleisli.kernel-result","version":1,"profile":"phase256-word-v1","accepted":true,"code":"accepted","stage":"verification"}
```

## Audit and remaining trust

Run source policy, compiled Audit, reductions, fresh leanchecker replay and independent native comparisons. Project axioms/noncomputable/unsafe/partial/extern/implemented_by/native_decide/proof holes reject; only propext, Classical.choice and Quot.sound are permitted transitive logical axioms. Lean code generation, compiler/runtime/standard primitives, OS I/O and decoder/adapter correspondence remain explicit assumptions. Audit tests catch generated helpers; finite tests do not prove native compilation or complete source preservation.
