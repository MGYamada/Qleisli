# Rust frontend and Lean 4 verification kernel

Adopted Rust frontend/Lean kernel direction. Existing production acceptance remains Rust; [VM-22–29](verification-migration-v0.2.md) schedule implementation and S05-C1–C5 govern authority transfer. The Mathlib-free executable package is separate from [mathematical bridges](../lean/README.md).

## Architecture and authority

Keep the fixed [trust partition](../TRUST_BOUNDARY.md). Rust produces untrusted IR/evidence and retains parsing, diagnostics, transport, simulation and search. The Lean checker reconstructs complete data against independent requests; reference semantics import neither checker nor transport. Exact phase, ownership, effects, entry encodings and cleanup remain public obligations.

\[
\operatorname{verify}(p,C,\pi)=\mathrm{true}
\quad\Longrightarrow\quad \llbracket p\rrbracket\models C.
\]

## Algorithm contracts and pipeline consolidation review

Finite Rust remains production-compatible; hierarchy/Rust sized source aim at one
independently checked boundary. Python sized/research kernels remain differential
oracles, lean-kernel the Mathlib-free executable checker, lean the independent intended
semantics. R14/H1–H5, source/IR/instrument binding and actual-definition proofs remain
separate gates; a component proof or Rust success flag is insufficient.


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
[VM-26](../tests/fixtures/verification_v026/README.md) extends this boundary to
observation, SSA/phis, retained branch-functions and matrix-free CP/TNI/TP
against original complex actions. VM-27–29 remain open; Rust is authoritative.

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

| Stage | Boundary and advancement gate |
| --- | --- |
| K0 | Shipped seed and VM-22 inventory; reproduce components, keep new M2 rules disabled pending actual proofs/binding/H1–H5. |
| K1 | VM-23/24 exact scalars/equations/reconstruction; prove interpretation, preserve phase/type/axes/source binding, failures/capacities/work. Raw extraction also needs K2. |
| K2 | VM-25–29 pure/observing raw IR, hierarchy/root closure and selected dual integration. Prove every migrated variant with no Rust-checker substitute; immutable common inputs, either rejection/disagreement fails, native/adversarial/platform validation and coverage audit. |
| K3 | v0.5 complete production [Soundness S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050), independent review/reproduction/artifact binding, supported audited packaging, explicit compatible migration; only then transfer authority, with no fallback. |
| K4 | v0.6 onward through v1 actual source/backend lowering/optimization/realization/emission proofs, CPTP dilation, target synthesis and [PR/RS gates](release-milestones.md). Preserve meaning/resource contracts under declared cost models, exact/approximate/device distinctions and runtime assumptions. Retire duplicated acceptance only through versioned migration. |


## First executable slice

The initial phase256 word profile proves cyclic X/phase normalization and actual acceptance against separate summaries. Both phase entries remain, including global phase. It is not full IR/ownership/instrument or native/compiler/source soundness. Later layout/DAG/phase/hierarchy/finite/QPE components have explicit narrower scope in [kernel README](../lean-kernel/README.md) and [rule inventory](rule-inventory.md).

The seed proves wordValid_iff/verify_conditions/normalize_valid, normalize_correct
for cyclic phase execution and verify_sound for both computed claim and independent
expectation. It proves neither complex/full-IR semantics, ownership/instruments,
source adequacy nor native/decoder correspondence, and issues no VerifiedProgram or
QIRF/std receipt. [Kernel README](../lean-kernel/README.md) records component scopes.


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
