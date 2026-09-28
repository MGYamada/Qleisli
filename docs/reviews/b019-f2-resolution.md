# B019 F2: compatible source-snapshot sharing

Status: **implemented and locally validated in development version 0.1.9**,
2026-09-28. This resolves the repeated-retention defect recorded as
[A020-10](../v0.2.0-backlog.md#a020-10--source-snapshot-copies-exhaust-the-shared-lowering-budget).
It is a private representation and resource-accounting correction, with no new
source syntax, primitive meaning, verifier acceptance rule or public Rust field.
It does not by itself complete the other [B019 conditions](../v0x-roadmap.md#v019-acceptance-boundary).

## Defect and correction

Previously, every distinct static provider binding and every distinct
`apply_contract` pair copied the entire loaded source collection into a
`FunctionIdentity`. Each copy consumed the 1,000,000-unit lowering budget.
Unimported comments and bundled library text therefore multiplied the cost of
otherwise trivial reuse. The [original replay](b019-2026-09-28.json) passed with
40 providers and a 2,919-byte main, then failed after adding a 25,003-byte
comment-only module. Both configurations now pass with the same source,
command, accepted grammar and exact checking rules.

The compiler now retains one immutable `Arc<Vec<(String, String)>>` for the
whole loaded project. Both frontend consumers use this same snapshot. Sources
remain complete: local modules, unimported modules, comments and bundled
standard-library modules keep their exact module names, ordering and bytes.
There is no dependency-pruning heuristic, digest authority, mutable shared
source, or rereading of files after evidence is issued.

## Storage and accounting contract

1. The snapshot is allocated only when a provider or function contract first
   needs evidence. Before cloning, the compiler enforces the existing metadata
   bounds: at most 128 modules, names of at most 4,096 bytes, and at most
   1,048,576 combined source/name bytes. It also charges the full source-text
   byte count against the existing 1,000,000-unit lowering budget before the
   copy. Failure leaves no retained snapshot.
2. Every subsequent receipt receives an `Arc` clone, so the retained source
   text and its lowering charge occur once per compilation. Module-name
   storage is bounded by the metadata profile; it is not multiplied per pair.
   AST visits, descriptions, matrices, circuit steps and ordinary source
   expansion continue to consume their existing lowering charges.
3. Distinct `apply_contract` pairs still charge their own raw representation
   snapshots and implementation/specification names before copying those
   values. Provider raw programs continue to have their original lowering
   accounting and independently bounded exact-evidence preflight/checking;
   this correction does not introduce a new provider charge that could reduce
   previously supported capacity.
4. Each evidence construction still validates **all** metadata and charges
   its complete metadata byte count to that construction's exact-work budget.
   The exact checker still requires implementation/specification names plus
   source/module-name bytes to fit the existing 1 MiB identity profile. Its
   raw IR bounds, 10,000,000-unit exact budget, independent verification,
   extraction and exact equation check are unchanged. Sharing bytes in the
   frontend never establishes a semantic theorem.
5. Existing cache keys remain exact resolved implementation/specification or
   implementation/meaning keys, private to an immutable loaded project.
   Cache hits reuse issued evidence. A new compilation has a new snapshot and
   checks its dependencies again. Final IR owns the snapshot through its
   receipts and remains valid after the loaded project or source files vanish.

The initial snapshot is still finite. Adding comments can exhaust the
remaining initial retention/lowering budget; the correction removes
**multiplication by the number of receipts**, not all source-size limits.
The 256-specialization cap, six-bit operation interface, circuit/dependency
limits and all unrelated finite profiles remain unchanged.

## Public compatibility and inspection cost

`FunctionIdentity` remains publicly constructible with
`sources: Vec<(String, String)>`. `FunctionEvidence::check`, the meaning
constructor, `identity() -> &FunctionIdentity` and `check_binding` keep their
signatures and exact observable metadata. Publicly supplied owned identities
still follow the same validation path.

Frontend evidence stores a private shared identity. Its first explicit
`identity()` inspection materializes an owned compatibility view in a
`OnceLock`; subsequent inspections and clones of that evidence share the
view. This can allocate one additional identity-sized copy per **distinct
inspected receipt**, bounded by the original metadata profile. Normal
compilation, evidence cloning, debugging, binding checks and execution do not
materialize it. This tradeoff preserves the owned public API while removing
the compiler's unconditional copies. The Rust 1.85 toolchain remains supported.

`check_binding` compares names, complete source bytes and both raw programs
directly against the retained data without forcing that compatibility copy.
Changing a name, source byte, module list or raw dependency cannot reuse the
receipt merely because a cache key or mathematical meaning happens to match.

## Regression and validation record

The [source-snapshot integration tests](../../tests/source_snapshots.rs) are
curated regression experiments, not a model-authoring benchmark. They check:

| Experiment | Observed result |
| --- | --- |
| 100,000-byte main and 256 distinct one-gate providers | Accepted and executed; all 256 receipts retained. |
| The same program plus an unimported 25,003-byte comment module | Accepted with unchanged output. Complete source-text payload is 132,171 bytes including the current 7,168-byte bundled sources, instead of 107,168 before the addition. |
| 256 distinct `apply_contract` pairs, or 128 pairs mixed with 128 providers, with the same source padding | Accepted and executed. |
| 257 distinct operation specializations | Rejected by the unchanged 256-instance limit. |
| Edited transitive implementation dependency, through either provider binding or `apply_contract` | Recompilation rejects the false meaning; already checked programs retain their old immutable behavior after file removal. |
| Edited identity names, module names/list or exact source bytes | Existing receipts reject the changed binding. |

Five focused unit tests in the
[compiler](../../src/frontend/compile/mod.rs) and
[evidence checker](../../src/contract/function.rs) additionally measure the
storage/accounting mechanism and its boundaries. In the isolated retention
experiment, 256 handles share one 100,000-byte payload and one 100,000-unit
charge; adding 25,003 bytes produces one 125,003-byte payload and charge.
These figures isolate retention from other AST/raw work. At the exact
remaining-work boundary, the first copy succeeds and subsequent reuse spends
no source bytes; one fewer available unit rejects before allocation.
Over-count, overlong-name and combined metadata overflow also reject before
copying. Receipt clones share the same lazy inspection cache. Shared metadata
does not bypass exhausted exact work, malformed raw IR or a false scalar-phase
equation.

Local checks completed on 2026-09-28:

- Rust 1.98.1 and Rust 1.85.0: the five snapshot unit tests and 60 integration
  tests across `function_contracts`, `function_evidence`,
  `operation_parameters`, `repair_diagnostics` and `source_snapshots` passed.
- Rust 1.98.1: `cargo clippy --all-targets -- -D warnings` passed.
- The frozen original 40-provider replay passed both without and with the
  unrelated comment file, with JSON exit code zero and no diagnostics.
- An [independent trusted-boundary review](b019-trusted-audit.md) found no new
  blocking correctness or public-API issue in the sharing path.

This record establishes the scoped repair and regressions. The release record
must separately bind the final candidate to whole-tree checks, distribution
validation and any hosted CI result; no tag or publication follows merely
from these local tests.
