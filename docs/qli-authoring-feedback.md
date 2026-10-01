# Current QLI authoring observations

This is an informed source-authoring account, not a measured model benchmark.
[Session procedure](../tests/fixtures/authoring_sessions/README.md) requires
complete first sources before checking, real diagnostics and revisions, and
independent semantic checks. Historical narratives belong in Git history;
source attempts, counterexamples and validation records remain with fixtures.
The [quick reference](qli-quick-reference.md) supplies copyable, CI-checked
current examples. Filesystem projects now require an enclosing `Qargo.toml`
selecting [edition 2026](language-editions.md).

## Finite corpus authoring

The [three-source corpus](../corpus/README.md) contains 42 finite translations,
14 each from the approved QuantumKatas, Qualtran and PennyLane sources.
The [0.2.3 session](../corpus/authoring/v023-small/session.json) adds odd-parity
preparation, Bell singlet, two constant predicates, RY and Ising ZZ at 1–3 qubits.
All six first source checks passed without repair. Known tuple, gate and rotation
workarounds and the existing driver template were available before authoring;
this cannot estimate unaided first-attempt success.

All complex entries are checked against independent coefficient/permutation
formulas. The singlet's Z/X order and ZZ's scalar leave ordinary probabilities
unchanged; RY and H agree on the zero-input preparation. Their deliberate
[type-correct faults](../corpus/semantic_faults/README.md) therefore require
nonzero inputs or coherent interference. Constant equality's wrong-endian fault
also leaves the zero-input quickstart unchanged. No new source syntax or library
API was needed. First attempts and earlier numerical reports stay intact.

## Shared source and measured QPE

The [sized source experiments](../corpus/sized/README.md) retain one definition
per component instead of width-specific algorithm copies. Register-tail
adapters avoided whole-register expansion for Xor/GHZ. Shared gradient calls
avoid duplicated QFT storage/checking, while repeated execution still incurs
its actual gate count. The [arithmetic source](../corpus/sized/qualtran_arithmetic/README.md)
uses transparent recursive controls, explicit owner groups and input restoration.
Its first missing-provider and work-budget diagnostics remain in the
[arithmetic session](../tests/fixtures/authoring_sessions/sized-arithmetic-v021/session.json).
Successful compaction did not relax the checker budget.

The [order/amplitude clients](../tests/fixtures/sized_clients/README.md) reuse
coherent QPE with operation forwarding. Provider identity must include nested
operations: an expected phase histogram alone can hide a wrong residual target.
The [source session](../tests/fixtures/authoring_sessions/sized-qpe-clients-v021/session.json)
and independent full-state checks preserve that obligation.

The [measured-QPE checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md)
now records the bounded source/CLI slice, explicit initialization/readout,
packed `CBits`, named independent provider requests, residual-reference maps,
execution and fresh-shot classical clients. Its initial missing `init_zero`
diagnostic is historical, not the current implemented state. Small named widths
pass; named (2,4) still exceeds the unchanged structural budget. General source,
native/decoder correspondence and full-profile migration remain open. Further
maximum-size runs are waived; they are not successful capacity checks.

## Current ergonomic obligations

| Authoring obligation | Evidence and current boundary |
| --- | --- |
| Explicit product trees and owner packaging | [Tuple contract](tuple-shapes.md), [type system](type-system.md) and [reshape first source](../tests/fixtures/authoring_sessions/reshape-v021/session.json). Flat and nested products are distinct. `split`/`join` and explicit adapters route owners; arithmetic width equality does not reorder axes or erase an owner. |
| Controlled access and operation identity | [Static-operation contract](static-operations.md) and [operation clients](../examples/operation_algorithms/README.md). Inverse/control/repetition require the declared capability and preserve scalar phase; mathematical unitarity alone does not supply an implementation. [Issue 45](https://github.com/MGYamada/Qleisli/issues/45) tracks the future capability calculus. |
| Exact rotation phase | [RX source](../corpus/pennylane_demos/rx_quarter/kernel.qli) and [ZZ source](../corpus/pennylane_demos/ising_zz_quarter2/kernel.qli). A case-local scalar helper remains necessary for RZ-derived rotations. [Issue 39](https://github.com/MGYamada/Qleisli/issues/39) tracks exact literals; no continuous-angle API is implied. |
| Total basis computation and unary meaning predicates | [Source fixtures](../tests/fixtures/qli_authoring/README.md). Product patterns work, but a multi-argument predicate cannot silently become a unary product contract. [Issue 25](https://github.com/MGYamada/Qleisli/issues/25) and [Issue 30](https://github.com/MGYamada/Qleisli/issues/30) track unresolved design. |
| Helpful diagnostics for generated source | [Parser prefix regressions](../tests/parser.rs), [repair regressions](../tests/repair_diagnostics.rs) and [review sources](../tests/fixtures/review_v021/README.md) cover truncated input, effect provenance and grouped imports. [Issue 95](https://github.com/MGYamada/Qleisli/issues/95) tracks lost size-error spans. |
| Evidence separate from source success | [Semantic faults](../corpus/semantic_faults/README.md), [protocol/reference tests](../examples/protocols/README.md) and [measured-QPE checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md). A checked source or inverse round trip is not its intended algorithm equation. |

These obligations select bounded experiments under the
[program-first method](design-philosophy.md#start-with-the-quantum-programs-we-want-to-write).
Removing punctuation, sharing source or proving a checker component must be
reported separately from eliminating a user obligation. Record unresolved
friction in its GitHub Issue with concrete source, an obligation and a checking
experiment; no duplicate backlog record is required.

## Proof and tooling evidence

Proof-only work does not reduce manual source routing by itself. The
[generated rule inventory](rule-inventory.md), [kernel package](../lean-kernel/README.md)
and [formal obligations](formal-core.md) identify actual component definitions,
proof scopes and executable harnesses. Original first sources and diagnostics
remain under [Lean fixtures](../tests/fixtures/lean_kernel/README.md) and
[hierarchy fixtures](../tests/fixtures/hierarchical_ir/README.md).
Production Rust authority, disabled external schemas and the
[staged VM-22–VM-29 migration](verification-migration-v0.2.md) remain explicit.

[QLT design sources](../tests/fixtures/qlt_design/README.md) preserve future
mathematical tests and deliberate phase/reversal/domain faults. Their subjects
can be checked today; QLT execution is deferred to v0.4.0 or later. Future
benchmarking must record model/version, context, untouched first source,
diagnostics, repairs and semantic outcome, without turning these informed
sessions or external timing reports into controlled measurements.
