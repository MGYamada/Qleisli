# Current QLI authoring observations

Informed source authoring, not a measured model benchmark. The [session procedure](../tests/fixtures/authoring_sessions/README.md)
requires untouched complete first sources before checks, real diagnostics/revisions
and independent semantic outcomes. [Quick reference](qli-quick-reference.md) is
copyable and CI-checked; filesystem trees explicitly select edition 2026.

## Finite corpus authoring

[Corpus](../corpus/README.md) now has 60 finite translations, 20 per approved source.
The [0.2.6 session](../corpus/authoring/v026-small/README.md) adds phased uniform/graph
states, phase-fixed and zero-control reflections, mixed noncommuting rotations and
negative ZZ evolution. Four first checks pass; two reflection sources initially
reverse repeat_static's count/operation arguments. Actual diagnostics and corrected
snapshots are retained; all six pass after repair. Independent full-complex checks
pass 164 new probes; six valid-source faults expose phase/sign/edge/order errors.
[Full replay](../corpus/validation-v0.2.6.json) passes 13,547 probes and detects 36 faults.
Known syntax/oracles were available; do not infer unaided model performance.
Historical sessions/results remain beside their sources, not repeated here.

## Shared source and measured QPE

[Sized corpus](../corpus/sized/README.md) shares actual register-tail, QFT, QPE and
arithmetic definitions. Sharing saves storage/checking, not repeated execution cost.
[Measured checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md)
retains preparation/readout, packed CBits, independent named provider requests,
residual/reference maps, shots and classical clients. Small named widths pass;
(2,4) still exceeds unchanged structural work. Further maximum runs are waived,
not successful capacity claims. Source/native/decoder/full-profile gates remain open.

## Current ergonomic obligations

Exact tuple/owner packaging and explicit reshape remain author obligations
([types](type-system.md), [first reshape source](../tests/fixtures/authoring_sessions/reshape-v021/session.json)).
Control/inverse access and full nested provider identity need separate capabilities
([#45](https://github.com/MGYamada/Qleisli/issues/45)); scalar-completed rotations still
need explicit phase/order ([#39](https://github.com/MGYamada/Qleisli/issues/39)).
Total predicates do not implicitly turn multiple parameters into a unary product
([#25](https://github.com/MGYamada/Qleisli/issues/25), [#30](https://github.com/MGYamada/Qleisli/issues/30)).
Size-error spans remain [#95](https://github.com/MGYamada/Qleisli/issues/95).
Checked syntax, inverse round trips or phase histograms do not establish intended
algorithm/reference instruments; [faults](../corpus/semantic_faults/README.md) test this.
Record source/design evidence, the obligation to remove and checking experiment in
its Issue, with no duplicate backlog. Proof-only work does not remove source routing.

## Proof and tooling evidence

[Ledger](rule-inventory.md), [formal core](formal-core.md) and [kernel](../lean-kernel/README.md)
record bounded component scopes. Rust remains authoritative, schemas disabled,
[VM-26 component](../tests/fixtures/verification_v026/README.md) checked; wider gates pending.
[Observing-source replay](../tests/fixtures/authoring_sessions/raw-observing-v026/session.json)
records late metadata honestly. [QLT source/faults](../tests/fixtures/qlt_design/README.md) remain future
v0.4+ tooling. Controlled benchmarks must record model/version/context, untouched
first source, diagnostics, repairs and semantics separately from these informed studies.
