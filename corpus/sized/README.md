# Shared sized corpus sources

These are executable **development experiments** using the
[Rust sized source API](../../src/frontend/sized.rs), existing hierarchical IR
and fresh native/finite reconstruction. The
[Python concrete producer](../../scripts/compile_sized_corpus.py) also serves
as a differential oracle. They reuse pinned inputs and are separate from the
42 finite corpus cases. The additive `qleisli sized` commands select a native
kernel explicitly. See the
[source contract](../../docs/sized-corpus-source.md).

| Source | Sizes exercised | Whole-space contract | License |
| --- | --- | --- | --- |
| [Xor](qualtran_xor/bitwise.qli) | 1, 2, 4, 8; local empty case 0 | `x,y` maps to `x,y xor x` with scalar +1, returning both owners. | Apache-2.0 |
| [GHZ](katas_ghz/prepare.qli) | 1, 2, 3, 8 | H on the low bit, then coherent controlled X on each other bit. The GHZ state requires all-zero input. | MIT |
| [QFT and inverse](qualtran_qft/README.md) | 1, 2, 3, 4, 8 | Positive Fourier matrix with explicit reversal; its inverse imports the same definition via `adjoint`. | Apache-2.0 |
| [Coherent QPE](qualtran_qpe/README.md) | (n,m)=(1,3),(2,4); further maximum-size checks deferred by user decision | Hadamards, phase-fixed controlled powers and the same inverse QFT; retains both quantum registers. Measured `CBits` API remains open. | Apache-2.0 |
| [AddK and Equals](qualtran_arithmetic/README.md) | n=1,2,3; local empty case 0 | Phase-fixed modular addition and equality into either initial target value, with coherent input restoration and no scratch. | Apache-2.0 |

Xor illustrates why basis data may control another register without cloning
unknown quantum states: on a superposition of x, it correlates the registers.
Each amplitude and phase is preserved, rather than measuring x. GHZ starts
with `H|0> = (|0>+|1>)/sqrt(2)`. Successive CNOTs correlate the remaining zero
bits with that coherent control. For arbitrary input `a+2t`, its output has
amplitude `1/sqrt(2)` at `2t` and `(-1)^a/sqrt(2)` at
`1+2*(t xor (2^(n-1)-1))`. Testing this full formula prevents zero-input tests
from hiding an incorrectly implemented unitary.

Each component reuses one algorithm definition at all widths. Static folds move the complete
carry; even temporary `Bits<0>` owners cannot be dropped or copied. Axis zero
is least significant. `Bit` and `Bits<1>` remain distinct. The producer can
normalize temporary routing, but emits explicit checked conversions at changed
IR boundaries. It tensors independent actions and keeps register tails, without
large dense contract matrices.

```sh
python3 scripts/compile_sized_corpus.py corpus/sized/qualtran_xor/bitwise.qli \
  --entry xor_into --size n=2 --output /tmp/xor2.json
python3 scripts/test_sized_corpus.py --small
cargo test --test sized_review_dialects -- --ignored --skip native
QLEISLI_HIERARCHY_KERNEL=lean-kernel/.lake/build/bin/qleisli-kernel \
  cargo test --test sized_review_dialects native -- --ignored
```

The first command emits **untrusted** IR only. The second independently checks
the actual artifacts, then compares complete basis columns and coherent
reference columns against separate algorithm formulas. The current
[small-system record](small-validation.json) follows the user's validation
scope. The earlier [full-width record](validation.json) retains source/artifact
hashes, verification work and execution gate counts: Xor width eight checked
all 65,536 inputs and GHZ width eight checked all 256. Those are historical
results, not newly required maximum-size checks.
Changed axes, phases, preparation or fanout remain valid circuits but fail the
algorithm oracle. Invalid ownership and a falsified leaf equation reject in
the independent verifier. These oracles issue no algorithm evidence and do not
prove general source preservation. Named contracts and production integration
remain required for full v0.2.1 acceptance.

Initially, direct framing exceeded the verifier allowance at Xor width four;
flattening all bits still exceeded it at width eight. Keeping tails as registers
and using explicit `Bits<1>` adapters admits width eight at 1,807,648 structural
units, below the unchanged two-million limit. GHZ width eight uses 1,385,780.
Each uses 536 exact units and eight one-bit leaves. No checker rule or proof
was changed for this experiment.

Sources and licenses remain those in the [main manifest](../manifest.json):

* Qualtran `Xor`, commit `8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`,
  [bitwise.py](../upstream/qualtran/qualtran__bloqs__arithmetic__bitwise.py).
  Preserve Google attribution and the [Apache license](../upstream/qualtran/LICENSE).
* QuantumKatas `GHZ_State_Reference`, commit
  `1a4740ff70ceffebde73d1434b2dedbe27643300`,
  [ReferenceImplementation.qs](../upstream/quantum_katas/Superposition__ReferenceImplementation.qs).
  Preserve Microsoft attribution and the [MIT notice](../upstream/quantum_katas/LICENSE).

The [authoring record](../../tests/fixtures/authoring_sessions/sized-corpus-v021/session.json)
retains first sources and actual failures. This is informed implementation work,
not a controlled model benchmark. No upstream material was downloaded.

The QFT continuation adds ordinary source module calls and adjoint, an
independently requested forward Fourier contract, inverse and shared-call
validation. Its [separate record](qft-validation.json) preserves execution
multiplicities as well as sharing; production integration remains open.

The [QPE record](qpe-validation.json) adds explicit transparent operation
providers and controlled repetitions, full-input/reference formulas, off-grid
phases and phase-sensitive provider changes. Remaining validation uses small
qubit systems by the 2026-09-30 user decision; the earlier (8,8) limit is retained
as history, without a claim of large-system capacity.

The [arithmetic record](arithmetic-validation.json) adds recursive coherent
controls, shared increment/complement/XOR components, 557 basis columns and
96 reference columns. Small-system source regression runs for
[Xor/GHZ](small-validation.json) and [QFT/inverse](qft-small-validation.json)
preserve the earlier full-width records. The
[local order/amplitude clients](../../tests/fixtures/sized_clients/README.md)
now reuse the same coherent QPE through operation forwarding, with full-input
and phase/reference diagnostics. These are Qleisli-authored integration fixtures,
not new upstream translations. Production integration, measured `CBits` clients
and complete classical-result paths remain open.
