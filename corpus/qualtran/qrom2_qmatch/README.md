# QROM with actual qmatch arms

This four-qubit translation reuses the approved Apache-2.0
[Qualtran QROM source](https://github.com/quantumlib/Qualtran/blob/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3/qualtran/bloqs/data_loading/qrom.py),
its [frozen original](../../upstream/qualtran/qualtran__bloqs__data_loading__qrom.py),
[license](../../upstream/qualtran/LICENSE) and [intake policy](../../POLICY.md).
No new upstream dependency or source pin is introduced.

## Exact contract

For `a = a0 + 2*a1`, `t = t0 + 2*t1`, the operation is
`|a,t> -> |a,t XOR [1,2,3,0][a]>`. The interface is the unchanged left-associated
`Q<(((Bit,Bit),Bit),Bit)>`, with ordered leaves `(a0,a1,t0,t1)` and integer
coordinate `a + 4*t`. Every specified amplitude is exactly **+1**; all other
matrix entries are zero. All sixteen inputs, including arbitrary initial
targets, are part of the contract.

| Input coordinate | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Output coordinate | 4 | 9 | 14 | 3 | 0 | 13 | 10 | 7 | 12 | 1 | 6 | 11 | 8 | 5 | 2 | 15 |

The written order is deliberately `3 => keep, 1 => load2, 0 => load1,
2 => load3`. `put_bit`/`take_bit` preserve the selector coordinates; the
zero-width remainder is explicitly consumed. The target is never initialized
or overwritten inside the kernel. The closed `main` is only an observing driver.

## Independent checks

[Exact regressions](../../../tests/static_semantics/qmatch_qrom.rs) construct
the complete intended matrix directly from the table and integer coordinates,
without reading either implementation. The retained circuit is interpreted by
the existing independent test evaluator over exact cyclotomic dyadics, including
its original function bodies and output axis order. Both this qmatch translation
and the current [CNOT/X translation](../qrom2/README.md) must individually equal
that matrix. Their agreement with each other is not the oracle.

The same independently constructed 256 coefficients are supplied to the
unchanged native encoded-contract checker. Wrong-arm and arm-phase sources
must compile successfully, then fail that request specifically with
`ContractError::EquationMismatch`. Parser, ownership, unavailable-profile,
transport and capacity failures fail the regression. The first negative
changes only arm 1 from XOR 2 to XOR 1. The second adds an eighth-turn phase to
arm 3: every computational-basis probability still agrees. A whole-operation
scalar mutation separately guards against equality modulo global phase.

Exact dense phased superposition and Choi-vector probes retain ordered complex
amplitudes and external-reference correlations. The Choi extension is algebra
inside the harness, not an eight-qubit source or native request. Equality of the
complete four-qubit operator implies equality after tensoring any reference
identity, including entangled inputs. Native checked quantum size remains four;
production work, source, matrix and quantum-size limits are unchanged.

With the pinned Rust and built/audited native checker selected:

```sh
cargo test --test static_semantics qmatch_qrom -- --include-ignored
python3 scripts/check_input_corpus.py target/debug/qleisli --case qualtran/qrom2_qmatch
```

The existing normal/MSRV `static_semantics` targets and native comparison manifest
run the exact tests. Maintained corpus discovery includes the positive case;
`additional_semantic_faults` registers both valid negative sources without
rewriting historical manifests bound by earlier migrations. The numerical
corpus runner retains its separate basis/X/Y interference observations.

## Evidence and remaining obligations

[Authoring history](../../authoring/qmatch-qrom/README.md) preserves this session's
first source bytes, actual diagnostics and the preceding audit's provenance.
Optional `QLEISLI_QROM_EVIDENCE_DIR` records the exact source/wrapper and accepted
IR/request bytes from the Rust regression. Records are output only, never an
acceptance input.

These are bounded conformance observations and native equations, not a general
compiler or runtime preservation proof. CLI checks still report
`source_preservation_verified: false`. Original source-to-IR preservation,
native compilation/decoder/runtime correspondence, general QROM synthesis and
broader QS/PR/RS/EXACT obligations remain separate. Passing does not close
[#521](https://github.com/MGYamada/Qleisli/issues/521), establish latest-head CI
or review, or authorize a release.
