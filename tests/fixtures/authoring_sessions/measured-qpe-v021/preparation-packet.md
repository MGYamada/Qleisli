# Fresh-zero source continuation — 2026-09-30

An independent request supplies the complete input `Side` and ordered fresh
one-bit ports. A proposal supplies actual `init0` definitions and the complete
output `Side`. Every step must have Iso effect, preserve the entire preceding
quantum/classical frame, and append exactly its requested fresh owner and axis.
Uniqueness includes pre-existing and zero-width owners. The empty case preserves
the input exactly. No zero-state flag or numerical tolerance is accepted.

The independent coefficient semantics multiplies by the zero factor of each
fresh axis: coefficients equal the input when all new bits are zero, and zero
otherwise. Old axes and arbitrary reference coordinates survive unchanged.
`Preparation.check_reference` proves that the actual projected initialization
sequence has this action; `check_boundary` binds the complete output frame.
These are component results, not the entire QPE or source-preservation theorem.
The reference definition still needs human review before production adoption.

Private `--preparation-check` transport uses `QLZ1`, request input Side, requested
fresh ports encoded as a Side with empty classical fields, the actual definition
array, output Side and remaining work. It reuses QLH1's u32/length-prefixed
encoding, strict EOF and 64 MiB/one-million-word/100,000-element limits.
The response is `qleisli.preparation-result 1`, then `checked` and work, or
`error` and `format`, `limit`, `invalid_ir` or `contract` with exit 1. The existing
16-axis and two-million-work limits apply. This response is component data.

[Ordinary source helpers](../../../../corpus/sized/measured_qpe/README.md) now
emit an initialization proposal, shared pure graph, observations and CBits pack.
Local frames preserve recursive helper structure. Untrusted graph compaction
composes adjacent rewires, removes exact identities, keeps shared/zero-repeat
bodies and replaces a balanced internal empty-register lifecycle by the existing
explicit Bit/Bits(1) conversion. It cannot erase an input or output empty owner.
Native inspection and Rust finite reconstruction still check the final graph.
Numerical before/after comparisons are regressions, not a preservation proof.
Inverse operands now retain their complete recursive subgraphs so independent
component inspection can read the actual decomposition. Surrounding routing
is still compacted; no algorithm name or annotation grants acceptance.

[Preparation validation](preparation-validation.json) covers actual-node,
frame/type/effect/freshness mutations and independent exact reference columns.
[Measured source validation](instrument-validation.json) covers initialization,
ordinary readout, order/amplitude clients, interleaved measurement/gates and
fresh preparation, plus wrong-initialization/order counterexamples. It records
the still-rejected small `(2,4)` wrapper. Full independent instrument/provider
binding, production source/runtime integration and the
remaining R14/H1–H5 gates remain open. No external schema is enabled.

## Composed pending checker

`Hierarchical.Instrument.checkAll` now composes the three checks in Lean. Its
request contains independent preparation, pure-root and readout requests and
the final public Side. Its proposal contains actual preparation/readout packets,
the pure artifact and its graph/pair schedules. It checks the pure artifact
against the independently supplied root meaning, then binds both intermediate
boundaries and the final output. Preparation and readout use the remaining
allowance after the pure/root and boundary costs. `checkAll_stages`,
`checkAll_boundary` and `checkAll_budget` prove the actual stage checks, exact
connections and the unchanged two-million total cap.

The result retains the actual `Root.Checked`, including every finite program
and finite-meaning equality obligation. Opaque finite bytes can produce only a
pending obligation, never a verified instrument. There is no serialized
success-flag input. [Fourteen native cases](composed-instrument-validation.json)
exercise independent phase requests, finite-obligation retention, forged
initialization/readout, disconnected boundaries, lost targets, packing and
oversized metadata. The earlier source report concerns separate component invocations. The host
connection below now performs fresh composed checking and Rust discharge;
named QPE/source binding and whole-instrument completeness remain open.

### Host connection contract

The additive `initialize-unitary-readout-v1` host profile takes two independent
JSON documents. `qleisli.instrument-ir` version 1 contains `preparation`
(`initializations`, `outputs`), `circuit` (the complete hierarchical artifact)
and `readout` (`measurements`, `pack`, `outputs`). `qleisli.instrument-request`
version 1 contains `preparation` (`inputs`, `fresh` one-bit port array), `circuit`
(an explicit `qleisli.hierarchy-request` meaning graph), `readout` (`inputs`,
ordered `owners`, fresh `result`) and the public `outputs`. Both documents
include their exact `format`, `version` and `profile`; unknown/duplicate fields
reject. Nested types and actual definitions reuse the hierarchy codec. A named
QFT request is outside this composed-root profile for now.

Private `QLI1` frames the QLR1 circuit request as a length-prefixed block, then
preparation input Side/fresh Side (empty classical array)/actual definitions/
output Side, readout input Side/owner array/result/actual definitions/pack/output
Side and the independent public output Side. All nested frames share a
one-million-word allowance and the entire message is capped at 64 MiB. The
native result names the actual finite implementation and requested-meaning
obligations. The Rust host must reconstruct every one under its existing exact
budget before returning an immutable checked report. The report retains both
complete documents and cannot be constructed from a serialized success flag.
This connection does not yet adopt production source semantics or a named QPE
schema; completeness and source/request independence remain obligations.

`Kernel::check_instrument` now implements this contract. Its sealed
`CheckedInstrument` retains both documents, all reconstructed finite leaves
and structural/exact work counts. It is separate from production
`VerifiedProgram`. [Host validation](host-instrument-validation.json) covers
772 independent binary frames, the shared nested decoder budget, missing or
duplicate returned obligations and exact phase faults even under zero repeat.
Four small source clients pass composed checks and 208 independent complex
coefficient probes; two source faults reject against a fixed baseline request.
Those baseline-generated requests test mutation binding, not independently
named QPE semantics. Hand-authored H/control requests separately test the host's
independent equation binding. [Both package audits](host-schema-validation.json)
retain disabled external schemas.

### Complete branch interpretation

The [branch bridge](../../../../lean/Qleisli/HierarchicalInstrument.lean) now
interprets actual initialization nodes, the constructed pure operator and
actual ordered readout as one unnormalized complex coefficient transform.
The [independent reference module](../../../../lean/Qleisli/Semantics/Instrument.lean)
imports no hierarchy/checker code. For a requested outcome `y`, residual label
`z` and original basis label `x`, its branch matrix is

```text
K_y[z,x] = sum_s U[select(y,z),s] [fresh(s)=0] [old(s)=x].
```

`checkAll_branches` derives the complete phase-sensitive transform, and
`checkAll_density` derives the full residual/reference density matrix, from
actual acceptance and the existing finite implementation/meaning equations.
`checkAll_classical` binds actual CBit packing and public output width.
`Meaning.actual_ir_only` excludes proposed meanings/proof metadata from the
actual interpretation. A [CNOT/S calibration](../../../../lean/Qleisli/InstrumentExamples.lean)
proves the expected correlated branch and relative `i` phase for arbitrary
input/reference coefficients. This calibration is not an algorithm proof.

[Both builds and axiom audits](branch-schema-validation.json) pass. The full
named QPE/provider formula, whole-instrument completeness, source preservation
and production source/runtime integration remain open. Rust finite-reader and
native/transport correspondence remain explicit assumptions. Human review of
the new reference definition is required before production adoption.
