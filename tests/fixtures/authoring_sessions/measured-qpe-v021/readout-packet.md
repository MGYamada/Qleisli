# Bounded readout continuation — 2026-09-30

The retained first source needs ordinary initialization and bulk measurement
helpers. First implement the missing measurement/assembly boundary; this packet
does not substitute for initialization, the coherent QPE proof or production
source/runtime integration.

An independent request supplies the complete input `Side`, an ordered list of
distinct one-bit owners to measure and a fresh classical result name. A proposal
supplies actual `observeZ` definitions, the intermediate classical names to
pack, and the complete output `Side`. The checker must bind each actual body,
effect and before/after interface. The intermediate results are packed in the
request's order, with position zero the least significant bit; intermediate
classical values are local and the public result has the exact type `CBits<m>`.
Other classical inputs and quantum owners (including Unit and Bits(0)) survive
unchanged. Measurement consumes the selected logical owners. The empty case
creates `CBits<0>` explicitly and consumes no quantum owner.

Reference semantics selects an unnormalized branch of the input coefficient
function by fixing the measured axes to the outcome bits. The remaining axes
and an arbitrary reference coordinate are unchanged. No probabilities,
normalization, independence of quantum owners or floating tolerance enters the
acceptance test. Packing means `b0 + 2*b1 + ...`; bit order is contractual.

This is an additive internal readout component, not a new variant of a public
Rust enum, an external schema, or permission to accept the entire QPE artifact.
Quantum register unpacking remains explicit and is checked by the existing
structural rules before this component. A future integration must bind these
boundaries to that actual graph and the independently checked pure provider.

The optional kernel command `--readout-check` receives private framing on stdin:
magic `QLM1`, the independently supplied input Side/owner array/result name,
the proposed definition array/pack-name array/output Side, then the work budget.
Fields reuse QLH1's little-endian u32/length-prefixed array, Side and Definition
encodings, 64 MiB/one-million-word/100,000-element limits and strict EOF. No
u32 truncation, text evaluation or implicit type conversion is permitted.
The result is `qleisli.readout-result 1`, followed by `checked` and work used,
or `error` and `format`, `limit`, `invalid_ir` or `contract`; rejection exits 1.
This is an internal component interface, not an external schema or a whole
artifact receipt. The caller must bind it to the preceding checked graph.

Validation: native differential cases on 0–3 measured qubits; noncontiguous
axis/owner/value labels, pre-existing classical values, empty quantum owners,
reordered measurements, wrong packing, aliased targets, changed output owners,
wrong effects and limits. Compare branch coefficients on superpositions and
entangled references, retaining phase and residual targets. Build and audit the
actual executable Lean definitions. Do not generate maximum-size corpus cases.
