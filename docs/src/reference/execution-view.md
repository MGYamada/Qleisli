# Canonical execution-view encoding

This is the implementation contract for
[#362](https://github.com/MGYamada/Qleisli/issues/362). QDV1 describes decoded
data; it is separate from the QIRF artifact version and the native request/reply
version. Encoding a description grants no acceptance authority.

The current foundation implements the byte encoding, the typed finite walkers
and a pure Lean finite comparison gate below. Rust exercises these walkers only
in tests. Native CLI comparison, complete retained execution profiles and the
protocol cutover remain required. The existing production protocol has not
changed. The foundation must not be reported as a bound production execution view.

## Byte grammar

An encoding starts with the four ASCII bytes `QDV1`, followed by exactly one
value. Values have these tags and payloads:

| Tag | Value | Payload |
| --- | --- | --- |
| `00` | null | none |
| `01` | false | none |
| `02` | true | none |
| `03` | natural | exactly eight bytes, unsigned little endian |
| `04` | text | four-byte unsigned little-endian UTF-8 byte count, then those bytes |
| `05` | ordered array | four-byte unsigned little-endian element count, then each complete value in order |

There are no object keys, floating-point values, aliases, whitespace, padding
or optional omitted fields in this grammar. Records use arrays with an explicit
record tag and a fixed field order supplied by their profile. Absence is null;
it is distinct from every empty array, empty string, false and zero. The
natural range is `0..18446744073709551615`; larger values reject, never truncate.

Text preserves its decoded Unicode scalar sequence as UTF-8. There is no Unicode
normalization. A valid surrogate pair in a source JSON string and the same
literal non-BMP character yield the same decoded text; a replacement character
is different. An unpaired surrogate is not an admissible Rust string. A
conservative host parser refusal does not demonstrate execution divergence.

The encoder bounds a description to 67,108,864 bytes including its header.
The root has depth zero; depth 128 is allowed and depth 129 rejects. A capacity
failure returns no encoding and cannot authorize a view. These are transport
capacities, not quantitative program resource certificates. The separately
configured repository fixture/PR budgets remain unchanged.

For example, null is `5144563100`, false is `5144563101`, and zero is
`51445631030000000000000000`. The string `𝄞` is
`514456310404000000f09d849e`. Byte counts concern UTF-8 bytes, not character
counts. The [shared vectors](../../../tests/fixtures/verification_v030/execution-view-binding/canonical-vectors.json)
fix type distinctions, unsigned width, endian order, nested array order, NUL,
non-BMP/replacement characters and composed/decomposed text.

## Typed finite records

Every row below denotes an array beginning with the quoted tag, followed by
the fields in the stated order. IDs, widths, axis indices, table entries,
gate codes and phase codes are naturals. Lists remain ordered arrays. Booleans
remain boolean values. These are data descriptions; they do not assert that
the described data satisfies ownership, effects or a semantic contract.

| Tag | Fields after the tag |
| --- | --- |
| `program` | quantum input ports, classical inputs, operations, quantum outputs, classical outputs, declared effect |
| `port` | token, wire list, bit width |
| `pack-unit`, `unpack-unit` | output or input token, respectively |
| `init0` | output token, wire |
| `gate` in a raw operation | gate code, input token, output token |
| `cnot` in a raw operation | control token, target token, control output, target output |
| `toffoli` in a raw operation | first control, second control, target, first control output, second control output, target output |
| `quantum-if` | control, target, control output, target output, zero-arm unitary steps, one-arm unitary steps |
| `split` | input, left output, right output, left bit width |
| `join` | left input, right input, output |
| `lift-basis` | input, output, output wires, table |
| `apply-unitary` | input, output, circuit steps |
| `certified-compute` | source, source output, ancilla wires, function table, use steps, logical steps |
| `compute-use-uncompute` | source, source output, targets, ancilla wires, function table, protected uses |
| `target` | input token, output token |
| `measure` | input token, output classical ID |
| `reset` | input token, output token, fresh wire |
| `discard` | input token |
| `constant` | boolean value, output classical ID |
| `not` | input classical ID, output classical ID |
| `xor`, `and` | left classical ID, right classical ID, output classical ID |
| `branch` | condition ID, complete then operations, complete else operations, quantum phis, classical phis |
| `quantum-phi` | then token, else token, output token, output wires |
| `classical-phi` | then ID, else ID, output ID |

Gate codes `0,1,2,3` mean H, X, Z, T. Phase codes `0,1` mean minus one and an
eighth turn. Declared effects `0,1,2` mean unitary, isometry and observe. The
derived effect and final live ports require separate binding in the complete
production profile; the `program` record does not supply that metadata.

Circuit steps use `step(controls, action)`, with each control described as
`control(index, when-one)`. Actions are `hadamard(target)`,
`monomial(indices, permutation, phases)` and
`contract(indices, original-evidence-table-index, adjoint)`.
Unitary steps inside a quantum conditional are `gate(gate-code, target-index)`,
`cnot(control-index, target-index)`, `toffoli(first-index, second-index, target-index)`
and `phase(phase-code)`; their enclosing field distinguishes them from raw
operations with similarly named tags.

Protected uses are `protected-gate(bit, gate-code)`,
`target-gate(controls, target-index, gate-code)` and
`protected-phase(controls, phase-code)`. A protected bit is
`protected-bit(region, index)`, with source region zero and ancilla region one.
Each protected control is `protected-control(bit, when-one)`.

A basis is its exact preorder list of `unit()`, `bit()`, `bits(width)`,
`pair()` and `tuple(arity)` records. This preserves zero-width fields, atomic
registers and immediate tuple arity. A matrix is `matrix(rows, cols, entries)`;
each row-major entry is a four-element array of `dyadic(numerator-text, exponent)`
records in `a,b,c,d` order. No shape or coefficient is inferred from width.

The Rust retained-evidence walker reads
`function-evidence(signature, implementation, specification, identity, circuit,
meaning, depth, expanded-steps)`. The identity is
`identity(implementation-name, specification-name, sources)` with
`source(path, text)` records. The circuit is `circuit(basis, steps)`. Dependency
indices identify original graph entries; process addresses serve only as
private lookup keys and are never encoded. Missing or ambiguous mappings fail
before any bytes are returned. Lean independently derives the execution
circuit from its literal implementation events and uses a fresh native receipt
for the checked exact matrix, depth and expanded-step count. Closed classical
branches select events only after both arms have been checked. Frame reorderings
rename later axes; only the final composite permutation is materialized.
Connecting these walkers to the complete retained graph and native comparison
remains an integration obligation.

The [finite vectors](../../../tests/fixtures/verification_v030/execution-view-binding/finite-walker-vectors.json)
include three retained observing source roots, all 21 Raw constructors, both
branch arms, zero-width owners, exact type trees and rectangular matrices.
The combined all-constructors row is intentionally transport data, not an
accepted quantum program. Rust and Lean read their own typed data and compare
against these independently specified descriptions. This checks the walkers,
not execution binding or a source/runtime preservation theorem.

The [function-cache vectors](../../../tests/fixtures/verification_v030/execution-view-binding/function-cache-vectors.json)
add ten independently specified full retained-evidence descriptions. They
cover Unit ownership, H–T–H exact coefficients, output permutations, branch
routes that compose or cancel, certified/protected ancilla phases, quantum
conditional phase and a dependency with an adjoint. Rust checks actual retained
function data; Lean freshly checks the original bodies and derives its own
cache view. Dependency zero in the last row identifies the first corpus entry;
the test remaps actual retained Arc references to that explicit corpus index.
This test indexing is not the eventual production artifact graph mapping.

## Retained finite graph

The `finite-graph` record contains, in order: the original root program index,
the actual root interface or null, the ordered source records, all decoded
programs in original table order, all fresh function-evidence records in
original table order, the actual execution root, its derived effect, and its
ordered output ports. A present interface is
`root-interface(input-basis, output-basis)`. The root is described separately
from the program table so that a different runtime root cannot borrow the
table's comparison. Output ports follow the program's return order, including
zero-width owners; the live-store insertion order is not their order.

Lean derives the effect from its checked observation state: observing if any
observing operation occurred, otherwise isometry if allocation or a width
change required it, otherwise unitary. A conservative declared `observe`
effect may therefore have derived unitary effect. Both fields remain bound.
Full-graph dependency references use original artifact indices, including
when the successful checking order differs from table order. The walker reads
fresh graph receipts produced by the common checker, never submitted receipts.

The [graph vectors](../../../tests/fixtures/verification_v030/execution-view-binding/finite-graph-vectors.json)
retain three original observing sentinels and add Unit interfaces, ordered
mixed-width output ports, conservative effects and an evidence table whose
first entry depends on its second. These remain bounded transport comparisons;
native gate and protocol integration are required before execution binding.

## Retained contract stages

The common native-contract adapter now retains its decoded original artifact,
request bytes and typed obligation for all six existing profiles. Encoded
contracts retain the freshly checked root, reconstructed action and finite
wrapper result. Leaf requests retain the original ports and exact matrix;
pure leaves retain both domain/codomain trees and their checked root/action.
Control requests retain the exact signature or owner forest and ordered axes.
Instrument requests retain the independently decoded expected artifact and
its order, signatures and source identity, with both fresh checked roots.

The old adapter results are projections of these same computations. Universal
Lean equalities preserve successes, errors and remaining work, and stage
binding theorems identify the retained core results. The leaf path retains its
existing validation sequence. No additional acceptance rule, native mode or
execution handle is introduced.

`NativeContract.checkRetained_bound` additionally ties every returned field to
the original packet body/request, UTF-8 text, parsed JSON, decoded artifact/order
and the exact returned request-stage result. Its work state runs continuously
from artifact decoding to the existing six-kind dispatch. This output-field
binding is separate from `checkRetained_acceptance`, whose original existential
acceptance witness does not by itself identify every field of the returned record.
Neither theorem establishes an execution-view match or runtime preservation.

The typed obligation walkers read these retained stages in Lean and the actual
typed contract/boundary/signature values in Rust. Their records are:

| Tag | Fields after the tag |
| --- | --- |
| `encoding` | logical basis, physical basis, exact map |
| `encoded-contract` | input encoding, output encoding, logical matrix |
| `encoded` | encoded contract |
| `leaf` | signature, input port, output port, required matrix |
| `pure-leaf` | domain, codomain, input port, output port, required matrix |
| `control` | signature, ordered control axes |
| `control-owners` | ordered owner signatures, ordered control axes |
| `instrument` | actual signature, expected signature, source identity |
| `instrument-signature` | input basis, complete prefix result tree |

Instrument result atoms are `unit()`, `bit()`, `bits(width)`, `quantum(basis)`,
`pair()` and `tuple(arity)`. Quantum owners and classical values remain distinct,
including at zero width. The actual and expected signatures are described
separately. Identity preserves names, source order and complete decoded strings.
The independently decoded expected artifact and fresh checked roots belong in
the complete instrument profile; the obligation record alone does not bind them.

The caller-circuit walker describes the supplied actual `Circuit` as
`circuit(basis, steps)`, retaining literal controls, phase tables, axis order and
actual dependency references mapped to original indices. It does not use the
synthetic single-action wrapper constructed by the encoded-contract checker.
The [contract vectors](../../../tests/fixtures/verification_v030/execution-view-binding/contract-walker-vectors.json)
check all six obligation kinds and two literal caller circuits. Lean freshly
checks each original native request before walking its retained obligation;
Rust describes independently constructed typed values. Data mutations distinguish
encodings, phase, both ports, equal-width type trees, source identity and axes.
The [authoring record](../../../tests/fixtures/verification_v030/execution-view-binding/README.md)
describes both preserved refusals and their corrections.
Actual caller circuit/cache binding and production comparison remain required.

## Pure complete contract comparison

The `native-contract` record has three fields after its tag: the typed request,
the actual `finite-graph`, and an expected `finite-graph` for instruments or
`null` for the other profiles. Both graphs include their original program and
evidence tables, selected runtime root, exact cached function data, ordered
interfaces, sources and derived metadata. The expected graph is taken from the
instrument's independently decoded and freshly checked reference, even when
its owner or wire identities differ from the actual graph.

`CheckedContract.check` invokes the original native-contract checker once,
then derives this description from that same retained result and compares the
canonical bytes inside Lean. Its binding theorem retains the exact returned
record, original-packet field binding, comparison and continuous work states.
Frame, error and work plumbing is shared with the pure finite gate. Core work
finishes before describing the view; the added work is not hidden.

Rust's corresponding walker borrows the actual typed obligation and retained
actual/reference runtime graphs. One bounded writer accounts for nesting and
total storage across all three fields. Neither side serializes the original
request JSON as the execution view. Rust still needs private unbound staging
before this walker can participate in production acceptance.

The [complete-contract vectors](../../../tests/fixtures/verification_v030/execution-view-binding/complete-contract-vectors.json)
retain eight independently authored graph descriptions covering every current
contract kind and an observing reference with distinct owner/wire identities.
The pure Lean gate refuses 1,152 individual scalar, empty-list and array-shape
mutations over these valid original requests. The Rust tests also refuse missing
or unexpected reference graphs. These checks do not bind original caller Arc
aliases/caches or hierarchy execution and do not complete the native CLI or
protocol cutover. No execution handle or new guarantee is issued by the walker.

## Required production profiles

Profile walkers must inspect actual retained typed data independently of the
existing QIRF JSON encoder and hierarchy bridge writer. They must not merely
copy original JSON fields or serialize a surrogate view that execution discards.
Their record schemas and shared vectors must cover:

- Finite raw operations and both branch arms, complete input/output ports,
  zero-width owners, declared/derived effects, classical identities and phis,
  root interface, graph references, original implementation/specification
  bodies and source identity strings.
- Actual function circuit and exact matrix caches, with their dependency
  mapping. A cache cannot be omitted because its producer intends it to agree
  with the body. A different cache used by execution is a different view.
- Encoded contract circuits and encodings, rectangular pure-leaf boundaries,
  instrument signatures, expected artifacts and independent request data.
- Actual compiled hierarchy nodes, finite matrices, root/interface axis order,
  exact phase parameters, preparation positions and ordered readout/packing
  and residual axes. Sampling must consume the same bound plan.

Exact scalar descriptions retain all four ordered dyadic coefficients of
`a + b sqrt(2) + i(c + d sqrt(2))`. Each coefficient has a canonical signed
decimal numerator and its nonnegative power-of-two denominator exponent.
Zero has exponent zero; negative zero, leading zeroes and reducible nonzero
dyadics are not canonical. Matrix dimensions and row-major entry order remain
explicit. Exact phase data is bound before numerical interpretation; numerical
runtime values are not a replacement for exact coefficients.

Complete profile record schemas and actual native comparison are not supplied
by the primitive byte grammar alone. Until their integration, no public
execution API may claim QDV1 comparison or use this foundation as a fallback.

## Acceptance and remaining assumptions

`ExecutionView.CheckedFinite.check` is a pure staging gate over an original
packet and a mandatory candidate view. It checks QDV1 framing, decodes the
original artifact/request, runs the common typed QIRF check once, derives the
view from that same fresh result, encodes it and compares exact byte arrays
inside Lean. It distinguishes `invalidView`, packet errors, native checker
errors, encoding failures and `decodedView`. The framing reader checks exactly
one bounded value, UTF-8, lengths, depth and EOF without allocating a list from
an untrusted array count. Neither framing nor encoding is semantic acceptance.

`check_binding` retains the original packet/body/request, the actual decoded
graph and checking computations, and equality of the candidate with the exact
encoding of that result's view. `Binding.original` transports that success to
the existing ordinary packet acceptance witness before view derivation.
`check_ownershipSafe` and `check_scopeSafe` concern the same original selected
root. View derivation has a separate remaining-work value; these proofs do not
claim unchanged whole-gate work or serializer/runtime correctness. This is
technical preservation support, not a new admitted constitutional guarantee.

The shared runner checks seven independently valid original artifacts against
their correct views and 71 divergent candidates, including every graph field
and retained evidence-cache fields. It separately covers malformed frames,
native work refusal and an original optional request. These are tests of the
pure staging gate. No native CLI mode or Rust execution handle uses it yet;
all execution profiles and the mandatory versioned protocol remain open.

The intended production gate compares the submitted actual-view encoding with
Lean's own decoded/derived view inside Lean. A well-framed mismatch rejects
with `decoded_view`. Missing or malformed data and unsupported protocol
versions reject separately. The production cutover must reject old native
request/reply frames; QIRF1/2 artifact compatibility is a separate contract.

Any private inspection needed to construct a candidate must not expose an
accepted execution handle. After successful comparison, execution must retain
the same immutable decoded/compiled data, rather than decode again. Tests must
mutate actual view fields while the original artifact remains natively valid.

Faithfulness of Rust view serialization/materialization, native compilation,
IO and runtime, numerical interpretation and source lowering remain explicit
proof duties. Hierarchy bridge comparison alone does not prove correspondence
to the original external JSON or source. Current ordinary ownership and
classical-scope guarantees must remain connected through the pure gate to the
actual new native protocol entry point by checked proofs; retaining old theorem
names or hashes is insufficient. QDV1 introduces no reference meaning, constitutional
interpretation, guarantee admission, full QS/PR/RS/EXACT discharge or release
approval.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
