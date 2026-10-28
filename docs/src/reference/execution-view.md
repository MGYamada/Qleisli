# Canonical execution-view encoding

This is the implementation contract for
[#362](https://github.com/MGYamada/Qleisli/issues/362). QDV1 describes decoded
data; it is separate from the QIRF artifact version and the native request/reply
version. Encoding a description grants no acceptance authority.

QLV3 connects these walkers and pure Lean gates to the production native
entry points. Finite execution prepares its actual graph, dependency caches
and root metadata before submission. The comparison borrows those exact
allocations; successful binding moves them into `AcceptedProgram` without
re-decoding. Both the immutable subject identity and an execution-capable
native scope are required. An inspection for identical bytes cannot substitute.

Hierarchy reports likewise retain the same boxed plan prepared before the
fresh native check. Each of the five modes compares that plan, including exact
finite descriptions and ordered preparation/readout coordinates. A failed plan
or description is retained as an execution error while explicit inspection
remains available. No report can lazily replace it with an unchecked plan.
Compatibility reports additionally keep freshly checked finite-leaf handles.

## Native envelope cutover

The #255 cutover extends #362 with `QLV3` as the external native envelope.
Its seven header fields are four magic bytes, the explicit `u32` constitutional
edition (2026), a `u32` scope, three `u32` byte
lengths (original payload, graph view, caller view), and a `u32` alias count.
Integers are little endian. The payload begins at byte 28, followed by
the alias indices as `u32`s.
Exact EOF is required. The complete envelope is bounded by 64 MiB, the two
views together by the existing QDV1 byte limit, and the alias count by 100,000.
Original per-profile limits remain in force; these are not increased budgets.

Scope 0 (`inspection`) requires empty views and no aliases. Scope 1
(`execution`) requires the graph view, an empty caller view and no aliases.
Scope 2 (`caller`) requires both views; it also compares the literal caller
root and each actual retained evidence alias against its proposed entry index.
Indices are proposals, not evidence. Hierarchy permits scopes 0 and 1;
standalone preparation/readout components permit only scope 0.

The original finite payload remains the exact internal QLV1 packet, and a
hierarchy payload retains its original bridge encoding. These inner payloads
are checked by the existing definitions. Neither is accepted as an unwrapped
external request after cutover. No compatibility retry is permitted.

All fifteen native modes use `qleisli.native-result 3`. Successful replies
contain, one per line: claim (`accepted`, `pending`, `engineering-checked` or
`checked`), checked edition, compiled complete product version, canonical mode
argument, checked scope, and the mode's unchanged payload fields. A final
newline is required. Finite payloads retain exact work and the request-presence
flag; hierarchy payloads retain structural/exact work and ordered obligations;
engineering payloads retain exact work. Component payloads retain their
original fields. These claims remain distinct.

The internal `--carrier-pure-check` mode requires execution scope. Its
`finite-carrier-pure-v1` QDV1 record compares the actual graph, attached and
required ordered owner forests, public effects and exact logical matrix.
Its private component result grants no ordinary source execution or
source-preservation claim; the [carrier boundary](production-boundary.md#finite-nominal-carrier-requests)
states the checked equations and remaining obligations.

The internal `--ordinary-root-check` mode also requires execution scope. Its
`finite-ordinary-root-v1` record contains the actual graph, project/exported
selection, original module/function, full result basis, typed SSA storage tree
and public effect. Lean freshly reads and checks the original declared result
and every complete exact instrument history before comparing this description.
The retained Rust program keeps the same graph and typed request objects.
An inspection/caller packet or an old-mode retry cannot authorize it. This
first closed ordinary-result slice supplies no original-body or numerical
runtime preservation theorem; see the
[ordinary-result boundary](production-boundary.md#closed-ordinary-result-requests).

Errors contain only the header, `error`, the rejection code and final newline;
they assert no successfully checked context. Hierarchy finite-decoder errors retain
their existing classification: malformed/noncanonical finite descriptions are
`format`, capacity failures are `limit`, and failed finite equations are
`contract`. The common dispatcher preserves that profile-specific projection. An unsupported well-framed edition
rejects as `edition`; a compared-view mismatch is `decoded_view`. Old external
QLV2/QLV1 requests and old replies reject without compatibility retry. Consumers
match edition, product, actual mode and requested scope before interpreting and
fully consuming their own bounded payload. Edition alone identifies neither a
checker implementation nor a completed constitutional proof.

The actual Main adapter invokes one pure `Protocol.NativeContext.run` and its
one reply projection. Its checked success bindings retain each original gate,
execution/caller comparison and scoped decoded-root property. Rust kernels
require an explicit edition; source commands derive it from the captured
manifest. Raw `verify-ir`, engineering commands and QASM/QIRF interop require
`--edition=2026`. Source inputs reject that override; interop source callers
may assert `--expect-edition=2026`, which must agree with the captured manifest
before kernel selection. Raw/foreign inputs reject that assertion.
Python requires an explicit `Client(..., edition="2026")` or CLI `--edition=2026`;
source calls use the expectation, and returned `Program` data retains its edition
for every fresh raw check. No new result-envelope fields convey acceptance.
The #255 migration still
requires complete helper, ecosystem, current-evidence and CI validation before
completion; this wire contract is not a release or broader proof claim.

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
counts. The [shared vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/canonical-vectors.json)
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
The production graph and caller descriptions include these walkers in the
native comparison before retaining the same runtime objects for execution.

The [finite vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/finite-walker-vectors.json)
include three retained observing source roots, all 21 Raw constructors, both
branch arms, zero-width owners, exact type trees and rectangular matrices.
The combined all-constructors row is intentionally transport data, not an
accepted quantum program. Rust and Lean read their own typed data and compare
against these independently specified descriptions. This checks the walkers,
not execution binding or a source/runtime preservation theorem.

The [function-cache vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/function-cache-vectors.json)
add ten independently specified full retained-evidence descriptions. They
cover Unit ownership, H–T–H exact coefficients, output permutations, branch
routes that compose or cancel, certified/protected ancilla phases, quantum
conditional phase and a dependency with an adjoint. Rust checks actual retained
function data; Lean freshly checks the original bodies and derives its own
cache view. Dependency zero in the last row identifies the first corpus entry;
the test remaps actual retained Arc references to that explicit corpus index.
This test indexing is separate from the original-index production graph mapping.

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

The [graph vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/finite-graph-vectors.json)
retain three original observing sentinels and add Unit interfaces, ordered
mixed-width output ports, conservative effects and an evidence table whose
first entry depends on its second. These remain bounded transport comparisons;
the native QLV3 regression separately exercises their production binding.

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
The [contract vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/contract-walker-vectors.json)
check all six obligation kinds and two literal caller circuits. Lean freshly
checks each original native request before walking its retained obligation;
Rust describes independently constructed typed values. Data mutations distinguish
encodings, phase, both ports, equal-width type trees, source identity and axes.
The [authoring record](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/README.md)
describes both preserved refusals and their corrections.
The QLV3 caller scope also binds the actual circuit steps and retained caches.

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
request JSON as the execution view. Production uses private unbound staging
and moves the compared graph into the accepted handle only after native success.

The [complete-contract vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/complete-contract-vectors.json)
retain eight independently authored graph descriptions covering every current
contract kind and an observing reference with distinct owner/wire identities.
The pure Lean gate refuses 1,152 individual scalar, empty-list and array-shape
mutations over these valid original requests. The Rust tests also refuse missing
or unexpected reference graphs. These pure checks are separate from the QLV3
native regressions and the caller/hierarchy bindings below. The walker alone
issues no execution handle or constitutional guarantee.

## Original caller evidence aliases

The caller collector retains the supplied root program, its optional
interface and every distinct actual `Arc<FunctionEvidence>` reachable through
implementation bodies, specification bodies and cached circuit steps. It walks
both complete classical branch arms and both certified use/logical step lists.
Repeated references to one Arc retain one entry; distinct Arcs retain separate
entries even when their snapshot keys are equal. Private addresses identify
objects during discovery and are never encoded.

The record is `caller-origin(interface-or-null, actual-root-program, aliases)`.
Each alias is `evidence-alias(original-evidence-index, function-evidence)` with
the complete actual function description specified above. An index is proposed
by the original encoder's canonical snapshot map. That lookup is not evidence
that the actual body, matrix, circuit or descendants equal Lean's fresh result.
The pure Lean attachment compares each emitted alias against that proposed
original entry. Native QLV3 caller requests invoke this attachment before
issuing an execution handle from the compared descriptions.

This extra traversal is necessary because the artifact encoder returns early
when it finds an equal snapshot. That encoder registers the directly encountered
Arc but need not visit that alias's distinct child Arcs. Describing only the
fresh Rust-decoded artifact or consulting only the encoder's direct pointer map
would omit actual caller caches. A missing original snapshot mapping refuses;
the collector cannot manufacture a new evidence-table entry from a cache.

One shared discovery counter charges operations, circuit steps and distinct Arcs
against the existing 1,000,000-node transport capacity. Description construction
uses one writer with the existing total-byte and depth limits. These are host
transport bounds, not quantitative quantum resource certificates.

The [caller recipes](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/caller-alias-recipes.json)
specify four complete descriptions independently of the walkers: repeated Arc,
separate equal clone, equal independently checked parents with distinct child
Arcs, and references in an unselected branch's certified use/logical circuits.
The [original branch refusal](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/first-caller-branch-refusal.json)
retains the first invalid phi wire and real diagnostic; the regression rechecks
that native refusal before exercising the corrected fresh-wire case.
These tests add no production acceptance authority. Private unbound staging and
hierarchy execution are checked separately through the QLV3 native entry points.

## Pure caller attachment

`Caller.alias` reads the fresh receipt at the supplied original evidence index
and independently derives its complete function description. Its universal
binding theorem identifies that exact slot and derivation. Repeated indices
are permitted for distinct actual caller aliases; missing receipts refuse.
`Caller.origin` describes the same checked root and original interface, then
every supplied alias in order. It accepts no host snapshot, matrix or receipt
as proof. It precharges the alias list and retains the existing node ceiling.

`CheckedCaller.finite` and `CheckedCaller.contract` each call their existing
finite or complete-contract comparison gate exactly once, then attach caller
comparison to that exact returned artifact/root. The latter covers all six
current contract kinds. Binding proofs preserve the actual base computation,
caller derivation, compared encoding and continuous work states. Original-byte
and ownership/scope binding, or native-contract returned-field binding, is
inherited from that same base execution.

The two QDV1 descriptions together must fit the existing 64 MiB ceiling.
The base description's byte length is reserved first. Caller construction
encodes the empty alias-list prefix, then counts each additional alias value
without its four-byte QDV1 header before retaining it. It therefore bounds
repeated large descriptions before accumulating the final tree. A supplied
lower byte limit cannot raise the fixed ceiling. Accumulation uses cons/reverse,
preserving order without quadratic list append. Exhausted work/capacity,
malformed framing, missing receipts and divergent data remain distinct refusals.

The four caller recipes also specify original artifacts and complete graphs
independently of the walkers. Rust checks exact original serialization and
the actual retained runtime graph. Lean checks the hand-authored caller data
through finite and native-contract attachments, including nonempty aliases;
all six contract kinds also have their existing independent request controls.
Mutations keep each native-valid original fixed and change only the supplied
description or proposed alias indices. Exact and one-byte-short capacities
exercise repeated-description accounting without large quantum instances.

The native CLI invokes these gates for the QLV3 caller scope. The gate checks
every emitted alias; correspondence of the collector with all objects actually
consumed by execution remains a runtime-preservation assumption. The binding
proofs do not prove the Rust collector or admit a constitutional guarantee.

## Retained hierarchy runtime plan

The Rust hierarchy runtime materializes one owned execution plan before the
fresh native decision. Native-only and finite-reconstructed reports retain that
same allocation, or its explicit materialization failure. Inspection still
makes the original native decision; unsupported execution cannot acquire a
replacement plan or change that decision. Public payload/request access is
immutable. Production QDV1 integration compares this same plan before
granting execution authority; preparation and retention alone do not perform
that comparison.

Pure plans retain original node order, child indices, width, root and ordered
input/output axes. Finite leaves own their exact matrices. A phase node retains
the literal target position and integer `j`/`k`; conversion to numerical sine
and cosine occurs only during interpretation. Phase normalization and numerical
values are not substituted for those exact parameters in the retained plan.

Instrument plans additionally retain input and fresh axes, preparation input
positions, measurement value/axis pairs in order, pack order, outcome positions
and residual axes/positions. Execution borrows this plan and creates fresh state
and work buffers. Every sampling shot borrows that same plan and starts from the
same normalized joint input/reference state. It does not reparse the JSON,
recompile nodes, reuse collapsed state or cache an earlier branch execution.

The independent small-system harness compares 19 original cases and 912 complex
coefficients, plus 768 seeded outcomes from three clients. Before/after records
retain identical original artifacts/requests and source hashes; coefficient
errors, work counts and outcome counts are unchanged. Private fault injection
also checks that execution retains its original plan after old transport/leaf
storage is poisoned. Hand-authored controls separately retain literal phase
parameters and nontrivial preparation/readout/reference coordinates. These
tests establish bounded regression evidence, separately from native plan comparison,
source/runtime preservation or a new constitutional guarantee.

## Hierarchy plan records

The hierarchy walker describes the owned plan actually read by execution and
sampling. It does not call the hierarchy JSON or bridge writer. These records
reuse the byte grammar and exact `matrix` record above:

| Record | Ordered fields |
| --- | --- |
| `hierarchy-plan` | `pure` or `instrument` record |
| `pure` | `hierarchy-program` |
| `hierarchy-program` | complete ordered node array, root index, input axes, output axes |
| `node` | width, operation |
| `leaf` | complete exact matrix |
| `sequence` | ordered child indices |
| `tensor` | left child, right child |
| `repeat` | child index, count |
| `inverse` | child index |
| `control` | child index, polarity |
| `permutation` | ordered source positions |
| `phase` | target position, literal numerator j, literal denominator exponent k |
| `instrument` | program, input axes, fresh axes, input positions, measurements, pack, outcome positions, residual axes, residual positions |
| `measurement` | actual classical value identity, actual quantum axis |

All definitions participate, including unused and zero-repeat children. A
structural operation becomes the actual coordinate permutation consumed by the
runtime. Literal phase parameters are retained before numerical evaluation;
`j = 9, k = 3` is not replaced by `j = 1, k = 3`. Preparation positions use
the circuit's input axes; outcome and residual positions use its output axes.
Measurement order and pack order are separate fields. Classical result ports
remain in the checked artifact even though the runtime stores its quantum
residual coordinates separately.

Lean derives this description independently from the typed hierarchy and exact
finite reconstructions. `HierarchyView.reconstructLeaf_bound` connects each
returned matrix to the original description decoding and original-body check
in that computation. `CheckedHierarchy.checkInspect` runs the original
structural checker once, reconstructs its actual finite obligations, derives
the view from those same results and compares inside Lean.
`checkInspect_binding` retains the original bridge, typed artifact, structural
result, exact matrices, continuous exact-work states and compared bytes.

Four shared cases fix a freshly checked H hierarchy, every runtime node kind,
reordered preparation/measurement/pack coordinates and a classical result port.
Three cases are explicitly untrusted materialization controls; they do not
claim accepted hierarchy or instrument semantics. The valid H original also
rejects 112 separately mutated, well-framed candidate descriptions, with
malformed-frame and exhausted-work controls. Rust's native and compatibility
reports describe the same retained H plan even after private fault injection
poisons old transport storage. The `CheckedHierarchy.Modes` gate also retains
the original fresh checks for independent root requests, named Fourier,
instruments and named QPE instruments. Its binding theorems retain the original
packet, actual finite matrices, independent pair/H checks and comparison with
the plan derived from those same objects. The QLV3 CLI dispatches to these gates
with a mandatory execution view when execution is requested. Production Rust
describes and retains the same plan; the walker itself confers no acceptance.

The [five-mode comparison record](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/hierarchy-mode-validation.json)
uses actual retained Rust plans
from five small native-accepted inputs. It rejects 2,683 individual description
mutations while fresh inspection of each original still succeeds. Three invalid
original requests separately exercise independent finite-pair phase checks and
the named-QPE phase-fixed H check. This is bounded cross-implementation evidence;
the generated graph/request structures are not independent source semantics.

## Engineering target execution view

The separate `--engineering-openqasm-check` mode accepts execution scope only.
Its original QLV1 body is the literal canonical OpenQASM byte array, and its
request is the fourteen-field closed engineering instrument contract described
in [realization](realization.md#literal-openqasm-target-comparison). The outer
QDV1 record `engineering-openqasm` has five ordered fields:

| Field | Retained data |
| --- | --- |
| 1 | Typed engineering request, including complete signatures, identity, epsilon and ordered majorants |
| 2 | Literal target bytes as an array of natural byte values |
| 3 | Ordered decoded gate-name strings |
| 4 | Complete generated actual graph, including its explicit Unit owner, unpack, initialization, terminal measurement and Observe effect |
| 5 | Complete original ideal graph and its fresh dependency checking results |

Lean independently decodes the same target bytes and ideal QIRF, checks their
complete instruments and bound, derives this view from that same result and
compares exact bytes. A stale word, graph, full type, identity or budget refuses
even when the submitted original remains individually valid. The Rust actual
graph is retained data, without an accepted-program constructor or fallback.
The private report authorizes only the declared engineering inequality; it
does not authorize simulation, source/export preservation, control, exact
cleanup or resources, including at epsilon zero. Existing envelope/view work
and size limits remain; the target profile separately limits bytes and gates.

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

The primitive byte grammar grants no authority by itself. The typed profile
walkers and fresh comparison gates below are required; encoding success is
never a fallback acceptance decision.

## Acceptance and remaining assumptions

`ExecutionView.CheckedFinite.check` is the pure finite comparison gate over an original
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
pure comparison gate. The QLV3 native tests separately check finite, complete
contract, caller and all five hierarchy paths, including valid original inputs
with divergent views and rejection of old external frames.

The production gate compares the submitted actual-view encoding with
Lean's own decoded/derived view inside Lean. A well-framed mismatch rejects
with `decoded_view`. Missing or malformed data and unsupported protocol
versions reject separately. The production cutover rejects old native
request/reply frames; QIRF1/2 artifact compatibility is a separate contract.

Hierarchy comparison covers inspection, independent root requests, named
Fourier requests, instruments and named QPE instruments. Each call obtains one
fresh structural result, reconstructs that result's actual finite leaves and
checks its independent pair/H obligations under the same exact-work allowance.
The plan then derives from those exact retained matrices and original typed
packet, including actual preparation and readout. A QPE plan uses the original
circuit entry, rather than the provider entry used for its independent request.
Inspection without an execution comparison remains distinct from an
execution-capable result, so unsupported execution cannot narrow inspection.

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
