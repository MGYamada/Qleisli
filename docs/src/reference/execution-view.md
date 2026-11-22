# Canonical execution-view encoding

The Rust host decodes its input and keeps the decoded data for execution. The
native checker decodes and checks the same input on its own. An
**execution view** lets the two sides compare what they hold. It is a
canonical description of the decoded data that the Rust host retains for
execution: a finite graph, a contract, a caller or a hierarchy plan. The
native checker derives its own description from the data that it decodes and
checks, and it compares the two descriptions as exact bytes.

This chapter specifies the formats of that comparison:

- The **QLV3 envelope** is the frame of every external request to the native
  checker. It carries an original payload, at most two views and proposed
  alias indices.
- **QDV1** is the byte encoding of one view. QDV1 describes decoded data. It
  is separate from the QIRF artifact version and from the version of the
  native request and reply.
- A **scope** is the check that an envelope requests: 0 (`inspection`),
  1 (`execution`) or 2 (`caller`).
- A **mode** is one dispatch argument of the native checker, such as
  `--runtime-root-check`. It selects which checker reads the original payload
  and which view record the comparison expects.
- A **walker** is the code that reads typed data and derives a view from it.
  Rust and the native checker each have their own walkers.

A description that encodes successfully is not thereby accepted: encoding
grants no acceptance authority. The chapter also specifies the native reply
and the view that each mode compares.

<a id="native-envelope-cutover"></a>

## The QLV3 envelope

The envelope puts the parts of one request into one frame: the original
payload, the views and the alias indices. A request to the native
checker is one QLV3 envelope. Its seven header fields are four magic bytes and
six `u32` values. Integers are little endian.

| Offset | Size in bytes | Field |
| --- | --- | --- |
| 0 | 4 | The magic bytes `QLV3` |
| 4 | 4 | The explicit constitutional edition (2026) |
| 8 | 4 | The scope |
| 12 | 4 | The byte length of the original payload |
| 16 | 4 | The byte length of the graph view |
| 20 | 4 | The byte length of the caller view |
| 24 | 4 | The alias count |
| 28 | The three lengths | The original payload, then the graph view, then the caller view |
| After the caller view | 4 for each alias | The alias indices as `u32`s |

The payload begins at byte 28. The original payload is the request of the
selected mode. A finite payload is the exact internal QLV1 packet, and a
hierarchy payload keeps its original bridge encoding. The envelope does not
change how these inner payloads are checked: the existing definitions check
them.

The mode `--openqasm-placement-check` is the exception. It reads a packet
that nests the envelope. [Status and limits](#status-and-limits) lists that
packet.

An alias index proposes an entry of the original evidence table for one piece
of function evidence that a caller retains.
[The caller view](#the-caller-view) gives the records and the rules of
aliases.

Rules:

- An envelope must end at exact EOF, after its last alias index. The native
  checker rejects missing data and trailing bytes with `format`.
- The magic bytes must be `QLV3`, and the original payload must not be empty.
- The edition must be 2026. The native checker rejects an unsupported edition
  in a well-framed envelope with `edition`.
- The complete envelope must not exceed 64 MiB.
- The two views together must not exceed the QDV1 byte limit.
- The alias count must not exceed 100,000.
- These limits raise no budget. The original limits of each profile apply
  unchanged.
- The scope must be 0, 1 or 2. The views and the aliases must match it as
  [Scopes](#scopes) states.
- A QLV1 packet and a hierarchy bridge payload must not be accepted as an
  external request without an envelope. An external QLV2 or QLV1 request
  is rejected. No compatibility retry is permitted. Compatibility of QIRF1/2
  artifacts is a separate contract.

> **Implementation note.** `Packet.read` in
> `lean-kernel/Protocol/ExecutionView/Packet.lean` reads the envelope. Rust
> kernels require an explicit edition. Source commands derive it from the
> captured manifest. Raw `verify-ir`, engineering commands and QASM/QIRF
> interop require `--edition=2026`. Source inputs reject that override. Interop
> source callers may assert `--expect-edition=2026`, which must agree with the
> captured manifest before kernel selection. Raw and foreign inputs reject
> that assertion.

> **Implementation note.** Python requires an explicit
> `Client(..., edition="2026")` or the CLI flag `--edition=2026`. Source calls
> use the expectation. Returned `Program` data retains its edition for every
> fresh raw check. No added result-envelope field conveys acceptance.

## Scopes

The scope says how much an envelope asks the native checker to compare. It
therefore fixes the views and the aliases that the envelope carries.

| Scope | Name | Graph view | Caller view | Aliases |
| --- | --- | --- | --- | --- |
| 0 | `inspection` | Empty | Empty | None |
| 1 | `execution` | Required | Empty | None |
| 2 | `caller` | Required | Required | Permitted |

Scope 0 compares no view. Scope 2 also compares the literal caller root and
each actual retained evidence alias against its proposed entry index.

Each mode permits a fixed set of scopes and compares one view record:

| Mode | Scopes | View record |
| --- | --- | --- |
| `--qirf-native` | 0, 1, 2 | [`finite-graph`](#the-finite-graph-view); in scope 2 also [`caller-origin`](#the-caller-view) |
| `--qirf-contract` | 0, 1, 2 | [`native-contract`](#the-contract-view); in scope 2 also `caller-origin` |
| `--hierarchy-pending`, `--hierarchy-request-pending`, `--hierarchy-fourier-pending`, `--instrument-pending`, `--qpe-instrument-pending` | 0, 1 | [`hierarchy-plan`](#the-hierarchy-plan-view) |
| `--hierarchy-control-pending` | 1 | `hierarchy-plan` |
| `--carrier-pure-check` | 1 | [`finite-carrier-pure-v1`](#the-carrier-view) |
| `--ordinary-root-check` | 1 | [`finite-ordinary-root-v2`](#the-ordinary-root-view) |
| `--engineering-openqasm-check` | 1 | [`engineering-openqasm`](#the-engineering-openqasm-view) |
| `--qmatch-source-check` | 1 | [`finite-source-qmatch-context-v4`](#the-named-arm-qmatch-component-view-version-4) |
| `--runtime-root-check`, `--qmatch-source-v5-check`, `--engineering-pure-check`, `--engineering-pure-tensor-check`, `--qirf-engineering-instrument-native`, `--engineering-openqasm-gate-check`, `--openqasm-placement-check` | 1 | Not specified in this chapter; see [Status and limits](#status-and-limits) |
| `--readout-check`, `--preparation-check` | 0 | None |

Rules:

- An envelope whose views or aliases do not match its scope is rejected with
  `format`.
- A mode rejects a scope outside its row with `format`. Hierarchy modes permit
  scopes 0 and 1, except `--hierarchy-control-pending`, which refuses scope 0.
  The standalone preparation and readout components permit only scope 0.
- Alias indices are proposals, not evidence.
- Execution requires two things: the immutable subject identity, and a native
  scope that is capable of execution. An inspection for identical bytes cannot
  substitute.

## The native reply

The native checker answers each request with one reply. A successful reply
names the claim of the checker and the context in which it checked: the
edition, the product version, the mode and the scope.

The compiler sends a version-1 verification request to `--verify-request`.
The binary request starts with `QLR1`, followed by three little-endian 32-bit
fields for the exact-work budget, product-version byte length and obligation
selector byte length. The product version and selector are followed by the
complete inner packet. It carries the edition, scope and original evidence.
The native checker rechecks that packet under the chosen obligation and
rejects a budget above 20,000,000. Readout and preparation also retain their
component-specific visit budgets.

The reply is text with one field on each line and a required final newline.
Rust checks the header and SHA-256 against the full request before interpreting
the payload. A successful reply has these fields.

| Line | Content |
| --- | --- |
| 1 | The header `qleisli.native-result 4` |
| 2 | The lowercase hexadecimal SHA-256 of the complete request |
| 3 | The claim |
| 4 | The checked edition |
| 5 | The complete product version compiled into the checker |
| 6 | The canonical obligation selector |
| 7 | The checked scope, by name |
| 8 and later | The payload fields of the obligation |

The differential driver can compare these decisions against a separate
version-3 checker supplied for offline replay. The packaged checker uses the
version-4 reply and refuses the former native mode command arguments.

The claim and the payload depend on the mode:

| Claim | Mode arguments | Payload fields, in order |
| --- | --- | --- |
| `accepted` | `--qirf-native` | exact work, request-presence flag (`0` or `1`) |
| `accepted` | `--qirf-contract`, `--carrier-pure-check`, `--ordinary-root-check`, `--runtime-root-check`, `--qmatch-source-check`, `--qmatch-source-v5-check` | exact work, the constant flag `1` |
| `pending` | `--hierarchy-pending`, `--hierarchy-request-pending`, `--hierarchy-control-pending`, `--hierarchy-fourier-pending`, `--instrument-pending`, `--qpe-instrument-pending` | visit count, exact work, then the ordered obligations as counted index lists |
| `engineering-checked` | `--engineering-pure-check`, `--engineering-pure-tensor-check`, `--qirf-engineering-instrument-native`, `--engineering-openqasm-check` | exact work |
| `engineering-checked` | `--engineering-openqasm-gate-check` | exact work, port basis width, gate count, T-gate count |
| `checked` | `--readout-check`, `--preparation-check` | visit count |
| `placement-checked` | `--openqasm-placement-check` | exact work, then the reserved, reset, gate, SWAP, T-gate and measurement counts |

The five claims are distinct. `Mode.status` and `payload` in
`lean-kernel/Protocol/NativeContext.lean` define this table.

An ordinary error reply contains the header, request identity, `error` and
one of these rejection codes:

| Code | Rejection |
| --- | --- |
| `format` | A malformed envelope, payload frame or view frame, a scope that the mode does not permit, or a derived view that cannot be encoded |
| `edition` | An unsupported edition in a well-framed envelope |
| `version` | A requested product version that differs from the compiled product version |
| `decoded_view` | A well-framed view that differs from the description that the native checker derives |
| `limit` | A capacity failure |
| `contract` | A rejected request or a failed equation |
| `clean_workspace`, `dirty_workspace` | A failed workspace restoration equation |
| `invalid_ir` | Another rejection of the original payload by its checker |

The internal mode `--openqasm-placement-check` has one longer error reply,
the located form. When this mode rejects a workspace restoration, its reply
can also carry the original Raw workspace interval. After `error` and
`clean_workspace` or `dirty_workspace`, the located form contains the checked
edition, the product, the mode, the execution scope, the zero-based Raw start
and the positive operation count. The located form is a rejection all the
same. Its extra fields serve diagnostics only.

Rules:

- An ordinary error reply contains only the header, request identity,
  `error`, the rejection code and the final newline. It asserts no context that was checked
  successfully.
- Before a consumer interprets its own bounded payload, it must match the
  edition, the product, the actual mode and the requested scope. It must
  consume that payload fully.
- A consumer must reject an old reply. No compatibility retry is permitted.
- An error from the finite decoder of a hierarchy mode keeps its
  classification. A malformed or noncanonical finite description is `format`,
  a capacity failure is `limit` and a failed finite equation is `contract`.
- When `--openqasm-placement-check` rejects a whole packet, the reply keeps
  the ordinary error framing.
- The host uses a valid located form only for diagnostics. The host returns a
  rejection with no resources.

> **Implementation note.** The Main adapter invokes one pure
> `Protocol.NativeContext.run` and its one reply projection. Its checked
> success bindings retain each original gate, the execution or caller
> comparison and the scoped decoded-root property. The common dispatcher
> preserves the profile-specific projection of hierarchy errors. The Rust
> adapter presents a `clean_workspace` or `dirty_workspace` rejection as the
> corresponding restoration obligation, under the existing contract rejection
> category.

## QDV1 byte grammar

QDV1 is a binary format with six kinds of value. Every view in this chapter
is written in it.

An encoding starts with the four ASCII bytes `QDV1`, followed by exactly one
value. A value is one tag byte and its payload:

| Tag | Value | Payload |
| --- | --- | --- |
| `00` | null | none |
| `01` | false | none |
| `02` | true | none |
| `03` | natural | exactly eight bytes, unsigned little endian |
| `04` | text | four-byte unsigned little-endian UTF-8 byte count, then those bytes |
| `05` | ordered array | four-byte unsigned little-endian element count, then each complete value in order |

The grammar has no separate kind of value for a record. A **record** is an
array with an explicit record tag and a fixed order of fields. The profile of
the record supplies that order. The notation `tag(field, field)` in this
chapter denotes such a record.

Rules:

- The grammar has no object keys, floating-point values, aliases, whitespace,
  padding or optional omitted fields.
- Absence is null. Null is distinct from every empty array, empty string,
  false and zero.
- The natural range is `0..18446744073709551615`. A larger value is rejected,
  never truncated.
- Text preserves its decoded Unicode scalar sequence as UTF-8. There is no
  Unicode normalization. A byte count counts UTF-8 bytes, not characters.
- A valid surrogate pair in a source JSON string and the same literal non-BMP
  character yield the same decoded text. A replacement character is
  different. An unpaired surrogate is not an admissible Rust string. When a
  host parser refuses an input conservatively, that refusal does not
  demonstrate that execution diverges.
- The encoder bounds a description to 67,108,864 bytes, including its header.
- The root has depth zero. Depth 128 is allowed, and depth 129 is rejected.
- A view frame must hold exactly one bounded value, with no trailing bytes.
  The native checker rejects a malformed view frame with `format`.
- A capacity failure returns no encoding, and it cannot authorize a view.

For example, in hexadecimal, null is `5144563100`, false is `5144563101`, and
zero is `51445631030000000000000000`. The string `𝄞` is
`514456310404000000f09d849e`.

> **Implementation note.** The framing reader checks exactly one bounded
> value, UTF-8, lengths, depth and EOF without allocating a list from an
> untrusted array count. Neither framing nor encoding is semantic acceptance.

## Typed finite records

The typed finite records describe a finite program and each of its
operations. The views later in this chapter are built from them.

Every row below denotes an array that begins with the quoted tag, followed by
the fields in the stated order. These records describe data. They do not
assert that the data satisfies ownership, effects or a semantic contract.

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
| `structural-compute` | source, source output, scratch wire, forward circuit steps, inverse circuit steps, protected uses |
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

Three fields hold codes:

| Field | Codes |
| --- | --- |
| Gate code | `0,1,2,3` mean H, X, Z, T |
| Phase code | `0,1` mean minus one and an eighth turn |
| Declared effect | `0,1,2` mean unitary, isometry and observe |

Rules:

- IDs, widths, axis indices, table entries, gate codes and phase codes are
  naturals.
- A list is an ordered array. A boolean is a boolean value.
- The `program` record supplies neither the derived effect nor the final live
  ports. The complete production profile requires a separate binding of that
  metadata. The [`finite-graph`](#the-finite-graph-view) record carries both.

### Circuit steps and protected uses

Several records above hold lists of circuit steps, unitary steps or protected
uses. This section gives the records inside those lists.

A circuit step is `step(controls, action)`. Each of its controls is
`control(index, when-one)`. The actions are `hadamard(target)`,
`monomial(indices, permutation, phases)` and
`contract(indices, original-evidence-table-index, adjoint)`.

Unitary steps inside a quantum conditional are `gate(gate-code, target-index)`,
`cnot(control-index, target-index)`,
`toffoli(first-index, second-index, target-index)` and `phase(phase-code)`.
Some raw operations have similarly named tags. The field that encloses a step
distinguishes it from such a raw operation.

Protected uses are `protected-gate(bit, gate-code)`,
`target-gate(controls, target-index, gate-code)` and
`protected-phase(controls, phase-code)`. A protected bit is
`protected-bit(region, index)`. Region zero is the source, and region one is
the ancilla. Each protected control is `protected-control(bit, when-one)`.

### Bases, matrices and exact scalars

These records describe a basis, a matrix and the exact scalars that a matrix
holds.

A basis is its exact preorder list of `unit()`, `bit()`, `bits(width)`,
`pair()` and `tuple(arity)` records. This list preserves zero-width fields,
atomic registers and immediate tuple arity.

A matrix is `matrix(rows, cols, entries)`, with its entries in row-major
order. Each entry is an exact scalar: a four-element array of
`dyadic(numerator-text, exponent)` records in `a,b,c,d` order. The four
records are the ordered dyadic coefficients of
`a + b sqrt(2) + i(c + d sqrt(2))`.

Rules:

- No shape or coefficient is inferred from width. Matrix dimensions and
  row-major entry order are explicit.
- An exact scalar description retains all four coefficients.
- Each coefficient has a numerator and an exponent. The numerator is a
  canonical signed decimal. The exponent is nonnegative, and it is the power
  of two of the denominator.
- Zero has exponent zero. Negative zero, leading zeroes and reducible nonzero
  dyadics are not canonical.
- Exact phase data is bound before it is interpreted numerically. Numerical
  runtime values do not replace exact coefficients.

### Function evidence

The host retains evidence for a function, and a view describes that evidence
as one record. The retained evidence of one function is the record
`function-evidence(signature, implementation, specification, identity, circuit, meaning, depth, expanded-steps)`.
The identity is `identity(implementation-name, specification-name, sources)`
with `source(path, text)` records. The circuit is `circuit(basis, steps)`.

Rules:

- Dependency indices identify original graph entries.
- Process addresses serve only as private lookup keys. They are never
  encoded.
- A missing or ambiguous mapping fails before any bytes are returned.

> **Implementation note.** The Rust retained-evidence walker reads the fields
> of this record from the retained function data. The native checker
> independently derives the execution circuit from its literal implementation
> events. It uses a fresh native receipt for the checked exact matrix, depth
> and expanded-step count. Closed classical branches select events only after
> both arms have been checked. Frame reorderings rename later axes; only the
> final composite permutation is materialized. The production graph and caller
> descriptions include these walkers in the native comparison before retaining
> the same runtime objects for execution.

## The finite graph view

The finite graph view describes what the host retains for a finite program:
its tables of programs and function evidence, and the root that execution
runs.

The mode `--qirf-native` compares the record `finite-graph` in scopes 1 and 2.
The record has eight fields after its tag:

| Field | Content |
| --- | --- |
| 1 | The original root program index |
| 2 | The actual root interface, or null. A present interface is `root-interface(input-basis, output-basis)`. |
| 3 | The ordered source records |
| 4 | All decoded programs in original table order |
| 5 | All fresh function-evidence records in original table order |
| 6 | The actual execution root |
| 7 | The derived effect of that root |
| 8 | The ordered output ports of that root |

Rules:

- The root is described separately from the program table, so that a
  different runtime root cannot borrow the comparison of the table.
- Output ports follow the order in which the program returns them, and they
  include zero-width owners. The order in which the live store inserted them
  is not their order.
- The derived effect is the first of these that applies. It is observing if
  any observing operation occurred. It is isometry if allocation or a width
  change required it. Otherwise it is unitary. A conservative declared
  `observe` effect may therefore have a derived unitary effect. Both fields
  are bound.
- A dependency reference in the full graph uses the original artifact index.
  This holds even when the order of successful checking differs from the
  table order.

> **Implementation note.** The native checker derives the effect from its
> checked observation state. The walker reads fresh graph receipts produced by
> the common checker, never submitted receipts. Finite execution prepares its
> actual graph, dependency caches and root metadata before submission. The
> comparison borrows those exact allocations. Successful binding moves them
> into `AcceptedProgram` without re-decoding.

## The contract view

The contract view describes a contract request together with the graphs that
the request concerns.

The mode `--qirf-contract` compares the record `native-contract` in scopes 1
and 2. The record has three fields after its tag:

| Field | Content |
| --- | --- |
| 1 | The typed request |
| 2 | The actual `finite-graph` |
| 3 | An expected `finite-graph` for instruments, or `null` for the other profiles |

Each of the two graphs includes its original program and evidence tables, its
selected runtime root, its exact cached function data, its ordered
interfaces, its sources and its derived metadata.

The typed request is one of six obligation records: `encoded`, `leaf`,
`pure-leaf`, `control`, `control-owners` or `instrument`. The table below
lists these six records. Its other rows are their components:

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
`pair()` and `tuple(arity)`.

Rules:

- A quantum owner and a classical value are distinct, even at zero width.
- The actual and the expected signatures are described separately.
- Identity preserves names, source order and complete decoded strings.
- The independently decoded expected artifact and the fresh checked roots
  belong in the complete instrument profile. The obligation record alone does
  not bind them.
- The expected graph comes from the reference of the instrument, which is
  decoded independently and checked freshly. This holds even when the owner
  or wire identities of the reference differ from those of the actual graph.
- Neither side serializes the original request JSON as the execution view.

> **Implementation note.** The common native-contract adapter retains its
> decoded original artifact, request bytes and typed obligation for all six
> existing profiles. Encoded contracts retain the freshly checked root,
> reconstructed action and finite wrapper result. Leaf requests retain the
> original ports and exact matrix; pure leaves retain both domain/codomain
> trees and their checked root/action. Control requests retain the exact
> signature or owner forest and ordered axes. Instrument requests retain the
> independently decoded expected artifact and its order, signatures and source
> identity, with both fresh checked roots.

> **Implementation note.** The old adapter results are projections of these
> same computations. The leaf path retains its existing validation sequence.
> No additional acceptance rule, native mode or execution handle is
> introduced. The typed obligation walkers read these retained stages in Lean
> and the actual typed contract/boundary/signature values in Rust.

> **Implementation note.** `CheckedContract.check` invokes the original
> native-contract checker once. It then derives this description from that
> same retained result and compares the canonical bytes inside Lean. Frame,
> error and work plumbing is shared with the pure finite gate. Core work
> finishes before describing the view; the added work is not hidden.

> **Implementation note.** The corresponding Rust walker borrows the actual
> typed obligation and the retained actual/reference runtime graphs. One
> bounded writer accounts for nesting and total storage across all three
> fields. Production uses private unbound staging and moves the compared graph
> into the accepted handle only after native success.

## The caller view

The caller view describes what a caller actually holds: its root program, its
optional interface and the function evidence that it retains. An alias pairs
one retained piece of function evidence with the index of an entry in the
original evidence table. The host proposes that index, and the native checker
compares the alias against the entry.

In scope 2, the modes `--qirf-native` and `--qirf-contract` also compare the
caller view. The record is
`caller-origin(interface-or-null, actual-root-program, aliases)`. Each alias is
`evidence-alias(original-evidence-index, function-evidence)` with the complete
actual function description that [Function evidence](#function-evidence)
specifies. The envelope carries the proposed index of each alias, in the order
of the aliases.

The caller-circuit walker describes the supplied actual `Circuit` as
`circuit(basis, steps)`. It retains literal controls, phase tables and axis
order. It also retains the actual dependency references, mapped to original
indices. It does not use the synthetic single-action wrapper that the
encoded-contract checker constructs. The QLV3 caller scope also binds the
actual circuit steps and retained caches.

Rules:

- The canonical snapshot map of the original encoder proposes each index.
  That lookup is not evidence that the actual body, matrix, circuit or
  descendants equal the fresh result of the native checker.
- Distinct actual caller aliases are permitted to carry the same index. A
  missing receipt is refused.
- Repeated references to one Arc retain one entry. Distinct Arcs retain
  separate entries even when their snapshot keys are equal.
- Private addresses identify objects during discovery and are never encoded.
- A missing original snapshot mapping is refused. The collector cannot
  manufacture an evidence-table entry from a cache.
- The two QDV1 descriptions together must fit the existing 64 MiB ceiling. A
  supplied lower byte limit cannot raise the fixed ceiling.
- Exhausted work or capacity, malformed framing, missing receipts and
  divergent data are distinct refusals.

> **Implementation note.** The caller collector retains the supplied root
> program and its optional interface. It also retains every distinct actual
> `Arc<FunctionEvidence>` that is reachable through implementation bodies,
> specification bodies and cached circuit steps. It walks both complete
> classical branch arms and both certified use/logical step lists. One shared
> discovery counter charges operations, circuit steps and distinct Arcs
> against the existing 1,000,000-node transport capacity. Description
> construction uses one writer with the existing total-byte and depth limits.

> **Implementation note.** This extra traversal is necessary because the
> artifact encoder returns early when it finds an equal snapshot. That encoder
> registers the directly encountered Arc but need not visit the distinct child
> Arcs of that alias. Describing only the fresh Rust-decoded artifact, or
> consulting only the direct pointer map of the encoder, would omit actual
> caller caches.

> **Implementation note.** `Caller.alias` reads the fresh receipt at the
> supplied original evidence index and independently derives its complete
> function description. `Caller.origin` describes the same checked root and
> original interface, then every supplied alias in order. It accepts no host
> snapshot, matrix or receipt as proof. It precharges the alias list and
> retains the existing node ceiling.

> **Implementation note.** `CheckedCaller.finite` and `CheckedCaller.contract`
> each call their existing finite or complete-contract comparison gate exactly
> once. They then attach the caller comparison to that exact returned
> artifact and root. The latter covers all six contract kinds. The pure Lean
> attachment compares each emitted alias against its proposed original entry.
> Native QLV3 caller requests invoke this attachment before issuing an
> execution handle from the compared descriptions.

> **Implementation note.** The byte length of the base description is reserved
> first. Caller construction encodes the empty alias-list prefix. It then
> counts each additional alias value without its four-byte QDV1 header before
> retaining it. It therefore bounds repeated large descriptions before
> accumulating the final tree. Accumulation uses cons/reverse, preserving
> order without quadratic list append.

<a id="hierarchy-plan-records"></a>

## The hierarchy plan view

The hierarchy plan view describes the plan that the hierarchy runtime
executes. The six hierarchy modes compare the record `hierarchy-plan` in
scope 1. Each mode reads its own kind of original payload:

| Mode | Original payload |
| --- | --- |
| `--hierarchy-pending` | A hierarchy artifact for inspection |
| `--hierarchy-request-pending` | An independent root request |
| `--hierarchy-control-pending` | A root request with source control obligations |
| `--hierarchy-fourier-pending` | A named Fourier request |
| `--instrument-pending` | An instrument |
| `--qpe-instrument-pending` | A named QPE instrument |

The plan records reuse the byte grammar and the exact `matrix` record above:

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

The two instrument modes compare an `instrument` record. The other four modes
compare a `pure` record.

Rules:

- All definitions participate. This includes a child that nothing uses and a
  child that is repeated zero times.
- A structural operation becomes the actual coordinate permutation that the
  runtime consumes.
- Literal phase parameters are retained as they stand before numerical
  evaluation. For example, `j = 9, k = 3` is not replaced by `j = 1, k = 3`.
- Preparation positions use the input axes of the circuit. Outcome and
  residual positions use its output axes.
- Measurement order and pack order are separate fields.
- Classical result ports stay in the checked artifact, even though the runtime
  stores its quantum residual coordinates separately.
- A QPE plan uses the original circuit entry, rather than the provider entry
  used for its independent request.
- For pure source `ctrl` calls, the `QLR2` request carries ordered original
  owner basis trees and control roles for each replayed call node. The
  `--hierarchy-control-pending` mode requires an execution view. It checks
  these obligations in the same invocation as composition and plan
  comparison. A successful response identifies that mode explicitly.
- An inspection without an execution comparison is a different result from
  one that is capable of execution. Unsupported execution therefore cannot
  narrow inspection.

> **Implementation note.** Each call obtains one fresh structural result,
> reconstructs the actual finite leaves of that result and checks its
> independent pair/H obligations under the same exact-work allowance. The plan
> then derives from those exact retained matrices and the original typed
> packet, including actual preparation and readout. The native checker derives
> this description independently from the typed hierarchy and exact finite
> reconstructions. `CheckedHierarchy.checkInspect` runs the original
> structural checker once, reconstructs its actual finite obligations, derives
> the view from those same results and compares inside Lean.

> **Implementation note.** The `CheckedHierarchy.Modes` gate also retains the
> original fresh checks for independent root requests, their source control
> obligations, named Fourier, instruments and named QPE instruments. The QLV3
> CLI dispatches to these gates with a mandatory execution view when
> execution is requested. Production Rust describes and retains the same plan;
> the walker itself confers no acceptance.

> **Implementation note.** The Rust hierarchy walker describes the owned plan
> actually read by execution and sampling. It does not call the hierarchy JSON
> or bridge writer. The Rust hierarchy runtime materializes one owned
> execution plan before the fresh native decision. Native-only and
> finite-reconstructed reports retain that same allocation, or its explicit
> materialization failure. Inspection makes the original native decision;
> unsupported execution cannot acquire a replacement plan or change that
> decision. Public payload/request access is immutable. Production QDV1
> integration compares this same plan before granting execution authority;
> preparation and retention alone do not perform that comparison.

> **Implementation note.** Hierarchy reports retain the same boxed plan
> prepared before the fresh native check. Each execution mode compares that
> plan, including exact finite descriptions and ordered preparation/readout
> coordinates. A failed plan or description is retained as an execution error
> while explicit inspection stays available. No report can lazily replace it
> with an unchecked plan. Compatibility reports additionally keep freshly
> checked finite-leaf handles.

> **Implementation note.** Pure plans retain original node order, child
> indices, width, root and ordered input/output axes. Finite leaves own their
> exact matrices. A phase node retains the literal target position and integer
> `j`/`k`; conversion to numerical sine and cosine occurs only during
> interpretation. Phase normalization and numerical values are not substituted
> for those exact parameters in the retained plan.

> **Implementation note.** Instrument plans additionally retain input and
> fresh axes, preparation input positions, measurement value/axis pairs in
> order, pack order, outcome positions and residual axes/positions. Execution
> borrows this plan and creates fresh state and work buffers. Every sampling
> shot borrows that same plan and starts from the same normalized joint
> input/reference state. It does not reparse the JSON, recompile nodes, reuse
> collapsed state or cache an earlier branch execution.

## The carrier view

The carrier view describes a graph together with two interfaces and one
logical matrix. The internal mode `--carrier-pure-check` requires execution
scope. It compares the QDV1 record `finite-carrier-pure-v1`, which has four
fields after its tag:

| Field | Content |
| --- | --- |
| 1 | The actual graph |
| 2 | The attached interface: its ordered input and output owner forests and its public effect |
| 3 | The required interface, with the same parts |
| 4 | The exact logical matrix |

Rules:

- The result of this mode is a private component result. It grants no
  ordinary source execution and no source-preservation claim. The
  [carrier boundary](production-boundary.md) states the checked equations and
  the open obligations.

## The ordinary root view

The ordinary root view describes one selected function of a graph, with its
inputs and its result. The internal mode `--ordinary-root-check` requires
execution scope. It compares the record `finite-ordinary-root-v2`, which
contains these fields after its tag, in order:

| Field | Content |
| --- | --- |
| 1 | The actual graph |
| 2 | The project, exported or internal selection |
| 3 | The original module |
| 4 | The original function |
| 5 | The ordered parameter basis forest |
| 6 | The input storage forest |
| 7 | The complete input rows |
| 8 | The full result basis |
| 9 | The result storage tree |
| 10 | The public effect |

Rules:

- An inspection packet, a caller packet or an old-mode retry cannot authorize
  this mode.
- This checking of ordinary inputs and results supplies no preservation
  theorem for the original body or for the numerical runtime. See the
  [ordinary-result boundary](production-boundary.md#ordinary-inputresult-requests).

> **Implementation note.** The native checker freshly reads the original
> signature and independently enumerates its complete canonical input domain.
> It requires exact row equality. It checks each typed input and every
> complete exact instrument history before comparing this description. The
> retained Rust program keeps the same graph and typed request objects.

## The engineering OpenQASM view

The engineering OpenQASM view describes a literal OpenQASM target together
with the ideal graph that the target is compared with.

The separate mode `--engineering-openqasm-check` accepts execution scope only.
Its original QLV1 body is the literal canonical OpenQASM byte array. Its
request is the closed engineering instrument contract that
[realization](realization.md#literal-openqasm-target-comparison) describes.
Version 1 of that request has fourteen fields. Version 2 has fifteen: it adds
`resource_limits`.

The outer QDV1 record `engineering-openqasm` has five ordered fields:

| Field | Retained data |
| --- | --- |
| 1 | Typed engineering request, including complete signatures, identity, epsilon and ordered majorants |
| 2 | Literal target bytes as an array of natural byte values |
| 3 | Ordered decoded gate-name strings |
| 4 | Complete generated actual graph, including its explicit Unit owner, unpack, initialization, terminal measurement and Observe effect |
| 5 | Complete original ideal graph and its fresh dependency checking results |

For version 2, the typed request of field 1 ends with a `resource-limits`
record: the model name, the gate limit and the T-gate limit.

Rules:

- A stale word, graph, full type, identity or budget is refused, even when the
  submitted original is individually valid.
- The private report authorizes only the declared engineering inequality. It
  authorizes none of these, even at epsilon zero: simulation, source/export
  preservation, control, exact cleanup or resources.
- The existing work and size limits of the envelope and the view apply. The
  target profile separately limits bytes and gates.

> **Implementation note.** The native checker independently decodes the same
> target bytes and the ideal QIRF, and checks their complete instruments and
> bound. It derives this view from that same result and compares exact bytes.
> The Rust actual graph is retained data, without an accepted-program
> constructor or fallback.

<a id="internal-named-arm-qmatch-component"></a>

## The named-arm qmatch component view, version 4

This view serves an internal component that checks one source function whose
`qmatch` selections use named arms. The request names the function, the
position of each source event and the sites of the selections.

The internal mode `--qmatch-source-check` reads a strict internal
`qleisli.qmatch-request` version 4 with profile
`finite-source-qmatch-context-v4`. This section specifies version 4 only.
[Status and limits](#status-and-limits) lists version 5 among the formats
that this chapter does not specify.

### The version-4 request

The request has exactly these keys: `format`, `version`, `profile`, `source`,
`positions` and `sites`. The first three hold the values above.

| Key | Content |
| --- | --- |
| `source` | The original `module` and `function` |
| `positions` | One literal interval for every supported source event |
| `sites` | 1–128 ordered sites. Each contains `attached`, `required`, `position` and `arms`. |

The two interfaces of a site, `attached` and `required`, use the existing
complete carrier codec. `position` contains the original UTF-8 byte `offset`
and the literal Raw operation `start` and `count`. Each arm contains an actual
original function-`evidence` index and a separate `controlled` program index.

Rules:

- Versions 1–3 are refused without fallback.
- Indices are u32, names contain 1–4096 UTF-8 bytes and the arm list contains
  1–64 entries.
- The request contains no logical matrix, label list, graph roots or success
  flag. Labels, names, types, effects and graph subjects are determined by
  reading the original source afresh. The shared Raw/nominal equations check
  the actual bodies.
- Each pair of interfaces describes its selected pair in selector/target
  order. The graph retains the parameter and result order of the complete
  original function, including additional zero-width owners. Fresh
  original-source moves bind those two orders; equal widths or an arbitrary
  interval cannot replace that judgment.
- `positions` contains one literal interval for every supported source event.
  This includes direct `h`, `global_phase_eighth` and supported `phase[j,k]`
  calls and every selection.
- There is no separate 128-event cap on this array. The existing byte and work
  limits apply, and the selection count is bounded by 128.
- Every original event must appear exactly once in evaluation order. The
  literal intervals cover the complete Raw operation list, with no overlap
  and no gap. Each interval uses its actual surrounding owner frame.
- Primitive intervals check the exact specified action. Selections use fresh
  arm/control evidence and exact sector equations. Cancellation between
  intervals cannot hide a wrong local operator.
- The outer public effect is bound independently of the pure selected pairs.

### Source events and coordinates

These rules say how the source events of the function are read from the
original source, and which source coordinate each event has.

Rules:

- Static parameters are read from original tokens and the actual lexical
  static environment. The request supplies neither their values nor a success
  receipt.
- A static initializer that is local to the body is checked even when it is
  unused. It emits no Raw interval of its own.
- Each phase call retains its distinct literal interval after evaluation of
  its runtime argument.
- Arguments are traversed before their enclosing call. The coordinate of a
  call is its first callee token, and the coordinate of a selection is its
  `qmatch` keyword. Grouping parentheses and comments do not replace either
  coordinate.
- Primitive resolution checks original lexical/module bindings and, when
  enabled, the original `std::prelude` row. A primitive name that the
  producer supplies is not sufficient.

### The version-4 view record

The QDV record contains the tag, which is the profile name, followed by four
fields:

| Field | Content |
| --- | --- |
| 1 | The complete fresh finite graph |
| 2 | `["source-function", module, function]` |
| 3 | The ordered event-position array. Each event position is `["source-interval", offset, start, count]`. |
| 4 | The ordered site array |

Each site is
`["qmatch-site", attached, required, ["source-interval", offset, start, count], arms]`,
where `arms` is an ordered array of `["qmatch-arm", evidence, controlled]`.

Rules:

- The pure QLV3 definition requires execution scope and exact bytes.
  Inspection, caller and malformed frames are refused.
- The complete proposed graph order supplies no reachability permission.
  Independent subject checking rejects unrelated nodes and source rows.
  Ordinary graph checking retains its main-only roots.

> **Implementation note.** The preparatory `Protocol.Qmatch` and
> `ExecutionView.CheckedQmatch` definitions implement this request and its
> comparison. The paired `--qmatch-source-check` mode requires this
> execution-only comparison and the product/edition context of the
> invocation. The Rust proposal roots come from the original main, actual
> requested evidence entries and controlled program indices. The Rust walker
> borrows the exact retained graph and typed request; it does not replay the
> QIRF JSON encoder.

> **Implementation note.** Fresh success retains those same allocations in a
> private `QmatchChecked` component. It has no public ordinary-program
> conversion, inverse/control capability or receipt constructor, and performs
> no old-mode retry. The shared ordinary/selected emitter also requires
> separate whole-root runtime acceptance after this component succeeds.

## Walkers and the comparison

This section says what data a walker reads and what the comparison gate does
with the two views. QLV3 connects the walkers and the pure Lean gates to the
production native entry points. The rules below apply to every profile.

Rules:

- A profile walker must inspect the typed data that is actually retained,
  independently of the existing QIRF JSON encoder and of the hierarchy bridge
  writer. It must not merely copy original JSON fields or serialize a
  surrogate view that execution discards.
- Inside Lean, the production gate compares two things: the submitted
  encoding of the actual view, and the view that the native checker decodes
  and derives. A well-framed mismatch rejects with `decoded_view`. Missing or
  malformed data and unsupported protocol versions reject separately.
- The primitive byte grammar grants no authority by itself. The typed profile
  walkers and the fresh comparison gates are required. Encoding success is
  never a fallback acceptance decision.
- Constructing a candidate can need a private inspection. Such an inspection
  must not expose an accepted execution handle.
- After successful comparison, execution must retain the same immutable
  decoded/compiled data, rather than decode again.
- Tests must mutate actual view fields while the original artifact stays
  natively valid.

The record schemas and the shared vectors of the walkers must cover:

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

> **Implementation note.** `ExecutionView.CheckedFinite.check` is the pure
> finite comparison gate over an original packet and a mandatory candidate
> view. It checks QDV1 framing, decodes the original artifact/request and runs
> the common typed QIRF check once. It derives the view from that same fresh
> result, encodes it and compares exact byte arrays inside Lean. It
> distinguishes `invalidView`, packet errors, native checker errors, encoding
> failures and `decodedView`.

## Status and limits

### Limits

This table collects the limits that the sections above state.

| Limit | Value |
| --- | --- |
| Complete QLV3 envelope | 64 MiB |
| Graph view and caller view together | 67,108,864 bytes, the QDV1 byte limit |
| Alias count of an envelope | 100,000 |
| One QDV1 description, including its header | 67,108,864 bytes |
| Depth of a QDV1 value, with the root at depth zero | 128 |
| QDV1 natural | `0..18446744073709551615` |
| Caller discovery of operations, circuit steps and distinct Arcs | 1,000,000 nodes |
| Sites of a version-4 qmatch request | 1–128 |
| Arms of a version-4 qmatch site | 1–64 |
| UTF-8 bytes of a version-4 qmatch name | 1–4096 |

- The QDV1 limits are capacities of the transport. They do not certify the
  quantitative resources of a program. The caller limits are bounds of the
  host transport. They do not certify quantitative quantum resources.
- The budgets for repository fixtures and for pull requests are configured
  separately. They are unchanged.

### Formats that this chapter does not specify

The native checker compares each of these views. This chapter does not specify
their records. For each one, the table names the file of
`lean-kernel/Protocol/` that defines it.

| Mode | View or packet | Lean definition |
| --- | --- | --- |
| `--runtime-root-check` | `finite-runtime-root-v2` | `ExecutionView/CheckedRuntimeRoot.lean` |
| `--qmatch-source-v5-check` | The version-5 `qleisli.qmatch-request` and its QDV records | `QmatchV5.lean` and `ExecutionView/QmatchV5.lean` |
| `--engineering-pure-check` | `engineering-pure` | `ExecutionView/EngineeringPure.lean` |
| `--engineering-pure-tensor-check` | `engineering-pure-tensor` | `ExecutionView/EngineeringPureTensor.lean` |
| `--qirf-engineering-instrument-native` | `engineering-instrument` | `ExecutionView/EngineeringInstrument.lean` |
| `--engineering-openqasm-gate-check` | `engineering-openqasm-gate` | `ExecutionView/EngineeringOpenQasmGate.lean` |
| `--openqasm-placement-check` | The placement packet, which nests the envelope | `ExecutionView/CheckedQmatchV5.lean` |

The [production boundary](production-boundary.md) states the requests and the
proof scope of the
[runtime root](production-boundary.md#mixed-runtime-root-requests) and of the
[qmatch component](production-boundary.md#named-arm-qmatch-component-requests).

### Limits of the version-4 qmatch component

- The version-4 source component uses named arms in complete structural
  quantum functions. This includes multiple selections, grouped or nested
  direct supported primitive calls, source moves and distinct zero-width
  spectators.
- The shared compiler records built-in selected pairs too when a nominal
  owner activates this function context. Direct primitive arms require named
  wrappers in that context.
- General expression/call frames, mixed ordinary parameters,
  constructed/static/generic arms and the complete twelve-bit profile require
  integration. These are implementation limits.

### Binding theorems

A binding theorem ties the result of a gate to the data and the computations
that produced it. The Lean proofs below cover these gates.

- `check_binding` of the finite gate retains three things. The first is the
  original packet/body/request. The second is the actual decoded graph and
  checking computations. The third is the equality of the candidate with the
  exact encoding of the view of that result.
  `Binding.original` transports that success to the existing ordinary packet
  acceptance witness before view derivation. `check_ownershipSafe` and
  `check_scopeSafe` concern the same original selected root. View derivation
  has a separate value of work left. These proofs do not claim unchanged
  whole-gate work or serializer/runtime correctness. This is technical
  preservation support, not an added admitted constitutional guarantee.
- For the retained contract stages, universal Lean equalities preserve
  successes, errors and the work left. Stage binding theorems identify the
  retained core results.
- `NativeContract.checkRetained_bound` additionally ties every returned field
  to the original packet body/request, UTF-8 text, parsed JSON, decoded
  artifact/order and the exact returned request-stage result. Its work state
  runs continuously from artifact decoding to the existing six-kind dispatch.
  This binding of output fields is separate from `checkRetained_acceptance`.
  That theorem has the original existential acceptance witness, which does
  not by itself identify every field of the returned record. Neither theorem
  establishes an execution-view match or runtime preservation.
- The binding theorem of `CheckedContract.check` retains the exact returned
  record, original-packet field binding, comparison and continuous work
  states.
- The universal binding theorem of `Caller.alias` identifies the exact receipt
  slot at the supplied index and the derivation of its function description.
- The binding proofs of `CheckedCaller.finite` and `CheckedCaller.contract`
  preserve the actual base computation, caller derivation, compared encoding
  and continuous work states. The binding of original bytes and of
  ownership/scope, or the binding of the fields that the native contract
  returns, is inherited from that same base execution.
- `HierarchyView.reconstructLeaf_bound` connects each returned matrix to the
  original description decoding and original-body check in that computation.
  `checkInspect_binding` retains the original bridge, typed artifact,
  structural result, exact matrices, continuous exact-work states and compared
  bytes.
- The binding theorems of the `CheckedHierarchy.Modes` gate retain the
  original packet, actual finite matrices, independent pair/H checks and
  comparison with the plan derived from those same objects.

### Tests and fixtures

The items below say what each set of tests and fixtures checks.

- The [shared vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/canonical-vectors.json)
  fix type distinctions, unsigned width, endian order, nested array order,
  NUL, non-BMP/replacement characters and composed/decomposed text.
- The [finite vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/finite-walker-vectors.json)
  include three retained observing source roots and 21 of the 22 Raw
  constructors: every constructor except `StructuralCompute`. They also
  include both branch arms, zero-width owners, exact type trees and
  rectangular matrices. The combined all-constructors row is intentionally
  transport data, not an accepted quantum program. Rust and Lean read their
  own typed data and compare against these independently specified
  descriptions. This checks the walkers. It does not check execution binding
  or a source/runtime preservation theorem.
- The [function-cache vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/function-cache-vectors.json)
  add ten independently specified full retained-evidence descriptions. They
  cover Unit ownership, H–T–H exact coefficients, output permutations, branch
  routes that compose or cancel, certified/protected ancilla phases, quantum
  conditional phase and a dependency with an adjoint. Rust checks actual
  retained function data. Lean freshly checks the original bodies and derives
  its own cache view.
- Dependency zero in the last function-cache row identifies the first corpus
  entry. The test remaps actual retained Arc references to that explicit
  corpus index. This indexing belongs to the test. It is separate from the
  production graph mapping, which uses original indices.
- The [graph vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/finite-graph-vectors.json)
  retain three original observing sentinels and add Unit interfaces, ordered
  mixed-width output ports, conservative effects and an evidence table whose
  first entry depends on its second. These are bounded transport comparisons;
  the native QLV3 regression separately exercises their production binding.
- The [contract vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/contract-walker-vectors.json)
  check all six obligation kinds and two literal caller circuits. Lean freshly
  checks each original native request before walking its retained obligation;
  Rust describes independently constructed typed values. Data mutations
  distinguish encodings, phase, both ports, equal-width type trees, source
  identity and axes. The [authoring record](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/README.md)
  describes both preserved refusals and their corrections.
- The [complete-contract vectors](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/complete-contract-vectors.json)
  retain eight independently authored graph descriptions covering every
  contract kind and an observing reference with distinct owner/wire
  identities. The pure Lean gate refuses 1,152 individual scalar, empty-list
  and array-shape mutations over these valid original requests. The Rust tests
  also refuse missing or unexpected reference graphs. These pure checks are
  separate from the QLV3 native regressions and from the caller and hierarchy
  bindings. The walker alone issues no execution handle or constitutional
  guarantee.
- The [caller recipes](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/caller-alias-recipes.json)
  specify four complete descriptions independently of the walkers. They are a
  repeated Arc, a separate equal clone, equal independently checked parents
  with distinct child Arcs, and references in the certified use/logical
  circuits of an unselected branch. These tests add no production acceptance
  authority.
  Private unbound staging and hierarchy execution are checked separately
  through the QLV3 native entry points.
- The [original branch refusal](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/first-caller-branch-refusal.json)
  retains the first invalid phi wire and real diagnostic. The regression
  rechecks that native refusal before exercising the corrected fresh-wire
  case.
- The four caller recipes also specify original artifacts and complete graphs
  independently of the walkers. Rust checks exact original serialization and
  the actual retained runtime graph. Lean checks the hand-authored caller data
  through finite and native-contract attachments, including nonempty aliases;
  all six contract kinds also have their existing independent request
  controls. Mutations keep each native-valid original fixed and change only
  the supplied description or proposed alias indices. Exact and one-byte-short
  capacities exercise repeated-description accounting without large quantum
  instances.
- The independent small-system harness of the hierarchy runtime compares 19
  original cases and 912 complex coefficients, plus 768 seeded outcomes from
  three clients. Before/after records retain identical original
  artifacts/requests and source hashes; coefficient errors, work counts and
  outcome counts are unchanged. Private fault injection also checks that
  execution retains its original plan after old transport/leaf storage is
  poisoned. Hand-authored controls separately retain literal phase parameters
  and nontrivial preparation/readout/reference coordinates. These tests
  establish bounded regression evidence, separately from native plan
  comparison, source/runtime preservation or a further constitutional
  guarantee.
- Four shared hierarchy cases fix a freshly checked H hierarchy, every runtime
  node kind, reordered preparation/measurement/pack coordinates and a
  classical result port. Three cases are explicitly untrusted materialization
  controls; they do not claim accepted hierarchy or instrument semantics. The
  valid H original also rejects 112 separately mutated, well-framed candidate
  descriptions, with malformed-frame and exhausted-work controls. The native
  and compatibility reports of Rust describe the same retained H plan even
  after private fault injection poisons old transport storage.
- The [five-mode comparison record](https://github.com/MGYamada/Qleisli/blob/51be9c8417c7ff7811d073c08bf43ec2ab17aa4d/tests/fixtures/verification_v030/execution-view-binding/hierarchy-mode-validation.json)
  uses actual retained Rust plans from five small native-accepted inputs. It
  covers every hierarchy mode except `--hierarchy-control-pending`. It rejects
  2,683 individual description mutations while fresh inspection of each
  original succeeds. Three invalid original requests separately exercise
  independent finite-pair phase checks and the named-QPE phase-fixed H check.
  This is bounded cross-implementation evidence; the generated graph/request
  structures are not independent source semantics.
- The shared runner of the pure finite gate checks seven independently valid
  original artifacts against their correct views and against 71 divergent
  candidates. The candidates include every graph field and retained
  evidence-cache fields. The runner separately covers malformed frames,
  native work refusal and an original optional request. These are tests of
  the pure comparison gate.
- The QLV3 native tests separately check the finite, complete contract and
  caller paths and five of the six hierarchy modes: every hierarchy mode
  except `--hierarchy-control-pending`. They include valid original inputs
  with divergent views and rejection of old external frames.
  `tests/selected_source_cli.rs` exercises `--hierarchy-control-pending`
  through the selected-entry route with the Selected hierarchy profile.
- The shared conformance vectors of the version-4 qmatch component separately
  test the retained Rust walker and the fresh native comparison. They do not
  establish native executable attestation, source-body lowering preservation
  or Issue completion.

### What the comparison does not establish

A successful comparison shows that two descriptions are the same bytes. It
does not show the items below.

- The gate checks every alias that the collector emits. That the collector
  corresponds with all objects that execution actually consumes is an
  assumption of runtime preservation. The binding proofs do not prove the
  Rust collector or admit a constitutional guarantee.
- The comparison does not prove that these are faithful: Rust view
  serialization/materialization, native compilation, IO and runtime,
  numerical interpretation and source lowering. Each is an explicit proof
  duty.
- Hierarchy bridge comparison alone does not prove correspondence to the
  original external JSON or source.
- The ordinary ownership and classical-scope guarantees must stay connected
  through the pure gate to the actual QLV3 native protocol entry point by
  checked proofs. Retaining old theorem names or hashes is insufficient.
- QDV1 introduces no reference meaning, constitutional interpretation,
  guarantee admission, full QS/PR/RS/EXACT discharge or release approval.
- Edition alone identifies neither a checker implementation nor a completed
  constitutional proof.
- This wire contract is not a release or a broader proof claim.

## History

- This chapter is the implementation contract for
  [#362](https://github.com/MGYamada/Qleisli/issues/362).
- The #255 cutover extends #362 with `QLV3` as the external native envelope.
  The production cutover rejects old native request/reply frames: old external
  QLV2/QLV1 requests and old replies reject without compatibility retry.
- The #255 migration requires complete helper, ecosystem, current-evidence and
  CI validation before completion.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
