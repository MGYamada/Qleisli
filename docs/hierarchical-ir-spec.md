# Selected bounded hierarchy and evidence profile

Status: **M2 architecture/profile adopted; component implementations in progress**.
The [M1 extension](next-minor-spec.md) is separate. This document fixes the
bounded IR/evidence contract for sized source and generalized APIs; it does not
enable the complete production profile.

New executable acceptance belongs in the [Mathlib-free Lean kernel](lean-kernel-migration.md).
Separate Mathlib proofs interpret those actual definitions. The
[rule inventory](rule-inventory.md) records component coverage, proofs and saved
validation; the [component manifest](../lean/README.md#component-registry-review)
pins declaration types and sources. Rust remains production-authoritative until
explicit migration gates transfer it. All external schema entries stay disabled;
remaining rules, source preservation and R14/H1–H5 remain open.

The subsequent [interoperability direction](interoperability-roadmap.md) places
QIR/OpenQASM target lowering below this semantic/evidence layer and adds external
frontends that still submit untrusted IR. It neither replaces this hierarchy
with LLVM IR nor establishes H1–H5 by adding a file converter.

The **[desugaring layer](terminology.md#desugaring-layer)** translates convenience
forms into already specified core operations without adding primitive meanings
or checker rules. Its output is untrusted and independently checked. In this
future profile, desugaring may target the specified hierarchy; it need not
expand shared calls or repetitions into flat gates. The [coefficient-domain
recommendation](coefficient-domains.md) is a further design direction, not new
nodes, arithmetic domains or acceptance rules for this versioned profile.

## Scope and representation

Select `qleisli.hierarchical-ir` version 1 with profile `qpe-dyadic8-v1`.
The outer serialization follows the strict JSON, integer, duplicate-key and
bounded parsing rules of [the machine interface specification](machine-interface-spec.md).
Its root fields are `format,version,profile,definitions,meanings,encodings,
proofs,entry`. References are u32 array indices. Each shared table is a DAG;
reject cycles, out-of-range references, unreachable entries and unknown nodes.
Do not accept current QIRF under this format by changing only its header.

An interface is an ordered list of `(owner,type,axes)` quantum slots and ordered
classical slots. Types preserve Unit nodes, tuple arity and nested structure,
following the [0.2.0 type specification](type-system.md); a flat triple is not
an implicit binary association. The initial source plan's left-fold rule was
superseded by the 2026-09-29 decision. The new
finite `Bits(n)` shape retains its declared n and little-endian axis order.
`Bits(0)` is a zero-wire owner, not no owner. Define its basis as integers
0≤x<2^n, bit k carrying 2^k. All quantum slots occur exactly once at input/output
unless the node's specified effect consumes/creates them. Axis permutations
are explicit bijections; wire IDs or dimension equality cannot identify trees.

Port maps point from destination positions back to source positions. Their
owner and classical arrays cover every corresponding destination slot exactly
once, including zero-width owners. The axis array covers the concatenated
destination axes in slot order and each slot's declared little-endian order.
All three arrays are bijections onto the complete source positions. A mapped
slot has the identical full type tree; mapping its ordered axes must yield
the source slot's ordered axes. Local owner/value/wire IDs are labels rather
than map indices. Calls additionally require consistent fresh renaming across
their input and output maps; a valid single-side map alone does not check that
cross-boundary condition. Splitting or regrouping typed slots requires the
separate explicit structural conversion contract, not this map operation.

A definition is `{interface,effect,body}`. `interface` has inputs/outputs,
including classical slots; `effect` is unitary/iso/observe; `body` is a node
with exactly the fields below. Children refer to definitions, so sharing is
real. Static parameter substitution happens before this per-size artifact is
emitted; a definition contains concrete bounded integers and dependency refs,
not executable host expressions. The source compiler may share a parameterized
family template but must emit checked instantiations in the artifact. This
profile makes no claim of accepting unbounded type-level arithmetic.

### External field encoding and reconstruction host

An interface is exactly `{inputs,outputs}`; a side is `{quantum,classical}`.
Quantum ports are `{owner,basis,axes}` and classical ports `{value,basis}`.
`basis` is a prefix array of `{tag:"unit"}`, `{tag:"bit"}`,
`{tag:"bits",width}` or `{tag:"tuple",arity}`. This retains complete tree
shape and zero-width owners. Node and rule objects use a `tag` field plus
exactly their listed operands; effects and table names are lowercase strings.
Meaning records are `{interface,body}`; encodings are `{logical,physical,body}`.
Port maps are `{owners,axes,classical}`. A structural operation is a tagged
object; `take_bit`/`put_bit` carry `width,position` and the other forms have no
operands. Proof witness fields are `{template_version,parameters,references}`,
with references `{table,index}`. A schema rule additionally has `id`.
The entry is `{implementation,proof}`. All numeric wire fields are u32.

Finite `program` and `description` fields are JSON strings whose decoded UTF-8
bytes contain the complete QIRF and exact finite matrix description. Their
embedded whitespace is preserved. Parsing the outer string does not execute
or validate its contents. Every object rejects unknown, missing or duplicate
fields; no evidence flag, cache or replacement theorem is a valid field.

The additive [Rust reconstruction host](../src/interchange/hierarchical.rs) first decodes this external data and
proposes a dependency schedule. A fresh invocation of the selected audited
Lean runtime receives the complete artifact over a private bounded binary
bridge and runs the actual `Conditional.checkAll`. It returns pending finite
proof indices, never a serialized evidence handle. The host projects each
index from the same retained immutable artifact and freshly checks its complete
finite program, meaning and required boundary with one shared exact budget.
It retains both outer artifact bytes and reconstructed leaves.
`Kernel::new(executable)` selects the trusted native dependency explicitly;
`Kernel::inspect(payload)` invokes that executable afresh and accepts no
caller-supplied runtime response. Process I/O is bounded, with a 60-second host
deadline and at most 1,100,000 response bytes. Failures return no partial
`Reconstructed` report. The public report exposes retained bytes, checked leaves
and structural/exact work, without a `VerifiedProgram` conversion.

This inspection result does not establish an independently requested root
contract and is not a production `VerifiedProgram`. All external schema rules
remain disabled. The remaining profile and production integration must be completed
before production hierarchy acceptance. The private bridge uses length-prefixed
little-endian u32 fields and byte strings, a 64 MiB framing bound and one million
bounded reads. It adds no external capacity or checker rule. Its decoder and
native compilation remain explicit correspondence obligations outside the pure
kernel. The [host packet](../tests/fixtures/hierarchical_ir/host-packet.md)
records the independent reconstruction and mutation experiment.

### Independently requested roots

A separate version-one request is exactly
`{format:"qleisli.hierarchy-request",version:1,profile:"qpe-dyadic8-v1",
kind,effect,interface,meanings,entry}`. It uses the same complete interface,
meaning and scalar formats; `entry` indexes the request's own meaning table.
The caller supplies this required contract independently. Artifact annotations
must never populate missing request fields or replace them. The physical root
interface/effect and actual proof kind must match the request exactly, including
all owner/value IDs, axis order, type trees and empty owners.

The root matcher compares a rooted graph of actual/requested node pairs.
Table numbering and sharing may differ in either direction. Every pair checks
complete interfaces, the constructor and all non-reference parameters, and
corresponding ordered children. The proposed pair graph must be acyclic, rooted
at pair zero and completely reachable, and cover the complete requested table.
Pair zero must name the actual entry proof's meaning and requested entry.
Checking consumes the same two-million-unit structural allowance as artifact
checking. No arbitrary algebraic normalization, implicit type conversion or
change in operation order is admitted by root matching.

Finite meaning pairs retain both complete description byte strings. They
create explicit obligations for equality of their independently decoded exact
matrices, allowing different JSON whitespace without dropping scalar phase.
The host discharges every obligation under the same ten-million-unit exact
budget as finite implementation reconstruction. The mathematical theorem stays
conditional on the existing finite-reader/Rust correspondence. A valid artifact
whose implementation and declared meaning were changed together still fails a
different independently requested contract. The [root-request packet](../tests/fixtures/hierarchical_ir/root-request-packet.md)
records the checking and proof experiment.

The additive `Kernel::check_against(payload, request)` now implements this path
for the supported conditional profile. Rust proposes the node pairs; the pure
[Root.checkAll](../lean-kernel/QleisliKernel/Hierarchical/Root.lean) independently
checks their complete structure and the original artifact. The private `QLR1`
message embeds the unchanged `QLH1` artifact and adds the complete request,
pair table and schedule. `--hierarchy-request-pending` returns finite proof and
meaning-pair indices. Rust freshly reconstructs every obligation, rejects
missing/duplicate indices and retains both original inputs in a private
`CheckedRequest`. Its 60-second process deadline and 64 MiB framing limit are
unchanged; the two index lists permit at most 2,200,000 response bytes. Each
artifact/request's embedded finite payload has the existing 16 MiB ceiling;
the complete framed message must fit the shared transport ceiling.

The [actual root theorem](../lean/Qleisli/HierarchicalRoot.lean)
`checkAll_denotes` constructs equal implementation and independently requested
denotations, conditional on the actual finite reconstruction and exact
meaning-pair obligations. `checkAll_unitary` and `checkAll_reference_laws`
preserve a common unitary and both inverse laws with arbitrary finite references.
There is no assumed whole-graph semantic environment. Reader/native/transport
correspondence, remaining full-profile rules and source adequacy stay open;
this additive result has no production `VerifiedProgram` conversion and enables
no external schema. The older `inspect` API continues to report artifact-only
consistency without claiming independent request binding.

`Kernel::check_instrument(payload, request)` adds the explicit
[`initialize-unitary-readout-v1` contract](../tests/fixtures/authoring_sessions/measured-qpe-v021/preparation-packet.md#host-connection-contract).
It binds actual initialization, a caller-selected unitary equation, ordered
measurement and final outputs in one fresh native check, then reconstructs
every finite obligation in Rust. Its sealed `CheckedInstrument` retains both
documents. Nested `QLI1`/`QLR1`/`QLH1` frames share one million decoded words;
the 64 MiB framing and two-million structural work limits remain. This additive
experimental report has no production conversion or named QPE guarantee.
The [actual instrument bridge](../lean/Qleisli/HierarchicalInstrument.lean)
proves full branch and residual/reference density equality under the same
finite reconstruction equations, plus actual CBit packing. Its reference
definition is separate from checking. The actual coordinate/completeness bridge
also proves branch columns and trace preservation under explicit finite-leaf
unitarity and independent meaning premises.

### Experimental named QPE instrument

`Kernel::check_qpe_instrument(payload, request, candidate)` checks the retained
instrument against a separate `qleisli.qpe-instrument-request` and untrusted
`qleisli.qpe-instrument-candidate`, both version 1, profile `qpe-dyadic8-v1`.
The request contains full preparation/circuit/readout/output interfaces and an
independently supplied ordinary hierarchy provider request. The candidate gives
actual provider-proof, H/power/inverse-Fourier indices and traversal schedules.
Neither candidate indices nor a proposal-derived comparison confer evidence.

The private `QLQ1` frame embeds the provider's `QLR1` request and the original
entry, schedule, preparation and readout. All nested frames share one million
decoded words and 64 MiB; checking shares the unchanged two-million structural
allowance. `--qpe-instrument-pending` returns all finite proof indices, provider
finite-pair indices, and the deduplicated union of phase/Fourier H indices.
Rust independently requires every obligation exactly once and reconstructs
the full equations, including the phase-fixed mathematical H, under one exact
budget. The 60-second process deadline and 2,200,000-byte response ceiling apply.

The privately constructed `CheckedQpeInstrument` retains candidate bytes and exposes its
`CheckedInstrument` for bounded execution. Actual
[`checkAll_kraus`, `checkAll_reference`, `checkAll_classical`](../lean/Qleisli/HierarchicalQpeInstrument.lean)
bind the checked artifact to QPE for the independently interpreted provider,
including arbitrary-reference branch maps, completeness and classical packing.
Exact finite/H equations and the independent provider interpretation remain
explicit theorem premises; native/decoder/Rust correspondence remains a trust
obligation. This additive API enables no external schema or production
`VerifiedProgram` conversion and proves no general source-preservation theorem.

### Experimental checked reference execution

The additive `CheckedRequest::execute` and `CheckedInstrument::execute` adapters
in `hierarchical::execution` interpret retained **actual definitions**, using
finite matrices bound to their checked implementation indices. They accept
finite, possibly unnormalized `[real, imaginary]` coefficients and an explicit
positive reference dimension. Flatten actual quantum ports in declared order,
with the first axis as the least significant bit; coefficient index is
`reference * 2^quantum_bits + basis`. The reference undergoes the identity.

Execution supports finite leaves, sequence, tensor, inverse, control, repeat,
rewiring, structural conversions and dyadic phases. Capability checking includes
children of zero repeats and inactive controls. Classical circuit inputs and
other constructors reject as `unsupported`. An instrument applies actual fresh
zero preparation, the pure circuit and actual ordered measurements. Its result
contains every unnormalized residual/reference vector; branch indices follow
the actual low-bit-first classical pack order, including zero-probability branches.

`ExecutionLimits` supplies aggregate amplitude-cell and work limits. The former
covers both state/work buffers or the state plus all returned branches; input
storage owned by the caller is excluded. Work counts preparation/readout cells,
definition visits, permutation/phase cells and finite matrix multiply-adds,
including actual repeated bodies regardless of amplitude or control values.
Pending task metadata is reserved only when its guaranteed future definition
visits fit the remaining work budget; a wide sequence cannot allocate an
unchecked task stack. Parsed graph metadata retains the existing bounded
artifact framing limits and is separate from the amplitude-cell allowance.
Overflow, invalid dimensions, nonfinite coefficients and exhausted limits reject;
no partial result or silent normalization is returned. Execution traverses the
DAG without expanding repetitions or constructing a whole-graph dense matrix.
These `f64` results are reference diagnostics outside acceptance authority.
The additive sized CLI uses the same adapter; execution itself proves neither
named meaning nor source preservation.

`CheckedInstrument::sample_normalized_shots` explicitly normalizes finite,
positive-norm input and reports its original norm. Each shot executes afresh
from that joint input/reference state, samples the actual complete branch
weights using one high-53-bit uniform draw from `RandomSource`, and returns
the packed outcome plus normalized conditional residual/reference amplitudes.
Independent uniform random words are a caller premise. Repeated execution is
charged even when the circuit and input are identical.

`SamplingLimits` bounds positive shot count before allocation and shares total
work/output storage across the batch. The mass-drift guard is
`min(2^-20, 2^-40 + 16 * f64::EPSILON * actual_steps)`; it is an explicit runtime
tolerance, not a certified numerical error bound. Zero/nonfinite norm, excessive
drift, overflow, exhausted limits and RNG failure return an error without a
partial batch. `execute` keeps its unnormalized contract unchanged.

### Definition nodes

| Node | Fields and meaning |
| --- | --- |
| `leaf` | `program`: complete bounded finite raw program; checked by the existing independent verifier and, when used as a semantic leaf, the exact checker |
| `sequence` | `children`: ordered nonempty definition refs; adjacent exact interfaces match; execution order is array order |
| `tensor` | `left,right`: disjoint interfaces; effect join; ownership includes both frames |
| `call` | `definition,input_map,output_map`: complete ordered bijective port maps, no capture; substitute local IDs freshly |
| `repeat` | `count,definition`: identical unitary quantum-only input/output; body checked even for count zero |
| `inverse` | `definition`: checked whole-space unitary, inverse effect remains unitary |
| `control` | `definition,polarity`: checked whole-space unitary and one additional distinct control owner, with boolean polarity; full phase retained |
| `rewire` | `permutation`: complete bijection of typed slots/axes, preserving each slot's type; zero-wire owners participate |
| `structural` | `operation`: one explicit ownership conversion from the closed set below; exact types and axis routing are checked without a dense leaf |
| `dyadic_phase` | `target,j,k`: Bit target, diag(1,exp(2πij/2^k)), exact integers in the angle profile |
| `computed` | `compute,use,logical,encoding`: complete checked compute/use/uncompute region; local scratch does not escape |
| `observe_z` | `input,output`: consume a Bit owner and emit a classical bit |
| `init0` | `output`: create fresh zero Bit ownership |

Only the leaf adapter may contain current classical branches/reset/discard.
Its complete interface/effect must match the definition. Future generalized
classical control and partial isometries need another profile; they are not
silently treated as unitaries. There is no standalone `release0` node.
`computed` may use only the encoding rule below, with matched compute inverse;
the scope's external interface contains all surviving data and frame owners.

For node typing, a sequence's effect is the join of all child effects
(`unitary < iso < observe`), and a tensor's interface concatenates the two
ordered interfaces. Tensor frames have disjoint owner, wire and classical
identities across both endpoints. A call maps caller inputs to callee inputs,
then callee outputs to caller outputs. The two maps together must define one
injective renaming of each callee identity domain: an identity preserved by the
callee cannot change its caller name, and a new callee identity cannot capture
a distinct caller input identity. Node annotations record the derived effect.

A `control` places its additional Bit owner first in both quantum interfaces;
the remaining ordered ports are exactly the callee's quantum-only interfaces.
Its owner and wire are fresh relative to both callee endpoints. This canonical
placement is adjusted through explicit call maps when needed. `dyadic_phase`
names its Bit target by local owner ID, preserves its complete interface, and
retains any unchanged frame. `observe_z` names the consumed owner and fresh
classical value ID; all other quantum/classical slots survive in order.
`init0` names a fresh output Bit owner and wire; removing that slot from the
output leaves the exact input frame. These local rules still require complete
body checking and finite-leaf reconstruction, including bodies under zero
repetition. Structural typing cannot establish a compute/uncompute equation
or a provider's asserted unitary meaning.

Coherent control preserves the ordered target type trees between its two
endpoints. Different local identity labels are permitted, but an equal-width
conversion such as Bit to Bits(1) cannot be inserted implicitly into the
inactive sector. Such a conversion needs an explicit admitted encoding rule;
mathematical unitarity alone does not provide that control implementation.

### Explicit structural conversions

`structural(operation)` closes the adopted explicit-axis/conversion obligation
for register and product ownership. A type-preserving `rewire` cannot express
one Bits(8) owner becoming Bit plus Bits(7); a six-bit dense leaf cannot justify
that boundary either. The new rule addresses that resource/encoding obligation,
not convenience-based permission to ignore types. Source notation remains
pending; these are concrete internal definition and meaning constructors.

| Operation | Complete quantum input and output |
| --- | --- |
| `take_bit(n,k)` | One Bits(n) owner becomes a Bit owner for axis k and a Bits(n−1) owner for all remaining axes in original order. Require 1≤n≤8 and k<n. |
| `put_bit(n,k)` | Exact inverse: Bit then Bits(n−1) become one Bits(n), inserting the selected axis at k. |
| `split_tuple` / `join_tuple` | One tuple owner becomes its immediate ordered field owners, or the inverse. Preserve each complete nested field tree and immediate arity, between 2 and 64. |
| `bit_to_bits` / `bits_to_bit` | Explicit Bit ↔ Bits(1), preserving its physical wire. |
| `pack_unit` / `unpack_unit` | No owners ↔ one Unit owner, explicitly creating or consuming the one-dimensional owner. |
| `pack_empty_bits` / `unpack_empty_bits` | No owners ↔ one Bits(0) owner, under the same explicit rule. Unit and Bits(0) remain different types. |

These unitary nodes cover exactly their converted quantum ports; unchanged
frames use checked tensor/call composition. Classical ports are absent. Every
input owner is consumed, every output owner is fresh against those inputs, and
no physical axis is added, lost, duplicated or renamed. Local names are labels,
not positional indices. `take_bit(1,0)` must return its fresh linear Bits(0)
remainder. Neither a zero wire count nor a matching dimension permits an
implicit ownership drop, tuple flattening or type coercion.

The denotation is the phase-free basis bijection determined by this actual wire
routing. Tuple/singleton conversions preserve order; selected-axis conversions
have the stated permutation. Its action extends by identity on an arbitrary
reference. Empty conversion has the scalar +1, not an arbitrary phase or a
claim that nonempty scratch can be released. The inverse descriptor swaps the
operation and endpoints. Both inverse laws are checked against the routing of
those actual reversed endpoints, not an unrelated supplied permutation.

[Hierarchical.Structural](../lean-kernel/QleisliKernel/Hierarchical/Structural.lean)
implements these rules and is called by both definition and meaning typing.
Actual acceptance implies full type/owner/axis validity and a basis permutation;
`valid_reference_round_trips` applies to the predicate used by both passes,
and `check_reference_round_trips` covers its remaining-budget API. The two
coefficient round trips retain arbitrary phases and reference coordinates.
This component materializes no matrix and cannot issue an external receipt.
The semantic derivation pass must still bind the same operation, implementation,
meaning and encodings; the source producer and execution adapter are pending.
The [implementation packet](../tests/fixtures/hierarchical_ir/structural-packet.md)
records the desired helper and acceptance experiment before the first build.

## Meanings, encodings and derivations

Meaning nodes are `identity(type)`, `finite(table-or-matrix,type)`,
`sequence(children)`, `tensor(left,right)`, `inverse(child)`,
`control(child,polarity)`, `power(child,count)`, `rewire(permutation)`,
`structural(operation)`, `phase(j,k)`, and `qft(m)`. The finite node uses existing exact scalars
`a+b√2+i(c+d√2)` with signed dyadic coefficients; only bounded leaves may
materialize a matrix. Every node has a checked exact interface. QFT means
`F_M[y,x]=exp(2πixy/M)/√M`, M=2^m, with positive sign and little-endian basis
indices. A named meaning is not executable access or evidence of a circuit.
Instrument meaning for the QPE observation entry is specified below; it is not
reduced to equality of outcome probabilities on eigenvectors.

All meaning constructors except `qpe_instrument` have quantum-only interfaces.
The phase meaning has one Bit slot; `qft(m)` has one Bits(m) slot and identical
input/output ports in their declared axis order. Sequence/tensor preserve exact
ordered interfaces; inverse reverses the child endpoints; power requires an
identical child input/output. Their pure children cannot be instruments, even
under count zero. Finite meaning headers stay within six input and six output
bits; reconstruction and exact equality remain separate checks. None of these
structural checks substitutes for the unitary premises of inverse/control or
the finite mathematical equation.

The QPE instrument meaning has the provider's one Bits(n) input, retains that
exact quantum output, and adds one CBits(m) classical output. The provider is
a pure, closed meaning with the same complete input/output; its unitary proof
must still be checked. The n/m profile and full target/axis/type binding apply
before the schema can be instantiated.

Allowed encodings are `identity(type)`, `tensor(left,right)`,
`rewire(child,permutation)` and `zero_scratch(type,scratch_bits,compute)`.
The latter is E|x>=C(|x>⊗|0_s>), with a checked whole-space unitary C;
E is isometric by construction. It authorizes release only after checked
uncompute restores exactly the zero product factor for every admitted x and
reference. Having E's description is not evidence that a runtime input lies
in its range. Entry is established only by the enclosing fresh-zero/compute
scope or a preceding checked encoding transition. Encodings cannot be asserted
by a `Clean` name, lifetime, provider field or user-supplied arbitrary matrix.

An identity encoding preserves its full side, including classical slots. Tensor
encodings concatenate disjoint logical/physical frames. A rewire encoding keeps
the child's logical side and explicitly maps its physical side. For zero scratch,
C is closed and quantum-only, its complete physical interface begins with the
unchanged logical ports, and the remaining fresh ports have exactly the declared
scratch width. Zero-width private owners are retained in this explicit region;
they are not erased by dimension comparison. This structural shape does not
establish C's unitary semantics, the entry premise or clean return by itself.

Each proof record has `kind,rule,premises,implementation,meaning,input_encoding,
output_encoding,witness`. For kind `equation`, its conclusion is the phase-exact equation
`U E_in = E_out u` for **that referenced implementation and complete ordered
interface**. The checker derives the conclusion from checked premises and
compares it structurally after the bounded normalizations below. It never
accepts the record's displayed conclusion on trust. Kind `instrument` is admitted
only for the QPE instrument schema below: the meaning contains its target-U
meaning and n,m, its encoding fields are identity at the complete external
input/output, and its conclusion equates all classical outcomes and residual
target/reference CP maps. An observe definition cannot use an equation rule.
No general instrument equivalence checker is claimed.

| Rule | Checker obligation/witness |
| --- | --- |
| finite leaf | Independently check the raw implementation, encoding and exact equation within six bits and existing arithmetic/work bounds |
| sequence / tensor | Match the actual IR children in execution order; intermediate encodings equal, or an explicit checked rewire premise connects them; tensor ports/owners disjoint |
| inverse | Whole-space unitary implementation and matching unitary logical/encoding boundary; rectangular encoding requires its separate admitted-range derivation, not this rule |
| control | Same complete encoding on both sectors, fresh distinct control, exact phase and controlled implementation binding; a restricted encoding needs both sectors' entry/exit premises |
| repeat / powers | Actual body/count equals the proof operand/count; identity interfaces and all premises checked for zero; natural arithmetic overflow rejects |
| associativity | Flatten only adjacent sequence nodes of the same exact interfaces/encodings; tensor reassociation needs an explicit owner/type rewire, not dimension equality |
| rewire composition | Compose full permutations including zero-wire owner slots; actual IR order must equal the derived permutation |
| dyadic phase | Match the actual target `Bit`, complete identity-encoded quantum interface and exact bounded `j,k` in both implementation and meaning; preserve phase rather than compare probabilities |
| compute/uncompute | Actual `computed` contains C, W, C† and fresh-zero scope; premise W E=E u with E=C(-⊗0); conclusion returns every private scratch axis exactly zero and factors it from arbitrary references |
| conjugation | Actual sequence V†; controlled W; V, with V/V† matched and disjoint control; whole-space v w v† rule or explicit admitted-encoding premises |
| schema | Only the fixed registry entry, static arguments, premise proofs and exact IR structural witness described below |

No rule does arbitrary algebraic equality, proof search, evaluation of host
code or whole-space matrix multiplication above six bits. Normalization is
limited to checked sequence reassociation, identity elimination with full
owner interfaces, permutation composition and modular dyadic angle reduction.
It cannot delete a phase, change a type tree or guess commutation. Common
subexpressions are checked once; caches use the complete node/premise/interface
identity, not a supplied digest. Include negative tests for well-typed but
incorrect binding, not merely malformed certificates.

### Finite reconstruction requests

The [finite unitary-leaf adapter](machine-interface-spec.md#reconstructed-finite-unitary-leaves)
now reconstructs complete QIRF1/2 packets through the Rust finite verifier and
exact checker. It binds an independently supplied exact matrix to actual final
ports, retained legacy type trees and immutable bytes, sharing the finite exact
budget across leaves. It exposes no serialized success flag.

The pure [Finite.inspect](../lean-kernel/QleisliKernel/Hierarchical/Finite.lean)
now extracts a pending reconstruction request from the actual indexed proof,
definition and meaning. It retains full program/meaning bytes and interfaces,
the proof index and all four endpoint indices. The version-one finite equation
must have no premises or extra witnesses and actual identity encodings; both
unary endpoints retain the same legacy type tree and at most six axes. Bits
needs an explicit adapter, including at width zero. Header typing and endpoint
binding are checked on these actual tables under the caller's remaining
structural allowance. Local payloads are bounded by the existing 16 MiB cap;
whole-artifact preparation additionally accounts aggregate payload storage.

`project_binding`, `project_unique`, `inspect_conditions` and `inspect_identity`
prove actual data binding, deterministic requests, checked predicates and work
bounds. They prove no statement about opaque byte semantics. Native cases
deliberately retain changed bytes as changed requests; the finite Rust adapter
must still parse and check those bytes against the independently decoded
matrix and boundary. There is no producer-supplied receipt argument.

The conditional derivation below now composes these requests. The reconstruction
host connects actual returned indices to complete immutable Rust leaf data.
Independent root-contract acceptance, remaining finite effects and
multi-owner boundaries still need production integration. The original
`Derivation.checkAll` entry continues to reject finite rules. No schema or
production semantic seal is enabled by request extraction.

### Conditional finite derivations

The additive [Conditional.checkAll](../lean-kernel/QleisliKernel/Hierarchical/Conditional.lean)
entry first checks every artifact/node/contract table, then traverses the actual
proof schedule from an empty proof cache and finite-request array. Finite rules
call `Finite.inspect`; ordinary rules use `TypedRule.check` with the context
constructed from that same typing success; schemas retain `Rule.check`.
Every actual premise must already have a conditional derivation. Shared proofs
are inspected once, and zero repetitions retain their complete bodies.

The reduced ordinary matcher preserves exact endpoints, phase, rule and ordered
premises. `ordinary_sound`, `check_conditions` and `context_of_checkAll` recover
the original rule conditions without an external typed flag. Scans and residual
comparisons are prepaid and continue the same two-million-unit structural
budget and aggregate payload/reachability checks. No call or repeat is expanded;
legacy standalone checks retain their behavior.

The result is `Pending`: every returned request is bound to the actual artifact,
and cached/root conclusions are conditional on satisfying **all** requests.
Producer caches, request arrays and success flags are not inputs. The universally
quantified leaf predicate is a theorem premise, never silently set to `True`.

The [finite interpretation](../lean/Qleisli/HierarchicalFiniteEvaluation.lean)
reads complete interfaces and payload bytes from implementation/meaning tables,
independently of proof metadata. Exact equality of the two partial readers for
every request yields a unique common entry denotation, full complex matrix and
arbitrary finite reference extension. Missing or unsupported leaves fail even
under zero powers. No global interpretation environment is assumed.
The [unitarity extension](../lean/Qleisli/HierarchicalFiniteUnitary.lean) requires
each request's common operator to satisfy its full `UnitaryInterface`; it derives
entry unitarity and both reference inverse laws through actual checked children.

The [fresh reconstruction host](#external-field-encoding-and-reconstruction-host)
uses [exact matrix transport](machine-interface-spec.md#exact-finite-matrix-descriptions)
to decode both complete byte strings with independent coefficient exponents
and exact global phase. Decoder/native correspondence and independent production
root binding remain explicit obligations. These mathematical denotations are
not the reference execution backend or a production hierarchy seal.

### Shared phase-gradient laws

The [diagonal laws](../lean/Qleisli/HierarchicalDiagonal.lean) preserve full
complex phase: sequence multiplies diagonals, repeat uses the actual count,
tensor is low-axis-first, control adds a separate low bit, and inverse routing
pulls back diagonal values. They extend to arbitrary correlated references.

Mathlib-free [sparse helpers](../lean-kernel/QleisliKernel/PhasePolynomial/Operations.lean)
scale coefficients modulo 256 and add positive control without changing term
count. Their evaluation laws do not check axis scope, ownership, canonical form
or budget; a caller must check these. `physical_controlled_gradient` retains an
explicit size bound and actual child-diagonal premise. The inspector below
derives that premise without expanding bodies or executing dense matrices.

### Actual shared-gradient inspection

The [gradient inspector](../lean-kernel/QleisliKernel/Hierarchical/Gradient.lean)
reads the actual empty-identity or split-high-bit / tensor(phase, child) / rejoin
recursion. It checks full interfaces, ordered children, phase fields and both
actual routing maps, retains `Bits<0>` ownership and permits consistent renaming.
Arity/header checks precede traversal. Supported parameters are
1 ≤ precision ≤ 8 and 0 ≤ width ≤ precision; recursion consumes the caller's
remaining structural budget. Complete artifact typing is separately mandatory.

The [complex bridge](../lean/Qleisli/HierarchicalGradient.lean) constructs actual
physical evaluation with diagonal exp(2πi·x/2^precision), where x is independently
defined from low-axis-first bits. Binding, evaluation uniqueness and arbitrary
reference laws require no supplied child matrix or global environment. Direct
control and controlled power consume this result, including omission of a
count-one repetition. This component does not issue semantic evidence.

### Actual Fourier-stage coefficients

The [coefficient proof](../lean/Qleisli/HierarchicalFourier.lean) independently
defines the positive Fourier matrix from little-endian integers. For every
natural width, tensor(H, identity), controlled gradient and
tensor(identity, recursive-child) have the recursive coefficient with exact
negative H entry and dyadic phase. Enter/leave routes preserve low-axis-first
order. The body reverses output bits; actual data reversal gives
exp(2πi xy/2^n)/sqrt(2^n), including arbitrary joint reference amplitudes.

The [stage inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierStage.lean)
checks the actual five-node sequence, full type trees, closed register/Bit ports,
identity rewires, take/put coordinates and both positional maps. It supports
lower-register widths 1–7; the one-bit base uses four nodes. Whole-artifact typing
and the caller's remaining two-million budget are required; no supplied operator,
cache or proof flag is accepted.

The [evaluation bridge](../lean/Qleisli/HierarchicalFourierStage.lean) derives
identity children and binds the actual stage. Exact H, controlled gradient and
recursive-body equations remain premises until the next inspector discharges
them. Structural `Pending` success or unitarity alone cannot discharge them.

### Complete recursive Fourier body

The [body inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierBody.lean)
composes the four-node base, bound H, positive control and literal repeated
shared gradient with the total natural-number recursor. All calls consume one
remaining structural budget; supported parameters are 1 ≤ width ≤ precision ≤ 8.
Exactly `width` H requests retain actual bytes, full interface and definition
index. No partial helper or runtime implementation override is admitted.

The base retains the empty `Bits<0>` owner and derives identity from actual
rewires. H is bound through its explicit owner rename to the independent exact
matrix with a negative lower-right entry. Control checks polarity, complete
interfaces and count 2^(precision-width), permitting the top count-one omission.

The [body theorem](../lean/Qleisli/HierarchicalFourierBody.lean) constructs actual
`reversedFourier width` evaluation by induction. Only the partial reader's exact
H equations remain; recursive/gradient matrices are derived. Uniqueness and joint
amplitude laws retain entangled references and full phase. Fresh Rust H checks
use the exact budget remaining after ordinary finite reconstruction and reject
X and global -H. Native/decoder correspondence to the mathematical reader remains
explicit. The following wiring/root inspectors bind actual output reversal;
these components still enable no external schema or production seal.

### Actual shared wiring

The [wiring inspector](../lean-kernel/QleisliKernel/Hierarchical/Wiring.lean)
processes actual rewire, structural, tensor and sequence bodies in a selected
dependency order from an empty cache. Missing/duplicate dependencies, cycles,
unsupported bodies, unequal widths and invalid axes reject. Routes are square
with at most 16 axes; empty routes retain independently checked owners. An omitted
root has no cache result. No producer route claim is accepted or repeat expanded.

Allocation, fields, structural routing and composition consume one remaining
budget. H/phase children are not treated as identity. Full artifact typing remains
required: computable routes cannot authorize duplicate axes or lost zero owners.
The [complex interpretation](../lean/Qleisli/HierarchicalWiring.lean) constructs
actual phase-free evaluation, coefficient one at the computed routing and zero
elsewhere, including arbitrary references. It assumes no leaf-reader equation
or global interpretation. A route alone is not an ownership or semantic seal.

### Actual outer Fourier request

The [root inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierRoot.lean)
receives an independently selected width and full positive-sign little-endian
Fourier interface. Its additional component profile supports widths 1–8 and an
outer sequence of 3–16 children; it does not reduce general IR capacity.

The entry must match the requested quantum-only interface and unitary effect.
The first child routes identically, the second passes recursive-body inspection,
and all remaining children compute complete bit reversal in a fresh wiring
cache. Missing roots/dependencies reject; commuting disjoint SWAPs are permitted.
Submitted routes or whole-circuit matrices cannot replace these checks.

Complete artifact typing is mandatory. Metadata, interface comparisons and route
composition are prepaid; body/wiring checks share the remaining budget. Returned
H obligations retain full bytes and interfaces; fresh exact checks reject X/-H.
The [coefficient theorem](../lean/Qleisli/HierarchicalFourierRoot.lean) constructs
the actual entry's positive Fourier matrix and arbitrary reference action,
deriving identity/reversal and retaining only the bound H reader equations.
Production sealing, native/reader correspondence and remaining profile/source/QPE
gates stay open. External schemas are disabled, and TP-005 APIs remain audited
until callers and the registry migrate compatibly.

### Fourier request host

The [host packet](../tests/fixtures/hierarchical_ir/fourier-host-packet.md)
connects the root theorem to `interchange::hierarchical::Kernel::check_against`.
The envelope remains `qleisli.hierarchy-request` version 1, profile
`qpe-dyadic8-v1`. Its named form is `kind: equation`, `effect: unitary`, entry zero,
and exactly one `qft(width)` meaning with the complete request-header interface.
The boundary is a closed single `Bits<width>` with identical owner, type and
axis order at both ends. Equal dimension or a `Bit` adapter is insufficient.

The untrusted Rust codec proposes the outer wiring schedule. Private `QLF1`
decoding checks the singleton form again; `FourierRoot.checkAll` invokes full
`Conditional.checkAll`, then root inspection with the remaining structural
budget and `namedBoundary`. Complete endpoint comparisons are prepaid.

A fresh native response names ordinary finite proof indices and actual H indices.
Rust reconstructs every ordinary equation and each exact H with its negative
entry, full bytes/interface and one shared exact budget. The H-index count must
match; duplicates, omissions, invalid indices and non-leaves reject. Private
`CheckedRequest` fields retain both raw inputs. No API accepts serialized pending
responses, checked flags or precomputed H results.

[The host theorem](../lean/Qleisli/HierarchicalFourierRoot.lean) combines actual
coefficient and conditional unitary results into the requested matrix, interface
and both arbitrary-reference inverse laws. Both finite-reader obligation sets
and native/decoder correspondence remain explicit. The fixture producer is
connected, but ordinary sized-source integration, remaining instrument/rules and
source/corpus release gates remain open. This is an additive inspection report;
it issues no production `VerifiedProgram` and enables no external schema.

### Whole-space derivation implementation

The untrusted [call producer](../lean-kernel/QleisliKernel/Hierarchical/CallLowering.lean)
emits two existing rewires and a three-child sequence, retaining the child and
all other definitions without expansion. Its
[coordinate theorem](../lean/Qleisli/CallLowering.lean) gives
U(output_map⁻¹(y), input_map(x)), unitary/reference preservation, conditional on
original call typing and one consistent fresh rename across both endpoints.
External/source translation validation remains open; the producer adds no rule.

[Rule](../lean-kernel/QleisliKernel/Hierarchical/Rule.lean) matches identity-encoded
unitary equations for actual rewires, structural conversion, exact dyadic phase,
ordered sequence, tensor, inverse, control, repeat and direct controlled power.
Ordinary templates use version 1 and empty parameter/reference arrays. Children
must be ordered actual proof endpoints; a zero repeat needs its checked body.
Phase uses exact j,k, including angles beyond the finite coefficient ring.

[Derivation.checkAll](../lean-kernel/QleisliKernel/Hierarchical/Derivation.lean)
checks all structural tables/scheduling, then every actual premise from an empty
cache. Shared proofs are checked once with all work charged to the same
two-million budget. `powerEntry` independently matches exponent/provider and
requires that provider's established proof. No external cache or flag is used.

The [rule induction](../lean/Qleisli/HierarchicalSemantics.lean) and
[complex operators](../lean/Qleisli/HierarchicalOperators.lean) preserve exact
phase, low-axis-first tensor order, inverse, coherent control, powers and arbitrary
references. The [constructed evaluator](../lean/Qleisli/HierarchicalEvaluation.lean)
derives equal unique entry denotations from actual checked bodies without an
assumed environment/provider equation. It uses decreasing dependency fuel;
unsupported/missing children fail, including beneath zero repeat. Physical and
logical readers are independent of proof metadata.

These mathematical sums are not executable verification or simulation. Remaining
finite/encoded/computed rules, schema/provider binding, independent production
requests and execution correspondence still gate full-profile Soundness. External
schemas remain disabled; current component evidence is in the rule inventory.

## Fixed schema import boundary

There is **no arbitrary Lean-proof import**. The production verifier ships a
closed, versioned registry of rule implementations and corresponding Lean
declarations from the pinned project. Initial requested entries are
`qft-dyadic8/1`, `controlled-power/1`, and `qpe-instrument/1`.
Compute/uncompute and conjugation are local rules with their own premises.
Predicate/adder schema identifiers are reserved for later separately reviewed
profiles; an unknown or not-yet-proved entry always rejects.

For each entry, the repository must contain a registry manifest with identifier,
version, complete premise/conclusion type, concrete parameter domains, Lean
module/declaration, source revision, template version and executable Lean
checker entry.
The release build must compile and axiom-audit the declaration and compare its
exported type with the manifest. The acceptance theorem must name the actual
Lean checking definition; executable-declaration and dependency audits are
additional gates. This establishes the stated Lean theorem, not correctness of
its native compilation, transport or any remaining Rust finite-leaf adapter.
The external artifact supplies only registry ID, bounded integers, premise
references and an IR witness. The verifier chooses
the shipped manifest; an artifact cannot supply a replacement theorem or hash.

QFT witness: ordered stages j=m−1..0, H(j), then controlled phases with k=j−1..0
and angle 2π/2^(j−k+1), followed by swaps reversing bit order. Swaps are checked
rewires or their checked three-CNOT realization, not arbitrary named gates.
Match the actual hierarchical nodes/port maps to this template, preserving
control/target roles and stage order. The theorem conclusion is the positive
F_(2^m), with this exact layout. The schema checker visits O(m²) nodes, never
constructs F as a dense matrix. A template mismatch rejects even if a different
circuit happens to implement QFT; another derivation is required.

Controlled-power witness: a checked U, integer k, and actual controlled
`repeat(2^k,U)`, or an independently proved provider of the exact same power
meaning. Repeated squaring is acceptable only with its checked power equalities
and implementations. An `efficient` string or abstract unitary assertion is
not evidence of efficient oracle access. Its theorem quantifies over the
phase-fixed unitary and disjoint control, including arbitrary references.

### Direct controlled-power artifact binding

The direct `controlled-power/1` projection matches actual implementation
`control(repeat(2^k, provider), true)` against logical
`control(power(providerMeaning, 2^k), true)`. Their indices are distinct domains.
The leading `Bit` control is coordinate zero. Exactly one provider-equation
premise must match both indices and identity encodings; full types, owners,
axes and closed interfaces must agree. Restricted encoding is excluded.
Template version 1 uses `[k, providerImplementation]` and no extra witness refs;
the caller independently supplies k/provider rather than trusting these fields.

[Power.inspectEntry](../lean-kernel/QleisliKernel/Hierarchical/Power.lean)
first checks complete artifact typing/dependencies, then spends only the remaining
budget without expansion or matrices. Local `inspect` alone is insufficient.
Its result retains a pending provider proof. The
[operator bridge](../lean/Qleisli/HierarchicalPower.lean) needs that exact equation,
plus an explicit isometry premise for unitarity, and preserves joint reference
maps. Generic derivation, finite reconstruction and independent request binding
must discharge these obligations on the same artifact.

The QPE witness is fresh m-bit zero, H on each precision bit, U^(2^k) controlled
by bit k for k=0..m−1, inverse positive QFT and ascending Z readout. Preserve the
full target output, all controlled-power proofs, dimensions and actual stage
bindings. The theorem must cover the complete instrument, not only eigenstate
outcomes. The [closed dispatcher](../lean-kernel/QleisliKernel/Schema.lean) checks
component IDs/versions/parameters; external schema enablement additionally needs
actual theorem/importer binding, tests and declared native/transport/finite-leaf
boundaries. Alternative efficient-power derivations and external integration
remain separate obligations.

### Dependency scheduling implementation

[Graph](../lean-kernel/QleisliKernel/Hierarchical/Graph.lean) checks a proposed
schedule as a complete index permutation and requires every actual edge to
decrease rank, with reachability/depth checks. Typed preparation extracts edges
from actual definitions, meanings, encodings and proofs, including zero-repeat
bodies; producer edge lists cannot replace this projection. External table order
need not be topological. Acceptance proves acyclicity, not semantic evidence.

Limits are 100,000 nodes, 1,000,000 references, depth 256 and 2,000,000 visits.
The conservative charge `10 * nodes + 5 * references + 3 * roots` covers scans,
arrays, lookups, scheduling and reachability. `checkWithBudget` takes only the
remainder after preparation, and later checks continue it. No repetition or
dense matrix is expanded. Reference counting stops before the next over-budget
visit; root counting inspects at most `nodes + 1` entries before rejecting.

### Typed artifact preparation

[Artifact](../lean-kernel/QleisliKernel/Hierarchical/Artifact.lean) contains four
typed tables, full interfaces, proof endpoints, ordinary witnesses and an explicit
entry pair. Table-tagged references are checked against their own bounds before
projection. All premise, witness, encoding and zero-repeat-body references enter
the actual dependency graph; acceptance proves its acyclicity.

Preparation checks prefix type trees, owner/wire uniqueness, widths, effects,
angle/count bounds and all four exact logical/physical endpoint equalities.
Classical Bit/Bits mean CBit/CBits. Unit/Bits(0) retain owner slots. IDs are labels;
maps use ordered slots/flattened axes. Equation endpoints cannot observe;
instrument endpoints require QPE meaning and identity encodings.

Constant-time size and quadratic-port precharges precede traversal/uniqueness;
repeated shared-interface comparisons are charged each time. Graph checking
receives only the remaining two-million allowance. Aggregate opaque finite
payload is capped at 16 MiB; external decoding also bounds complete headers/data.
Prepared data is not semantic evidence: node typing, finite decoding, derivations,
schema projection and independently required meaning still need checks.

### Complete side-map checker

[Ports](../lean-kernel/QleisliKernel/Hierarchical/Ports.lean) constructs coordinates
in port/axis order and checks both inverse laws for actual owner/axis/classical
maps over their complete domains. Structural identity includes tuple arity,
nesting, Unit and Bits width; equal dimension cannot authorize conversion.
Local IDs are labels, not map positions. Classical-map bijectivity preserves
boundary slot types without forbidding classical copying inside operations.

The proved coefficient round trip extends to arbitrary references. Array/width
prechecks precede coordinate allocation. The checker returns its charge against
the caller's remaining profile budget; the enclosing node pass must debit it.
A single-side check does not establish both call sides, fresh names, a body
meaning or an equation. It enables no acceptance rule by itself.

### Definition-node typing

[NodeTyping](../lean-kernel/QleisliKernel/Hierarchical/NodeTyping.lean) checks actual
constructor fields and child headers. Both call maps share one injective fresh
identity relation for owners, wires and classical values. Sequence checks exact
intermediates/effect joins; tensor checks disjoint frames at both ends. Repeat
and inverse require unitary conditions; control requires a distinct leading Bit.
Phase/init/measurement check named owners, effects and complete surviving frames,
including zero-width owners.

`checkAll` prepares the actual artifact and checks every definition once, including
zero-repeat bodies. Index allocation, headers and side maps use one remaining
two-million budget. This establishes structural conditions, not leaf semantics.
Computed nodes check C/W/u/E interfaces and zero-scratch encoding shape; encoding
typing follows below. C/W unitarity and W E = E u remain semantic obligations.
Finite reconstruction, rule equations and external request binding are required.

### Meaning and encoding typing

[ContractTyping](../lean-kernel/QleisliKernel/Hierarchical/ContractTyping.lean)
invokes actual definition-node checking, then checks every indexed meaning and
encoding. Allocation, header comparisons and maps continue one aggregate
two-million budget without repeated-body or dense-matrix evaluation. Coherent
control cannot implicitly convert target types; consistent local renaming of
the same ordered types is permitted.

Structural success does not prove finite descriptions, provider/compute
unitarity, zero-scratch return, derivation equations, actual schema projection
or the consumer's independent meaning. Those checks remain mandatory, and all
external schemas stay disabled.

## First QPE profile and exact angles

Select target widths **1≤n≤8**, precision widths **1≤m≤8**, total live interface
n+m≤16, with 0≤j<2^k and **0≤k≤8** for ideal dyadic phases. Canonicalize by
reducing j modulo 2^k, then dividing even j and its denominator by two; zero
is (0,0). Negative inverse angles are reduced modulo the same denominator.
No float, decimal approximation or numerator rounding participates in proof
comparison. Addition uses checked integers at the larger denominator; reject
an out-of-profile denominator before shifting. H is a separate exact primitive.
Current ζ8 leaves remain unchanged; π/8 and finer phases use this symbolic
node/schema path, not the existing exact scalar representation.

Keep the ideal angle/meaning domain separate from a hardware gate-set forecast.
Future coefficient-domain type parameters must bind arithmetic, interpretation
and evidence identities to a reviewed domain; they do not enable arbitrary
real-angle equality automatically. Native-rotation support needs a separately
specified domain/meaning and approximation/device contract as described in the
[design note](coefficient-domains.md). The `qpe-dyadic8-v1` bounds, R8 leaves
and exact cleanup rules here remain unchanged.

For M=2^m, QPE outcome y has Kraus operator on the unmeasured target

```text
K_y = (1/M) sum_(j=0)^(M-1) exp(-2π i j y/M) U^j.
rho -> sum_y |y><y| tensor (K_y tensor I_R) rho (K_y† tensor I_R).
```

The instrument includes residual target/reference correlations and all y;
eigenstate/phase promises are only for algorithmic precision claims. Measuring
m bits yields y=sum bit[k]*2^k. No target measurement/discard is implicit.
Ideal exact semantics and floating reference sampling are distinct layers.

Checker limits: 16 MiB encoded artifact, nesting 128, 100,000 combined
definition/meaning/encoding/proof nodes, 1,000,000 references, DAG depth 256,
repeat counts 0–4,096, two million charged graph/rule/structural-comparison visits,
and 10,000,000 aggregate exact leaf-work units. Charge every edge/array element
visited; memoize shared checked nodes. Limits reject with `limit`; wrong
interfaces/ownership/effects with `invalid_ir`; wrong equations/schema/binding
with `contract`; unavailable profile with `unsupported`. Error reporting must
retain the failing definition/proof index and premise chain within the budget.

Checking is polynomial in the shared artifact plus bounded leaf work. QFT
generation/proof size is O(m²); explicit repeated-U QPE execution still uses
2^m−1 U applications. A logarithmic Repeat node is not a speedup in oracle cost.
Record generation time, encoded IR/proof sizes, checker node/leaf visits, peak
dense dimensions and expanded execution counts separately at each tested width.

No approximate backend is admitted to this exact profile. A later adapter must
bound the diamond distance of implemented and ideal instruments; for unitary
components it may use operator-norm bounds ε_i and the conservative channel
bound 2*sum ε_i (capped at 2), counting each actual invocation. Sampling error
and QPE resolution error are separately reported. Approximation cannot weaken
exact private-scratch cleanup; keep an exactly uncomputed implementation or
reject the backend. Hardware validity is an additional backend obligation.

## Synthesis without complete truth tables

M3 selects an acyclic Boolean DAG fragment: input bits, constants, NOT, XOR,
AND and shared subexpressions. For each gate, allocate a fresh zero scratch bit
and compute its result reversibly using X/CNOT/Toffoli. Copy the requested output
bits into distinct output targets by XOR, then reverse the scratch computation.
The contract is `|x,y,0_s> -> |x,y xor f(x),0_s>` for every input/reference,
not cloning arbitrary quantum states. Each DAG node's local gate identity and
the complete inverse trace justify cleanup. Proof and generated circuit are
O(nodes+edges+outputs), with shared computation represented once; no 2^n table
is required. Noninjective f is valid for this oracle, never as an in-place lift.
In-place permutation synthesis additionally needs a checked inverse and its
whole-space extension. Keep existing finite tables as regression oracles.

M4's selected arithmetic decomposition is fixed-width reversible add,
carry/borrow and comparison, conditional subtract/reduce, then exact reverse
cleanup. For multiplication by a coprime a mod N, require 0<a<N<2^n,
gcd(a,N)=1, inverse constant a^-1 mod N, and identity on x≥N. Double-buffer
compute, swap and inverse-multiply uncompute must restore its old buffer;
verify modular-power providers against a^(2^k) mod N. Local add/compare schemas,
out-of-residue branches, inverse equations and complete scratch binding are
mandatory before using this in Shor. This is a selected decomposition, not a
completed M4 source/API specification or arithmetic proof. V1-C5 remains open.

## Migration and implementation gates

Introduce a versioned successor IR/API; do not mutate the meaning of existing
RawOp fields. The old finite adapter structurally validates and embeds old IR
as checked leaves, preserving full signatures and contracts. A reverse adapter
may expand only within the old budgets/representable angles; it rejects π/8,
unsupported nodes or excessive expansion explicitly. Public exhaustive Rust
matches must migrate to the successor API; old raw constructors retain their
old path. Versioned serialization keeps readers from mistaking hierarchy for
flat checked evidence.

| Gate | Required implementation evidence |
| --- | --- |
| H1 independent binding | Fresh-process checking of every node/rule; mutation of body, static count, interface, phase, dependency, port map and encoding rejected even when cached names match. |
| H2 schemas | Pinned Lean statements about the actual checking definitions, axiom and executable audits; matched templates and negative premise/layout/angle cases; record remaining native, transport and Rust finite-leaf correspondence assumptions. |
| H3 scaling | One shared QPE/QFT definition instantiated at (n,m)=(1,3),(2,4),(8,8); report all size/work metrics, forbid any dense matrix above six bits and any expansion of shared repeated bodies during checking. |
| H4 semantics | Small exact admissible-angle comparison; π/8/finer schema cases; independently computed QPE instrument on superpositions/entangled references at small widths, not only exact eigenphases; preserve target ownership. |
| H5 failure/migration | Cycles, deep inputs, zero-repeat invalid bodies, limits, wrong theorem registry/version and forged entry evidence; old adapter round-trip and explicit reverse-adapter rejection. |

H1–H5 are unexecuted future gates. Only their specification is completed here.
They do not replace the separately required executable V1-C1–C5 evidence.
