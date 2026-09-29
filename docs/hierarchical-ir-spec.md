# Selected bounded hierarchy and evidence profile

Status: **M2 architecture/profile adopted; component implementations in progress**
(2026-09-27). This settles the joint IR/evidence, schema-import and first-QPE
profile decisions raised by the v0.1.4 review. The M1 extension specification
is [separate](next-minor-spec.md). Sized source grammar, generalized standard
APIs and their G020-1 extension review remain M2 work; this document fixes the
checker/IR contract they must satisfy. The component results below do not yet
implement the complete profile or enable production acceptance.

The subsequent [Lean kernel migration](lean-kernel-migration.md) selects Lean 4
without Mathlib runtime dependencies for this new executable checker. Separate
proof modules may use Mathlib to interpret those same executable definitions.
The [phase-word and shared-DAG checkers](lean-hierarchy-slice.md) are limited
precursors. The latter proves composition and actual acceptance for bounded
cyclic phase actions, with explicit owner ports and zero-repeat dependencies;
it does not implement this full hierarchy, schema registry or QPE instrument.
The [typed layout component](lean-layout-slice.md) additionally checks complete
owner/axis permutations, zero-width slots and structural types. Its bounded
reindexing proofs are now connected to [shared typed calls and ordered
composition](lean-layout-dag-slice.md), with actual-checker soundness for phase-free
coordinate graphs. The [combined phase/layout component](lean-phase-layout-slice.md)
now checks controlled dyadic phases and typed call composition through sparse
polynomials. Non-diagonal graph integration, general transforms/encodings,
complete schemas and H1–H5 remain open. The [interference continuation](lean-interference-slice.md)
now supplies local H/diagonal amplitude laws and a complex interpretation
bridge. The [QFT circuit proof](lean-qft-proof-packet.md) establishes the actual
matched template's Fourier coefficients and arbitrary reference extension.
The [typed QFT graph projection](lean-qft-graph-packet.md) now binds exact
interfaces, effects and shared dependencies to those coefficients. The
[QPE component](lean-qpe-instrument-packet.md) proves actual schedule and
branch/reference equations, plus conditional completeness and total trace
preservation. Its unitary-provider premise must be independently established.
The typed four-table preparation, definition-node and meaning/encoding typing
are implemented below. A supported whole-space derivation pass now checks
actual local rules and every provider premise from an empty cache. Constructed
actual-body denotations now give exact complex operator/reference equations for
the supported accepted rules. Whole-space unitarity, general encoded
derivations, finite reconstruction and external hierarchy import remain open.
The [component type/source manifest](lean-qpe-instrument-packet.md#shipped-type-and-source-manifest)
now pins the proved internal declarations; all external entries remain disabled.
Current finite acceptance remains
in Rust until the explicit migration gates transfer each covered boundary.

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
entry runs the existing complete artifact/node/contract typing pass and then
starts with an empty proof cache and finite-request array. It visits the actual
proof schedule: finite rules call `Finite.inspect`, ordinary rules use
`TypedRule.check` with the type context proved from that same actual completed
typing pass, and schemas retain `Rule.check`. Every actual premise must already have a conditional
derivation. Shared proofs are inspected once. A zero repetition still requires
its complete body; no call or repetition is expanded. The same two-million-unit
structural allowance and aggregate payload/reachability checks apply.

The typed ordinary matcher retains exact endpoint, rule, phase and ordered
premise comparisons. It avoids repeating node/meaning typing and quadratic
layout predicates already established on the immutable artifact. Its
`ordinary_sound` and `check_conditions` theorems recover the original
`Rule.ordinary`/`Rule.Matches` conditions; `context_of_checkAll` constructs the
needed context from actual checker success. No typed flag, context or cache is
an external artifact field. Proof-state induction and the public
`Conditional.checkAll_conditions` theorem retain their earlier conclusions.
Finite reconstruction and schema checks are unchanged. Residual comparisons
are charged by complete linear field scans, with precharges before traversal;
the two-million-unit ceiling is unchanged. Legacy standalone local check/scan
APIs retain their behavior.

The [actual QFT authoring packet](../tests/fixtures/hierarchical_ir/qft-binding-packet.md)
exposes this repeated work using finite H leaves, dyadic control, explicit bit
extraction/reinsertion and data swaps. Widths 1–4 of the directly lifted
construction fit the existing allowance; its width-eight form remains a
capacity regression. An untrusted [shared-gradient construction](../tests/fixtures/hierarchical_ir/qft-shared-gradient-native.json)
uses recursive register boundaries, shared phase subgraphs and existing
controlled/repeat rules. Every width 1–8 fits, with width eight costing 1,694,205
structural units and 536 exact units for eight one-bit H leaves. The checker
performs no shared-body expansion, and no budget or rule was changed for this
producer improvement. These artifact-consistency checks do not bind the named Fourier meaning or enable
the external QFT schema. Independent numerical Fourier probes remain test
oracles, never evidence supplied to the checker.

The result is `Pending`. It contains every actual finite request and accepts
no producer cache, request array or success flag as input. `step_requests` and
`checkAll_conditions` prove that returned requests came from inspection on the
same artifact and that all cached/root conclusions have actual derivations
**conditional on satisfying every request**. The remaining leaf predicate is
universally quantified in the theorem; it is not executable input and is never
silently set to `True`. Repetitions 0–4096 retain the same request count and
checking cost in the [native fixture](../scripts/test_hierarchical_conditional.py).

The separate [finite-leaf interpretation](../lean/Qleisli/HierarchicalFiniteEvaluation.lean)
reads actual implementation and meaning tables through independent partial
leaf readers taking the complete interface and payload bytes. Proof tables do
not enter these readers. `checkAll_denotes` constructs a common successful
entry denotation, conditional on exact equality of the readers for each returned
request. The same value is unique across sufficient dependency fuel; missing
or unsupported leaf interpretations fail, including under zero powers.
`checkAll_matrix` and `checkAll_reference` retain complete complex coefficients,
global phase and arbitrary finite reference systems. No whole-graph semantic
environment or producer-displayed conclusion is assumed.

The [finite unitarity extension](../lean/Qleisli/HierarchicalFiniteUnitary.lean)
strengthens each returned leaf premise to a common decoded operator satisfying
its complete `UnitaryInterface`. `derives_unitary` propagates this property
through the actual ordinary children and controlled-power provider/repeat/control
nodes. `checkAll_unitary` constructs a common unitary entry denotation;
`checked_denotation_unitary` applies it to any successful evaluation of that
entry, and `checkAll_inverse_laws` gives both inverse equations after extension
by an arbitrary finite reference system. No global unitary environment or
assumption about unchecked nodes is introduced.

This is a compositional theorem relative to the chosen leaf interpretations,
not a proof that a Rust return value establishes those interpretations. Their
decoder/transport correspondence, independent production root-request binding and the rest of the profile remain
required before issuing a verified hierarchy or enabling a schema. The
mathematical evaluator is not the reference execution backend.
The [exact finite matrix transport](machine-interface-spec.md#exact-finite-matrix-descriptions)
now lets the Rust adapter freshly read both byte strings and retain their full
binding, including global phase and independent exact coefficient exponents.
The reconstruction host now connects actual returned request indices to that
same retained data. Mathematical correspondence of the readers and transport
remains explicit; the host report does not establish a requested root contract.

### Shared phase-gradient laws

The [diagonal operator extension](../lean/Qleisli/HierarchicalDiagonal.lean)
proves exact matrix laws for the actual `HierarchicalOperators` definitions:
composition multiplies the diagonal values, repetition raises them to the
actual count, tensor products retain the low-axis-first order, coherent control
adds the separate low control bit, and a forward/inverse data permutation pulls
the diagonal values back along its route. These statements retain complete
complex phases; `joint_amplitude` covers arbitrary correlated reference columns.

The Mathlib-free [sparse operations](../lean-kernel/QleisliKernel/PhasePolynomial/Operations.lean)
scale coefficients modulo 256 and add a positive control condition. Their
evaluation and unchanged-length theorems hold for arbitrary polynomials and
counts. They are total helpers, not acceptance functions: axis scopes,
ownership, canonical representation and work must still be checked by a caller.
The complex bridge proves that these summaries describe the actual repeated
and controlled operators, without body expansion or dense runtime matrices.

`physical_controlled_gradient` reads the actual controlled/repeated bodies,
their count and the actual child evaluation, then applies the dyadic-precision
equation under its explicit size bound. That reusable theorem retains the
child's diagonal as a premise. The subsequent inspection theorem below derives
this premise from actual definitions. [First sources and native checks](../tests/fixtures/hierarchical_ir/gradient-first/README.md)
retain the original component scope separately from the complete algorithm gate.

### Actual shared-gradient inspection

The Mathlib-free [gradient inspector](../lean-kernel/QleisliKernel/Hierarchical/Gradient.lean)
reads actual definition indices and requires the recursive empty-identity or
split-high-bit / tensor(phase, child) / rejoin pattern. It checks complete
register and bit interfaces, ordered children, phase target/numerator/exponent,
and both routing maps computed from actual wire labels. It retains the empty
`Bits<0>` owner and accepts consistent owner/axis renaming. Fixed arities and
header sizes are checked before traversals; all recursive costs use the same
caller's remaining structural budget. Supported inspection parameters are
1 ≤ precision ≤ 8 and 0 ≤ width ≤ precision. This is a component inspection,
not whole-artifact ownership acceptance or a verified-hierarchy result; the
caller must also retain the actual complete-artifact typing check.

`project_bound` and `inspect_sound` bind successful inspection to every actual
body and remaining-budget bound. The [complex proof](../lean/Qleisli/HierarchicalGradient.lean)
then constructs the actual physical evaluation by induction. `inspect_evaluates`
proves its complete diagonal is exp(2πi·x/2^precision), with x independently
defined from the low-axis-first input bits. No child diagonal, matrix receipt,
finite leaf equation or whole-graph environment is assumed. Evaluation
uniqueness and `inspect_joint_amplitude` extend the result to any successful
evaluation and arbitrary correlated reference columns. The direct-control and
controlled-power bridges consume this result, including the top stage that
omits a repetition of count one.

[Native checks](../tests/fixtures/hierarchical_ir/gradient-binding-native.json)
cover 175 outcomes on the actual shared-QFT producer, including renaming,
mutations and exact/insufficient budgets. After whole-artifact conditional
checking, inspecting every selected gradient still fits the original budget:
width eight uses 1,754,765 of 2,000,000 units in total. Independent numerical
phase probes cover 574 basis/reference vectors and detect a phase fault whose
probabilities remain unchanged. These diagnostics are distinct from the Lean
proofs. [First attempts](../tests/fixtures/hierarchical_ir/gradient-binding-first/README.md)
retain real repairs. Binding finite H gates, all outer QFT stages and the final
reversal to the complete requested Fourier coefficients remains necessary;
external schemas and generic source/corpus acceptance remain disabled/pending.

### Actual Fourier-stage coefficients

The [coefficient proof](../lean/Qleisli/HierarchicalFourier.lean) defines the
desired positive Fourier matrix independently from little-endian integers.
For every natural width, the actual tensor(H, identity) / controlled-gradient /
tensor(identity, recursive-child) matrix product has the expected recursive
coefficient, including the negative H entry and all dyadic phases. Explicit
enter/leave routing follows the actual low-axis-first convention. The recursive
body produces reversed output bits; a separate data-reversal permutation
converts it to exp(2πi xy/2^n)/sqrt(2^n). The result extends to arbitrary joint
reference amplitudes. These matrix expressions occur only in the proofs.

The Mathlib-free [stage inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierStage.lean)
reads the actual five-node sequence and tensor children, checking full type
trees, closed register/Bit interfaces, exact identity rewires, structural
take/put coordinates, and both positional routing maps. For lower-register
width 1–7 it returns a pending step and its charged work. This is not a new
Fourier acceptance rule. The one-bit base uses a different four-node sequence.
Whole-artifact typing and the caller's remaining two-million budget remain
required; inspection does not accept a cache, supplied operator or proof flag.

`project_bound`/`inspect_sound` prove actual indexed-body binding and the budget
bound. The [evaluation bridge](../lean/Qleisli/HierarchicalFourierStage.lean)
constructs the stage's physical evaluation, derives both identity children,
and proves the coefficient law conditional on its three nontrivial actual
children: exact H, the controlled gradient and the recursive Fourier body.
These obligations are not discharged by unitarity, matching headers or a
`Pending` result. Final reversal of the actual outer graph, the base case,
finite H reconstruction and complete independently requested-root binding still
have to be connected before any external schema is enabled; the subsequent
recursive-body checkpoint below discharges the base/control/recursive premises
and binds the finite H request.

[Native checks](../tests/fixtures/hierarchical_ir/fourier-stage-native.json)
cover 144 outcomes on all 28 five-node producer stages at widths 2–8, including
renaming, exact/one-short budgets and malformed structure. A complete width-eight
artifact, its selected gradients and all stage inspections consume 1,800,097
structural units cumulatively. Independent numerical checks compare 168
complex basis/reference vectors with the Fourier formula and detect replacing
H by X. Explicit tests confirm that unresolved H/gradient bodies remain pending,
rather than silently treating geometry inspection as semantic evidence.
[First attempts](../tests/fixtures/hierarchical_ir/fourier-binding-first/README.md)
retain the actual diagnostics. Generic source, shared QPE, corpus completion and
R14/H1–H5 remain separate open gates.

### Complete recursive Fourier body

The [recursive-body packet](../tests/fixtures/hierarchical_ir/fourier-recursion-packet.md)
now connects the four-node one-bit base, exact H request, positive coherent
control, literal repeated gradient and all recursive children. Its
[pure inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierBody.lean)
composes the bounded component inspectors and passes the same remaining
structural budget at every call. It uses the total natural-number recursor;
no compiler implementation override or partial helper is admitted. Supported
parameters are 1 ≤ width ≤ precision ≤ 8. Each returned H request retains the
actual full leaf bytes, interface and definition index; the proved request
count is exactly the width.

The one-bit base retains the empty `Bits<0>` owner and derives its identity
from the actual rewires. Its geometry reuses the stage record without adding
a synthetic node to the artifact; its binding theorem records the actual four
children. The H inspector binds the finite leaf and its explicit owner rename,
without decoding or trusting the payload. The independent target is the exact
phase-fixed H matrix, including its negative lower-right entry. The control
inspector checks the actual polarity, shared gradient, full interfaces and
count 2^(precision-width), including the top stage's omitted count-one repeat.

The [complex theorem](../lean/Qleisli/HierarchicalFourierBody.lean)
constructs the actual physical evaluation and derives its complete
`reversedFourier width` matrix by induction. `inspect_evaluates` no longer
assumes a recursive-child or gradient matrix; its only leaf premise is the
actual partial reader's exact H equation for each returned request. Evaluation
uniqueness and `inspect_joint_amplitude` retain arbitrary entangled reference
columns and full phase. Fresh Rust reconstruction checks each native-returned
request against an independently constructed exact H matrix, sharing the exact
work remaining after ordinary finite reconstruction. Correspondence of Rust
decoding, transport and native execution to the mathematical reader remains
explicit; a test report or Rust handle is not a Lean theorem.

[Base/H checks](../tests/fixtures/hierarchical_ir/fourier-base-native.json) pass
206 native outcomes and 40 finite reconstructions, including X, global -H,
malformed bytes and stale owner bindings. The
[integrated body checks](../tests/fixtures/hierarchical_ir/fourier-body-native.json)
pass 172 outcomes across all 36 precision/width pairs and directly export the
36 positive bound requests for fresh H reconstruction. Phase/count/polarity and
recursive-body mutations reject. The H payload itself remains a pending exact
obligation until reconstructed. Independent numerical checks cover 200
basis/reference vectors; global -H demonstrates why probability equality is
insufficient. Whole-artifact checking plus the full width-eight body costs
1,819,083 structural units. Each independently requested smaller body gets the
remaining budget after its own whole-artifact check, not a reset inside its
recursive inspection.

This is the recursive body before output reversal. The universal reversal law
is already proved, but the actual outer owner-renaming/SWAP graph and the
independently requested named Fourier root are not yet connected. No external
schema, production hierarchy seal, generic source, QPE or corpus gate is
completed by this checkpoint. [First sources and failures](../tests/fixtures/hierarchical_ir/fourier-recursion-first/README.md)
and [build/audit results](../tests/fixtures/hierarchical_ir/fourier-recursion-registry.json)
retain the evidence and limits.

### Actual shared wiring

The [wiring packet](../tests/fixtures/hierarchical_ir/wiring-packet.md) computes
axis routing directly from actual `rewire`, structural, tensor and sequence
bodies. The [pure inspector](../lean-kernel/QleisliKernel/Hierarchical/Wiring.lean)
starts with an empty cache and processes an untrusted selected dependency order.
Every result has a fresh finite derivation over the same definitions and
previously computed children. Missing dependencies, duplicate entries, cycles,
unsupported bodies, unequal widths and out-of-range axes reject. It never
accepts a producer route claim or expands a repeat. Returned square routes
have at most 16 axes; an empty route retains its independently checked owners.

Initial cache/order allocation, shallow scans, full fields, computed structural
routes and compositions consume one remaining structural budget. Only selected
wiring dependencies are summarized; H/phase children are not treated as identity.
An omitted independent root has no cache result: its caller must require and
bind the selected result. A route is not a typing, ownership or unitarity seal.
The actual whole-artifact checks remain mandatory. In particular, duplicated
axes or dropped zero-width owners can have a computable coordinate action but
fail the independent node-typing predicate.

[The complex interpretation](../lean/Qleisli/HierarchicalWiring.lean) proves
composition and tensor laws, then constructs actual physical evaluation from
the fresh-cache derivation. `inspect_evaluates` gives coefficient one exactly
at the computed basis routing and zero elsewhere, with no leaf-reader equation
or whole-graph interpretation premise. `inspect_joint_amplitude` applies to any
successful witnessing fuel and arbitrary correlated reference columns. These
are exact complex equalities, including scalar phase; the mathematical sums
are not executed by the inspector.

[Native checks](../tests/fixtures/hierarchical_ir/wiring-native.json) cover 93
outcomes and 2,736 independent basis/complex vectors for the actual outer QFT
renames and lifted SWAPs at widths 1–8, including shared dependencies, mutation
and capacity cases. Renaming tests this wiring component, without claiming
renewed finite-leaf evidence for the modified artifact. The whole width-eight artifact, recursive body and selected
wiring use 1,931,284 of 2,000,000 structural units. Ownership/type faults test
why coordinate checking alone is insufficient. This closes the actual-wiring
component; composing the full outer graph with the recursive Fourier body and
the independent named request remains open. No external schema or source/corpus
gate is enabled. [First sources and diagnostics](../tests/fixtures/hierarchical_ir/wiring-first/README.md)
retain proof and fixture repairs.

### Actual outer Fourier request

The [outer-root packet](../tests/fixtures/hierarchical_ir/fourier-root-packet.md)
connects those body and wiring components to the actual complete entry. Its
[pure inspector](../lean-kernel/QleisliKernel/Hierarchical/FourierRoot.lean)
receives an independently selected width and full interface for the
positive-sign, little-endian Fourier transform. The supported component profile
is width 1–8 with an outer sequence of 3–16 children. This does not restrict the
existing general IR: unsupported shapes are outside this additional inspector.

The actual entry must have the requested interface and width and be quantum-only
and unitary in its declared effect. Its first child must compute identity
routing, its second must pass the recursive Fourier-body inspector, and all
remaining actual children together must compute complete bit reversal. Every
required route must exist in the fresh wiring cache. Missing independent roots
therefore reject as well as missing dependencies. Equivalent orders of disjoint
SWAPs pass; submitted route summaries or asserted whole-circuit matrices are
never accepted as premises. Complete artifact typing remains mandatory.

The root's metadata, full interface comparison and route composition are
precharged. Recursive-body and wiring inspection then consume the same remaining
structural budget. The returned obligations contain actual finite H interfaces
and complete source bytes. Changing H to X or global -H may retain the inspected
outer structure, but fresh exact reconstruction rejects its pending equation.
A structural success alone is not a production evidence seal.

[The coefficient proof](../lean/Qleisli/HierarchicalFourierRoot.lean) constructs
the physical evaluation of that same actual entry. `inspect_evaluates` proves
its full matrix equals the independently defined positive-sign Fourier matrix;
`inspect_joint_amplitude` applies to arbitrary reference columns and any
successful evaluation fuel. The identity and reversal actions are derived,
and the only remaining semantic premises are the returned bound finite H
equations. The proof's matrix sums are not an executable checking algorithm.

[Native validation](../tests/fixtures/hierarchical_ir/fourier-root-native.json)
passes 74 outcomes, 40 fresh finite-H checks and 70 independent complex vectors.
It covers changed width/interface, missing or duplicated swaps, nonidentity
input routing, wrong phase/polarity, missing cache roots/dependencies and exact
or one-short budgets. Whole-artifact plus complete outer inspection costs
1,933,823 structural units at width eight. Renamed artifacts use a freshly
matched request for structural comparison; stale finite bytes still reject.

This closes the actual outer coefficient/request component. Production request
transport and sealing, native/finite-reader correspondence, remaining profile
rules, generic source and integrated QPE/corpus gates remain open. All external
schemas stay disabled; TP-005 projection APIs remain maintained until their
callers and pinned registry can migrate compatibly. [First attempts](../tests/fixtures/hierarchical_ir/fourier-root-first/README.md)
and [rebuilt audits](../tests/fixtures/hierarchical_ir/fourier-root-registry.json)
record this component's validation scope.

### Fourier request host

The [host packet](../tests/fixtures/hierarchical_ir/fourier-host-packet.md)
connects the complete-entry coefficient theorem to the existing
`interchange::hierarchical::Kernel::check_against` API. The external request
envelope stays `qleisli.hierarchy-request` version 1, profile
`qpe-dyadic8-v1`. The supported named form has `kind: equation`,
`effect: unitary`, entry zero and exactly one meaning with body `qft(width)`.
That meaning's full interface must equal the request header. The named boundary
is the published closed single `Bits<width>` register, including identical owner,
axis order and type at both endpoints. Merely having the same dimension is
insufficient; explicit adapters to `Bit` do not change the named meaning's type.

The untrusted Rust codec proposes only the outer wiring schedule and transports
the complete artifact and caller request. The private `QLF1` decoder checks the
singleton form again. The pure `FourierRoot.checkAll` first invokes complete
`Conditional.checkAll`, then the actual Fourier inspector with the remaining
structural budget and enforces `namedBoundary`. Full endpoint comparisons are
prepaid by the existing header charge. Its conditions theorem retains both
actual checker successes and the named boundary predicate.

The fresh native response contains ordinary finite proof indices and actual H
definition indices. Rust reconstructs every ordinary finite equation, then
checks every H against the independent exact matrix with the negative lower-right
entry, using the same remaining exact budget and actual full leaf interfaces
and bytes. The response must contain exactly the requested number of H indices;
duplicates, invalid indices, non-leaves and omissions reject. Both raw inputs
are retained by the private-field `CheckedRequest` report. No external API
accepts a serialized pending response, checked flag or precomputed H result.

`HierarchicalFourierRoot.checkAll_unitary` combines the actual coefficient and
conditional unitary proofs: the same constructed entry has the requested
unitary interface and Fourier matrix. `checkAll_reference_laws` proves both
inverse laws for arbitrary finite reference extensions. Both sets of finite
reader obligations remain explicit mathematical premises; host/native and
decoder correspondence have not silently become axioms or proved claims.

[Native host checks](../tests/fixtures/hierarchical_ir/fourier-host-native.json)
cover 187 independent binary framing cases and 39 host scenarios. Coordinated
changes to circuit and asserted meaning can pass artifact consistency while
failing the unchanged Fourier request: wrong phase, control polarity, repeat
count, missing reversal, X and global -H are tested. Renumbered definitions and
commuting disjoint SWAPs pass. Correctly typed adapters to a `Bit` or open owner
boundary reject the named request. Malformed subprocess responses cannot become
reports. All supported widths pass with cumulative width-eight work 1,933,823
and exact work 944; these limits were not raised.

This is an additive named-request path, not a production `VerifiedProgram` or
enabled external schema ID. The shared QFT fixture producer is connected;
the ordinary sized-source producer, remaining hierarchy/instrument rules,
native/reader correspondence and source/corpus release gates remain open.
[First attempts](../tests/fixtures/hierarchical_ir/fourier-host-first/README.md)
retain the actual boundary counterexample and repairs.

### Whole-space derivation implementation

The compatible [call expansion producer](../lean-kernel/QleisliKernel/Hierarchical/CallLowering.lean)
now expresses a typed call as two existing rewire nodes and a three-child
sequence. It appends the two adapters and retains the actual child index;
no child body or repeat is expanded. Its `plan_binding` and `install_other`
theorems bind generated metadata and preserve other actual definitions.
`plan` and `install` are untrusted data constructors, not evidence APIs.

The [coordinate interpretation](../lean/Qleisli/CallLowering.lean) proves that
this composition has coefficients `U(output_map⁻¹(y), input_map(x))` and
preserves a unitary child's whole-space laws and arbitrary reference maps.
Original call typing, including one consistent fresh renaming across both
endpoints, is an explicit premise; individually valid permutations are not
enough. The current native fixtures check this premise separately and submit
the generated nodes, independent meanings and evidence to the unchanged
ordinary derivation checker. Full external call translation validation and
source integration remain pending. No new acceptance rule or public enum
variant is introduced by this producer.

The [local rule matcher](../lean-kernel/QleisliKernel/Hierarchical/Rule.lean)
currently implements identity-encoded unitary equations for actual rewires,
explicit structural conversions, dyadic phase, ordered sequence, tensor,
inverse, control, repeat and the direct controlled-power schema below. Ordinary
rules use template version 1 and empty parameter/reference witness arrays.
Implementation and meaning children must equal the ordered endpoints of the
actual premise proofs. In particular, a zero repeat still has one checked
body premise; a `unitary` annotation alone never discharges it. Phase matching
uses exact `j,k` in the selected domain, including angles beyond the finite
coefficient ring. It has a distinct IR proof rule, not a new source primitive.

[Derivation.checkAll](../lean-kernel/QleisliKernel/Hierarchical/Derivation.lean)
first checks all structural tables and their dependency schedule. It creates
an empty internal proof cache, visits the proof nodes in that schedule and
requires every actual premise already established. Each shared proof is checked
once, with body/header/metadata matching and cache work charged to the same
two-million-unit allowance. It accepts no cache or success flag from the caller.
`powerEntry` additionally matches the independent exponent/provider request and
requires the projected provider proof to be established by that pass.

`step_invariant`, `scan_invariant`, `checkAll_conditions` and
`powerEntry_provider` prove finite closure of the actual supported derivations.
The [actual-body interpretation](../lean/Qleisli/HierarchicalSemantics.lean)
now proves ordinary rule preservation, direct-power preservation and the full
derivation induction. Its `Interprets` premise requires each actual definition
and meaning body to satisfy its interpretation equation; it never assumes
the proposed proof conclusions. Complete interfaces bind the phase target and
each operator's ordered axes. `checkAll_entry_sound` also binds the result to
the artifact's actual entry implementation.

The [complex instantiation](../lean/Qleisli/HierarchicalOperators.lean) uses
width-bounded complex coefficients, finite composition, tensor with first
operand on the low axes, conjugate transpose, coherent control and literal
repetition. `matrix_power` relates the latter to matrix exponentiation.
`checkAll_operator`, `checkAll_matrix` and `checkAll_reference` give exact
phase-preserving conclusions under the actual-body interpretation premise.
`powerEntry_operators` obtains the controlled-power provider equation from
its accepted derivation, rather than an additional assumed equation. These
mathematical sums and iterations are confined to the separate proof package;
the executable checker neither imports Mathlib nor evaluates these matrices.

The subsequent [constructed evaluation](../lean/Qleisli/HierarchicalEvaluation.lean)
removes the `Interprets` premise for these supported derivations. A total partial
evaluator follows actual body references with decreasing dependency fuel;
unsupported bodies, exhausted fuel and missing children return no value.
`evaluate_more` and `evaluate_unique` prove successful values persist and are
unique. `derives_evaluate` constructs sufficient fuel and equal successful
values from each actual finite derivation, including the two actual nodes of
the direct power schema. `checkAll_denotes` binds these denotations to the
actual entry implementation. Its complex operator/matrix/reference corollaries
therefore require no assumed semantic environment or provider equation.
`physical_ir_only` and `logical_ir_only` establish that changing proof metadata
cannot change either interpretation. Zero repetition still evaluates its body.

This evaluator constructs mathematical denotations, not the reference simulator
or a second, expansion-based verification path. Whole-space unitarity, finite
reconstruction, call/encoding/compute derivations, QFT/QPE schema integration,
external root-contract binding and execution correspondence remain required.
Unsupported cases currently reject. This internal equation theorem is not the
complete Soundness Theorem, a production semantic seal or an enabled external
registry entry. The [operator](../tests/fixtures/hierarchical_ir/operator-packet.md)
and [evaluation](../tests/fixtures/hierarchical_ir/evaluation-packet.md) packets
record scope, first attempts and remaining obligations.

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

The initial direct `controlled-power/1` projection reads implementation
`control(repeat(2^k, provider), true)` and logical
`control(power(providerMeaning, 2^k), true)` from their respective actual table
bodies. Implementation and meaning indices are different domains; table order
need not agree. The control is the leading `Bit` port at local coordinate zero.
The equation has exactly one provider-equation premise, with that exact
implementation and meaning, and whole-space identity input/output encodings.
Complete types, owner slots, axes and closed interfaces must match. A restricted
encoding cannot use this direct rule. Its template version is 1, parameters are
`[k, providerImplementation]`, and its extra witness-reference array is empty.
The independently selected request supplies `k` and the provider implementation;
a producer's own parameter list cannot substitute for that request.

[The actual Lean projection](../lean-kernel/QleisliKernel/Hierarchical/Power.lean)
implements these checks. `inspectEntry` first runs complete artifact typing and
dependency checking, then charges projection against the same remaining work
budget. It does not expand the repeated body or construct a matrix. The local
`inspect` helper alone does not establish whole-artifact validity.

Both results retain a **pending provider proof**, not a semantic receipt.
The [operator bridge](../lean/Qleisli/HierarchicalPower.lean) proves the actual
definition and meaning projections equal under that provider's exact equation;
unitarity additionally uses its explicit isometry premise. The reference theorem
compares complete joint maps. Generic derivation checking must still discharge
these premises on the same artifact, independently reconstruct finite leaves,
and match the caller's root contract. External decoding, schema enablement and
alternative efficient-power derivations remain open. The internal component
registry theorem is unchanged by this partial artifact integration.

QPE witness: fresh m-bit zero register; H on each precision bit; control bit k
applies U^(2^k) for k=0..m−1; inverse of the registered positive QFT; Z measurement
in ascending bit order. Require the exact controlled-power proofs and full
target output ownership. Schema instantiation checks all dimensions and binds
every stage to the actual definition. The theorem must establish the instrument
below, not only successful eigenstate outcomes.

The complete external schema declarations and executable acceptance theorems remain
**implementation obligations**. The QFT circuit component now has the
[proved Fourier/reference theorem](lean-qft-proof-packet.md), but its typed
hierarchical importer and full binding tests remain open. The
[closed component dispatcher](lean-qpe-instrument-packet.md#closed-component-dispatch)
now checks fixed IDs, versions and independent parameters against typed
QFT, single controlled-power and QPE witnesses. Its acceptance-to-semantics
theorems do not establish the external projection or provider premises.
A registry entry may be enabled
only after its theorem, importer/checker tests and explicitly stated remaining
native, transport and Rust finite-leaf proof boundaries are recorded. Existing
local equations can discharge parts
of those obligations; their mere presence is not schema-import support.

### Dependency scheduling implementation

[Hierarchical.Graph](../lean-kernel/QleisliKernel/Hierarchical/Graph.lean) checks
a proposed topological schedule of the combined dependency graph. External
table order need not be topological. An untrusted adapter proposes the schedule;
the executable checker reconstructs ranks, checks a complete index permutation,
and requires every actual edge to decrease rank. Its `check_acyclic` theorem
excludes nonempty cycles in the actual submitted dependency graph. It also
checks reachability, depth and shared work capacities without expanding bodies.

The [artifact preparation](#typed-artifact-preparation) now extracts edges from
typed definitions, meanings, encodings and proofs, including all zero-repeat
dependencies. A producer-supplied edge list cannot replace it.
Graph acceptance alone issues no semantic evidence and enables no wire format.
The existing desired shared-QPE source remains the motivating client; this
component does not make that source executable yet.

The graph pass uses the profile's 100,000-node, 1,000,000-reference, depth-256
and 2,000,000-visit ceilings. Its conservative charge is
`10 * nodes + 5 * references + 3 * roots`, including scans, rank/depth arrays,
edge lookups, schedule checking and reachability. `checkWithBudget` takes the
remaining allowance; the artifact preparer debits its own scans and comparisons
before invoking it. Subsequent semantic checks must continue that same budget.
No repeat count or dense matrix contributes
to this scheduling traversal. Reference counting stops as soon as its next
visit would exceed the allowance; it does not first compute every oversized
adjacency-list length. Root counting likewise inspects at most `nodes + 1`
entries before rejecting. The [native fixture](../tests/fixtures/hierarchical_ir/README.md)
includes permuted tables, shared graphs, cycles, unreachable entries and exact
capacity boundaries against an independent DFS oracle.

### Typed artifact preparation

[Hierarchical.Artifact](../lean-kernel/QleisliKernel/Hierarchical/Artifact.lean)
contains the four typed tables, all node constructors above, complete interfaces,
proof endpoints, ordinary data witnesses and an explicit implementation/proof
entry pair. References retain their table tag until their own table's bounds
have been checked. An out-of-range definition index cannot alias a meaning.
`project` reads the actual constructor fields to derive the combined graph;
premise, witness, encoding and count-zero body references all participate.
`prepare_acyclic` proves acyclicity of this actual projection after acceptance.

Preparation checks the complete prefix type tree, owner and wire uniqueness,
declared width, effect kind, angle/count bounds and endpoint binding. Classical
ports are separate from quantum owners; their Bit/Bits atoms mean CBit/CBits.
Unit and Bits(0) still occupy owner slots. Local IDs are labels; maps address
ordered slots and flattened axis positions. `endpoints_bound` establishes all
four exact logical/physical interface equalities, including axis order and zero
owners. Equation proofs cannot label an observe definition, and instrument
endpoints require the QPE meaning and identity encodings. These conditions do
not yet establish a node's typing or an instrument's meaning.

Scans, structural comparisons and reference allocation share the two-million
visit allowance. A preliminary constant-time size charge precedes traversal of
large arrays; conservative quadratic port charges precede uniqueness checks.
Repeated comparisons against a shared interface are charged each time. Graph
scheduling receives only the remainder, and `prepare_conditions` proves the
accepted aggregate charge is within the ceiling. Aggregate opaque finite
payload storage is capped at 16 MiB here; the external decoder must additionally
bound the complete encoded artifact, including headers.

This pass returns **prepared data, not semantic evidence**. Opaque finite bytes
have not yet been decoded or verified. The subsequent typing passes integrate
port maps, node effects and meaning/encoding headers. Finite-leaf reconstruction,
derivation rules, schema projections and comparison
against an independently supplied required contract remain mandatory later
steps. A deliberately well-formed phase mutation passes preparation and must
fail the future semantic pass. No external format or schema is enabled by this
component. The [native record](../tests/fixtures/hierarchical_ir/README.md)
keeps the first source, repairs, dependency mutations and shared-budget limits.

### Complete side-map checker

[Hierarchical.Ports](../lean-kernel/QleisliKernel/Hierarchical/Ports.lean)
implements the single-side map contract above. It constructs canonical
coordinates in port/axis order, computes candidate inverses from actual map
arrays, and checks both inverse laws using the existing proved layout
definitions. Owner, axis and classical maps cover their full domains. Type
identity includes tuple arity, nesting, Unit and the declared Bits width;
equal dimensions do not authorize a conversion. Arbitrary local IDs remain
labels and cannot be substituted for map positions.

`check_owners`, `check_axes` and `check_types` concern this executable checker.
`check_reference_round_trip` proves coefficient reindexing is inverted without
altering an arbitrary reference coordinate; it assumes no product state.
Classical maps preserve full classical slot types as well. Their bijectivity
is a boundary-map condition, not a restriction on copying classical values
inside an operation.

The checker accepts only a caller-supplied remaining allowance within the
profile ceiling and returns its charge. Constant-time array-size checks precede
traversal; wire counts use sizes before allocating flattened coordinates.
The enclosing node pass must subtract each returned charge from the shared
allowance. The checker does not yet validate both sides of a call together,
freshness across that call, an arbitrary node body or a semantic equation.
The native fixture includes 39 map cases and the exact 592/591-visit boundary
for a single Bits(0) owner. No public acceptance rule is enabled here.

### Definition-node typing

[Hierarchical.NodeTyping](../lean-kernel/QleisliKernel/Hierarchical/NodeTyping.lean)
now applies the local definition rules to actual constructor fields and child
headers. Calls use both complete side maps and one injective identity relation
across their endpoints, separately for owners, wires and classical values.
Sequence checks exact intermediate interfaces and effect joins; tensor checks
disjoint frames across both endpoints. Repeat and inverse enforce their unitary
conditions; control requires a distinct leading Bit. Phase, initialization and
measurement check their named owners, effects and complete surviving frames.
In particular, zero-width owners cannot disappear during measurement.

`checkAll` first prepares the actual artifact, then checks every definition
once, including all zero-repeat bodies. All scans, compared child headers and
side maps consume the same remaining work allowance. Index-list allocation is
charged before constructing that list. `checkAll_conditions` proves actual
preparation succeeded, every indexed definition satisfies the local conditions,
and total visits are at most two million. This is a compositional structural
typing result, not a proof that a leaf has its asserted effect or equation.

Finite leaf bytes still require independent reconstruction and exact checking.
The computed node checks its referenced C/W/u/E interfaces and zero-scratch
encoding constructor; the next pass checks the encoding's own typing. C/W
unitary semantics and the W E = E u premise remain derivation obligations.
A wrong but well-typed phase still passes this stage and must fail the
semantic rule checker. Meaning/encoding semantics, derivations,
schema/provider projections and external request binding remain open.

### Meaning and encoding typing

[Hierarchical.ContractTyping](../lean-kernel/QleisliKernel/Hierarchical/ContractTyping.lean)
now implements the structural meaning and encoding rules above. Its whole-table
entry first calls the actual definition-node checker, then validates every
shared meaning and encoding. `checkAll_meaning` and `checkAll_encoding` connect
acceptance to the actual indexed objects. `checkAll_conditions` also carries the
previous pass and proves the aggregate work remains within two million visits.
All table/list allocation, compared headers and maps continue the same budget;
no repeated body or dense matrix is evaluated here.

The native fixture checks every meaning/encoding constructor, all 64 QPE n/m
header combinations, retained target and CBits binding, finite width 6/7 limits,
explicit private zero-width owners, and invalid meaning bodies under zero power.
It also confirms that coherent control rejects implicit target type conversion
while permitting consistent local names of the same ordered target types.

This completes structural typing of those tables, not their semantic proof.
Opaque finite descriptions still need independent decoding and exact checking.
Provider and compute unitarity, zero-scratch entry/return, rule equations,
actual schema projection and the consumer's independently required meaning are
not inferred from these headers. All external schemas remain disabled.

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
