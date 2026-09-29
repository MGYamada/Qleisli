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

### Whole-space derivation implementation

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
