# Selected bounded hierarchy and evidence profile

Status: **M2 architecture/profile specification, not implemented**
(2026-09-27). This settles the joint IR/evidence, schema-import and first-QPE
profile decisions raised by the v0.1.4 review. The M1 extension specification
is [separate](next-minor-spec.md). Sized source grammar, generalized standard
APIs and their G020-1 extension review remain M2 work; this document fixes the
checker/IR contract they must satisfy. No current research rule or Lean theorem
is credited with implementing the new profile.

## Scope and representation

Select `qleisli.hierarchical-ir` version 1 with profile `qpe-dyadic8-v1`.
The outer serialization follows the strict JSON, integer, duplicate-key and
bounded parsing rules of [the machine interface specification](machine-interface-spec.md).
Its root fields are `format,version,profile,definitions,meanings,encodings,
proofs,entry`. References are u32 array indices. Each shared table is a DAG;
reject cycles, out-of-range references, unreachable entries and unknown nodes.
Do not accept current QIRF under this format by changing only its header.

An interface is an ordered list of `(owner,type,axes)` quantum slots and ordered
classical slots. Types preserve Unit nodes and pair structure, with the new
finite `Bits(n)` shape retaining its declared n and little-endian axis order.
`Bits(0)` is a zero-wire owner, not no owner. Define its basis as integers
0≤x<2^n, bit k carrying 2^k. All quantum slots occur exactly once at input/output
unless the node's specified effect consumes/creates them. Axis permutations
are explicit bijections; wire IDs or dimension equality cannot identify trees.

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

## Meanings, encodings and derivations

Meaning nodes are `identity(type)`, `finite(table-or-matrix,type)`,
`sequence(children)`, `tensor(left,right)`, `inverse(child)`,
`control(child,polarity)`, `power(child,count)`, `rewire(permutation)`,
`phase(j,k)`, and `qft(m)`. The finite node uses existing exact scalars
`a+b√2+i(c+d√2)` with signed dyadic coefficients; only bounded leaves may
materialize a matrix. Every node has a checked exact interface. QFT means
`F_M[y,x]=exp(2πixy/M)/√M`, M=2^m, with positive sign and little-endian basis
indices. A named meaning is not executable access or evidence of a circuit.
Instrument meaning for the QPE observation entry is specified below; it is not
reduced to equality of outcome probabilities on eigenvectors.

Allowed encodings are `identity(type)`, `tensor(left,right)`,
`rewire(child,permutation)` and `zero_scratch(type,scratch_bits,compute)`.
The latter is E|x>=C(|x>⊗|0_s>), with a checked whole-space unitary C;
E is isometric by construction. It authorizes release only after checked
uncompute restores exactly the zero product factor for every admitted x and
reference. Having E's description is not evidence that a runtime input lies
in its range. Entry is established only by the enclosing fresh-zero/compute
scope or a preceding checked encoding transition. Encodings cannot be asserted
by a `Clean` name, lifetime, provider field or user-supplied arbitrary matrix.

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
module/declaration, source revision, template version and Rust checker entry.
The release build must compile and axiom-audit the declaration and compare its
exported type with the manifest. This establishes the manifest's Lean theorem,
not Rust correspondence. The external artifact supplies only registry ID,
bounded integers, premise references and an IR witness. The verifier chooses
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

QPE witness: fresh m-bit zero register; H on each precision bit; control bit k
applies U^(2^k) for k=0..m−1; inverse of the registered positive QFT; Z measurement
in ascending bit order. Require the exact controlled-power proofs and full
target output ownership. Schema instantiation checks all dimensions and binds
every stage to the actual definition. The theorem must establish the instrument
below, not only successful eigenstate outcomes.

These Lean schema declarations and their Rust correspondence are **obligations
for implementation**, not newly proved results. A registry entry may be enabled
only after its theorem, importer/checker tests and explicitly stated remaining
Rust proof boundary are recorded. Existing local equations can discharge parts
of those obligations; their mere presence is not schema-import support.

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
| H2 schemas | Pinned Lean statements and axiom audit; matched templates and negative premise/layout/angle cases; record which Rust acceptance-to-model correspondence is still unproved. |
| H3 scaling | One shared QPE/QFT definition instantiated at (n,m)=(1,3),(2,4),(8,8); report all size/work metrics, forbid any dense matrix above six bits and any expansion of shared repeated bodies during checking. |
| H4 semantics | Small exact admissible-angle comparison; π/8/finer schema cases; independently computed QPE instrument on superpositions/entangled references at small widths, not only exact eigenphases; preserve target ownership. |
| H5 failure/migration | Cycles, deep inputs, zero-repeat invalid bodies, limits, wrong theorem registry/version and forged entry evidence; old adapter round-trip and explicit reverse-adapter rejection. |

H1–H5 are unexecuted future gates. Only their specification is completed here.
They do not replace the separately required executable V1-C1–C5 evidence.
