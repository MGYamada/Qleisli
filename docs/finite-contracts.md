# Finite exact semantic and function contracts

Normative bounded SC/FC contract for v0.2.x; consolidates the adopted v0.1
supplements without changing acceptance. The Rust path is implemented/tested;
general Rust/source/extraction/simulation adequacy remains unproved. Mathematical
rule soundness, actual Lean component proofs, numerical tests and intended
specification review are separate ([formal scope](formal-core.md)).

## Semantic equation and entry

SC-1 fixes logical/physical types, operators and isometric encodings independently
of the implementation:

```text
u : L_in -> L_out,       u†u = I
E_in : L_in -> P_in,     E_in†E_in = I
E_out : L_out -> P_out,  E_out†E_out = I
U E_in = E_out u.
```

Initial physical circuits are square unitary on one finite basis type. Logical
u/encodings may be rectangular; square u is unitary. Scalar phase is exact.
SC-2 retains full type trees, ordered holders/axes, effect and coordinates;
first product field occupies low bits, index(a,b)=a+2^bits(A)b. Equal dimensions,
images or widths do not identify encodings/types. `Q<Unit>` remains linear.
Changing coordinates requires explicit checked transport.

SC-3 requires actual entry in image(E_in): checked preparation, exactly matching
previous output encoding, or a scoped construction. Owning physical wires and
`check_entry`'s interface comparison alone do not establish a runtime state
premise. Tensor the equation with I_R for every reference; it applies to
correlated pure/mixed states without a product-state assumption.

## Exact checking and immutable binding

SC-4 checks untrusted circuits/encodings/equations through independent IR
verification and exact arithmetic. A name, digest, source identity or cached
success is not evidence. Bind the actual circuit, complete contract, ordered
interface and issued dependency identities; changed implementations require
fresh certification before substitution.

The fixed ring is `Z[ζ8,1/2]=Z[1/2,sqrt(2),i]`. Canonical dyadic coefficients
in basis `(1,sqrt(2),i,i sqrt(2))` have signed i128 numerators and denominator
exponents ≤126. Unsupported entries, overflow and exhausted limits reject;
no floating tolerance issues evidence. Intermediate evaluation may exhaust even
when another evaluation order fits. [Future domains](coefficient-domains.md)
change neither this ring nor clean-release obligations.

| Capacity | Bound |
| --- | --- |
| Dense logical/physical circuit width | 6 bits, including control/scratch; matrices at most 64×64 |
| Flat circuit | 1,024 steps |
| Contract basis tree | 128 nodes, depth 32, root depth zero |
| Raw certified-compute exact work | Shared 10,000,000 charged scalar operations/program; each region also capped at that default |

Public Rust APIs take a caller `Budget`; raw verification supplies the fixed
default. Every equation/isometry/interpretation spends shared work. Source
checking has separate capacities. All limits/ownership rules remain mandatory.
`BasisType::{Unit,Bit,Pair,Tuple}` retains exact trees; Tuple has ≥3 immediate
fields, two fields use Pair, zero/one-field Tuple rejects. No reassociation.

[Contract API](../src/contract/mod.rs): Circuit binds type/ordered steps;
Encoding binds logical/physical types and a checked rectangular isometry;
Contract fixes encodings/u. Private immutable CheckedContract is created only
by successful checking or checked rule constructors. `check_binding` requires
full structural equality; `check_entry(Option<&Encoding>)` compares exact input
encoding and returns output encoding, without state-indexed ownership.
Untrusted descriptions and serialized evidence are rechecked at final IR.

## SC evidence rules

Write C(U;Ei,Eo;u) for the checked equation with the preceding premises.

| Rule | Required construction and conclusion |
| --- | --- |
| SC-EQ | Validate actual circuit and all three isometries; compare every entry of UEi and Eou. Probabilities, selected columns or Eo†UEi without leakage checking do not suffice. Identity uses IE=EI on a checked encoding and empty validated circuit. |
| SC-SEQ | Matching complete middle encoding: C(U1;E0,E1;u1), C(U2;E1,E2;u2) yield C(U2U1;E0,E2;u2u1). Check actual emitted composition. |
| SC-TENSOR | Disjoint owned interfaces and explicit order; tensor implementations, encodings and logical operators. Valid also on entangled inputs. |
| SC-ADJOINT | Both U and u unitary; reverse/invert actual steps and swap encodings. U†Eo=Ei u†. Not available for arbitrary logical isometries/preparation. |
| SC-CONTROL | U/u unitary and Ei=Eo=E; distinct control, phase-preserving actual circuit. C(U)(I_Bit tensor E)=(I_Bit tensor E)C(u). Unequal encodings reject. Mathematical unitarity grants no opaque controlled access. |
| SC-REUSE | Reuse only the bound circuit/contract/interface; certify changed implementations separately. |

Finite acyclic rule induction gives exact equations and arbitrary-reference
stability. This paper argument proves no Rust implementation/search correctness
or evidence-finding completeness. Evidence constructors preserve independent
well-formedness, physical unitarity, logical isometry, ownership and capacities.

## Certified computed source and raw region

SC-SOURCE is a language form, not a stdlib function:

```qli
with_computed(q, f, u) { |d, a| body }
```

Evaluate q once before static name resolution; live/spent locals hide globals.
f/u participate in nonrecursive dependency checking. q is consumed Q<A>;
f is total packed-domain A→Bit (multiple parameters left-associated, zero
parameters Unit); u is declared unary `unitary Q<A>→Q<A>` without classical
ports, or an eligible sealed one-bit unitary. Distinct private d:Q<A>,a:Q<Bit>
replace q. Body is Unitary and returns exactly `(Q<A>,Q<Bit>)`, in data/aux
order, with every private owner covered. Form returns Q<A>, joining q's effect.

Body isolation captures no outer quantum or classical value. Outer owners stay
in the complete frame, including pending/caller holders. Outer names remain
unavailable placeholders, preventing shadowed declarations from reappearing;
binders may reuse masked outer-owner spellings without consuming them. Closed
classical computations/branches are allowed only when the finite extractor can
resolve them. Unsupported type-correct unitary bodies reject. Data may split,
rejoin and change; exact output tree and axis transport are checked. Q<Unit>
must return explicitly. Six-bit checking allows at most five data bits plus aux;
body/logical circuits each obey 1,024 steps.

SC-COMPUTED fixes the actual ordered body W and independently compiled u:

```text
E0|x> = |x,0>,   Cf|x,a> = |x,a xor f(x)>,   Ef=Cf E0
W Ef = Ef u
Cf† W Cf E0 = E0 u.
```

Cf is a permutation, Ef is isometric even for noninjective f. The equation
proves exact zero/separation and logical u for every input/reference. It is
not permission to assert encoding for an arbitrary state or expose Release0.
Failed relation rejects even when ownership/unitarity pass.

Raw `CertifiedCompute` binds f/table, actual use_steps/logical_steps and complete
interface/output order, retaining the physical scope. Independent verification
rechecks equality under shared budget. Static extraction may replace that whole
proved clean scope by u; the physical witness stays inspectable. Old two-argument
`with_computed(q,f){|a|...}` keeps its original identity/Z/T-chain rule.

[Executable examples](../examples/semantic_contracts/README.md) cover Z_aux→Z,
H_aux;H_aux→I, and simultaneous data/aux X→X. Reject aux-only X, Z with requested
I, data-only X leaving the relation, capture, observation, wrong returned order,
implicit discard, nonunitary logical target, malformed evidence and exhaustion.
Asymmetric predicates, output permutations, entangled references and empty
owners need independent regressions, not merely zero-input execution.

## Function application and extraction

FC-1 fixes ordinary implementation/specification with the same exact unary
`unitary Q<A>→Q<A>` signature, no classical ports, and full-space equality U=u.
Different private auxiliary layouts may implement that same public operation
only through checked cleanup. Nonidentity public encoded-state handles and
observation contracts need separate extensions.

FC-SOURCE/FC-APPLY is the reserved language form:

```qli
apply_contract(implementation, specification, input)
```

Evaluate/consume input once before resolving both names. Targets must be
ordinary declared unitary functions, not runtime operation values; include
both in dependency checks even unused or under zero repetition. Require exact
source type trees and all ordinary ownership/pending-frame rules. Return one
fresh token for the same ordered Q<A>; join input effect with Unitary. An iso
whose body happens to be unitary remains ineligible. Successful equality to the
supplied specification does not establish its intended algorithmic meaning.

FC-CHECK, [independent function checker](../src/contract/function.rs): validate
both original raw programs and all nested evidence, complete ownership/fresh
IDs/effects/interfaces; independently extract ordered pure circuits including
returned-axis transport, phases and embedded contract actions; compare every
exact entry; bind both programs/circuits/signature/names/frozen source records.
Do not call frontend flattening or skip unsupported constructors.

Extractor supports gates, split/join, equal-width permutations, ApplyUnitary,
QuantumIf, closed classical constants/Booleans/branches, protected compute and
certified compute. Both arms are validated; selected-arm phi reads all classical
inputs from pre-merge records and transports all quantum phi. Preparation,
observation, classical ports and width-growing lifts are outside this function
profile. Certified-scope substitution uses the established SC-COMPUTED equation
and retains original physical raw bodies. General source/typing lowering
adequacy remains a separate obligation.

| Function capacity | Bound |
| --- | --- |
| Public interface | 6 bits; contract tree 128 nodes/depth 32 |
| Raw operations | 1,024/function, both branch arms counted |
| Retained flat steps | 1,024/function including submitted use/logical circuits |
| Extracted circuit | 1,024 steps |
| Classical branch nesting / evidence dependency depth | 32 each |
| Dependency-expanded circuit | 1,000,000 leaf steps each for implementation/specification; empty body costs one |
| Frozen identities | 128 sources, 1 MiB names+bytes, names ≤4,096 bytes |
| Work | One caller budget over metadata, preflight, both validations, extraction and comparison; nested checks never reset it |

Reject excessive inputs before deep clones/recursion. Individual bounds do not
guarantee that shared exact/work capacity fits.

## FC evidence, caching, transforms and execution

FC-OPAQUE: private immutable FunctionEvidence shared by Arc retains actual raw
bodies, checked operator/circuit, signature, names and source records. No unchecked
public constructor. Clone preserves issued proof identity; separately checked
equivalent operators have distinct dependency identities. `check_binding` compares
all own snapshot/identity fields and nested issued identities; changed dependencies
require rebinding. Initial safe construction is acyclic. Portable graphs use the
separate [QIRF decoder](machine-interface-spec.md), not arbitrary proof code.

FC-CACHE: within one frozen compiler instance, cache keys include complete
resolved declarations/signature/dependencies. No cross-compilation cache.
Shared immutable full-project source snapshots (including unrelated modules,
comments and std) spend source-copy work once before copying; each receipt still
checks metadata/equality and pair/raw work. Public owned FunctionIdentity and
identity() remain compatible; bounded lazy owned views do not weaken exact public
binding. Changed disk files do not change a theorem about frozen inputs or certify
new ones. Bytes establish provenance/mismatch detection, not source preservation.

FC-IR retains `CircuitAction::Contract {indices,evidence,adjoint}`; enclosing
CircuitStep carries controls. Check ordered distinct in-range targets, matching
width and disjoint distinct controls. Empty indices may carry a scalar phase;
Q<Unit> ownership still consumes/returns. Remapping/tensor/sequence/repetition
retain evidence and order; adjoint reverses steps/toggles flag; coherent control
retains both branch actions/phases. Zero repetitions still check eligibility.
Do not replace an action with an unbound sequence. Backend replacement needs a
checked correspondence at its final boundary.

FC-EXECUTE: exact interpretation may use checked logical matrix; numerical
reference execution uses extracted implementation circuit on actual target axes
with recorded adjoint/controls, including justified cleanup substitutions. It
never executes specification as a second call. Whole-run max_execution_steps
(default 1,000,000) is shared over branches/components; charge expansion before
recursive execution. Individually valid receipts may exceed this runtime budget.
State the executed representation when reporting resources; physical snapshots
need not allocate auxiliaries already removed by checked substitution.

FC-THEOREM/FC-STATIC are conditional paper equality/reference/transport/inverse/
tensor/composition/power/control laws, assuming valid independent raw checking,
exact primitive interpretation and meaning-preserving extraction. They do not
prove Rust cache/checker/compiler/simulator correctness or opaque device access.

[Substitution examples](../examples/function_contracts/README.md) and
[regressions](../tests/function_contracts.rs) keep one fixed public Z contract
while replacing direct/private-cleanup implementations in unchanged clients,
including control, adjoint, repetition and entangled frames. Wrong scalar,
asymmetric output axes/predicate, stale binding, missing empty owners, invalid
controls, lost evidence or unsupported work must reject. V01-C1–C6 audits the
combined path; one matrix API/example alone does not complete a milestone.
