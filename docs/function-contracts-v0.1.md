# Function contracts and evidence retained through static transformations

Status: **bounded implementation and regression coverage; English specification
supplement** (2026-09-27). This
English supplement connects the [finite exact contract kernel](semantic-contracts-v0.1.md)
to ordinary source-function boundaries. It supplies the V01-C3 and
V01-C5 path in the [release milestones](release-milestones.md), whose acceptance
audit combines this path with the SC kernel and source extension. Implementation
and regression results are recorded in the
[conformance ledger](specification-status.md).

The purpose is to let a client name the operation it requires separately
from the implementation selected to perform it. Checked evidence binds those
two definitions and remains attached to calls after inverse, control,
repetition, and axis transport. This supports the project north star: the
concepts used to reason about an algorithm should also be the concepts used
to express its program, with their implementation correspondence checked.

## 1. Public meaning and interchangeable implementation

**FC-1 — Fixed client contract.** For one finite source basis type A, let
the specification be an ordinary function with exact signature
`unitary fn specification(q:Q<A>)->Q<A>`. Its compiled pure operator is u.
An implementation is a separate ordinary function with the same exact
signature and compiled operator U. The client requires

```text
U = u : H(A) -> H(A).
```

This is the same-encoding instance `U I_A=I_A u` of the finite contract
equation. Exact phase and complete output-axis order are part of equality.
The specification is a fixed input to checking; the checker cannot derive a
new public operation from U and use that as the required meaning.

The public interface has one owned register and no classical ports. The
implementation may use private auxiliaries through independently checked
cleanup forms. Consequently different physical implementations, including
different private widths, can expose the same public contract. Each retains
its own physical raw IR and cleanup evidence. A different width is not hidden
by silently discarding an output or weakening an ownership check.

The first function boundary deliberately uses identity public encodings.
General nonidentity entry/output encodings, encoded-state handles, first-class
operation parameters, and contracts with classical ports are not introduced
by this form. The separate Rust finite-contract API continues to express
explicit isometric encodings; carrying their entry promises as source state
types requires additional rules.

## 2. Source language form

**FC-SOURCE — Classification and grammar.** `apply_contract` is a **language
form**, not an ordinary standard-library definition or a newly imported sealed
gate. It is a reserved keyword; an existing ordinary identifier with that
spelling must be renamed. Its grammar is

```ebnf
ApplyContract ::= "apply_contract" "(" Name "," Name "," Expr ")"
```

In `apply_contract(implementation,specification,input)`, the first two operands
are statically resolved ordinary function names, not runtime operation values.
Both targets participate in declaration dependency/cycle checking, including
when the form occurs in an unused declaration or in a zero-count static
target. A contract cannot make recursion or an invalid target unreachable to
checking.

The input expression is evaluated and consumed exactly once, before either
target name is resolved. Name hiding, signature checking, and resolution
use that residual environment: a local value or
spent local name hides the corresponding function until its scope ends.
Each target is checked in its defining module with its own parameters and
imports, without caller capture.

Both targets must be ordinary definitions. Sealed names such as `h` or `z`
are not eligible directly; a user may wrap one in an ordinary unitary function
with the required signature. The public interface is bounded at six bits.
Independent evidence checking imposes additional raw-program, circuit,
nesting, provenance-size, and exact-work limits, recorded with the implemented
checker. Exceeding any limit rejects evidence construction.

| Item | Required type, ownership, and effect |
| --- | --- |
| implementation | Ordinary declared `unitary` function with exactly one parameter `Q<A>` and result exactly `Q<A>`. |
| specification | Ordinary declared `unitary` function with the same exact input/output type tree. |
| input | One owned `Q<A>`, evaluated once and consumed by the form. |
| result | One owned `Q<A>`, with a fresh IR token and the complete ordered public interface. |
| effect | `Unitary` for the contract call, joined with the effect of evaluating input. |

The targets have no ordinary classical parameters or results. Closed
classical computations in their bodies are eligible only when independent
static extraction can resolve them into the supported finite pure circuit.
Calls use their declared effect: an `iso` declaration is not accepted merely
because its current expanded body happens to be unitary.

Use exact type-tree equality, not only equal width or matrix dimension.
`Q<(Bit,Unit)>` and `Q<Bit>` are different signatures. `Q<Unit>` remains one
linear owned input and output even when the circuit has no target axes.
The form grants no copying, implicit discard, outer quantum capture, or
exception to normal pending-frame accounting. Distinctly owned surrounding
registers may be entangled with the argument and must remain in the frame.

Conceptually, the rule is

```text
E ; F ; R |- input => q(s,A):Q<A> ! eps ; E1 ; R1
implementation and specification resolve under the static name rule
both target signatures are exactly ordinary unitary Q<A> -> Q<A>
independent function evidence establishes U = u for their actual IR
---------------------------------------------------------------- FC-APPLY
E ; F ; R |- apply_contract(implementation,specification,input)
  => q(s,A):Q<A> ! eps join Unitary ; E1 ; R2
```

This is a contract application at a function boundary. Successful checking
establishes equality to the supplied specification's operator, not that the
specification solves an external mathematical problem. The author's separate
proof or independent expected-result check still relates that specification
to its intended algorithmic meaning.

## 3. Independent whole-function evidence

**FC-CHECK — Inputs to checking.** The
[independent function checker](../src/contract/function.rs) implements
`FunctionEvidence::check`, which takes the
implementation and specification raw programs, their common exact signature,
resolved identities, and the frozen source/dependency records used to compile
them. It performs the following checks before constructing evidence:

1. Independently validate both raw programs, including linear input/output
   coverage, issued IDs, effects, all embedded instructions, and all private
   auxiliary evidence. Require one public quantum input/output register,
   no classical ports, and the common signature's width.
2. Independently extract each validated ordered pure circuit. Include the
   complete returned-axis transport, exact phases, and every embedded
   contract action. Reject an unsupported raw construction rather than
   treating it as identity or skipping it.
3. Interpret the finite circuits exactly, and require equality of all
   operator entries with the declared tensor convention. A probability
   comparison or equality up to scalar phase does not qualify.
4. Bind the resulting checked equality to both actual programs, their
   ordered circuits, the exact signature, and their frozen provenance.

Source type trees are checked before width-based raw-IR erasure. Raw
verification alone cannot reconstruct those trees. The typed function
evidence retains the signature, while general correctness of source typing
and lowering remains an explicit implementation-adequacy obligation.

The extraction rule for an existing certified compute region uses its
already independently established relation `Cf† W Cf E0=E0 u`. Replacing that
region by u in a pure circuit is justified by that relation, including phase
and arbitrary reference extension. The original physical region remains in
the evidence's raw implementation snapshot. A claimed logical circuit does
not bypass validation of W or cleanup.

The initial independent extractor handles the existing sealed gates,
split/join, equal-width basis permutations, `ApplyUnitary`, coherent
`QuantumIf`, closed classical constants/Boolean operations and branches,
structured protected compute/use/uncompute, and verified `CertifiedCompute`.
It is separate from the frontend's static flattening implementation. A
selected classical branch transports every quantum phi and evaluates all
classical phi inputs in the pre-merge record; the unselected branch was still
validated independently. Preparation, observation, classical ports, and
width-changing lifts are outside this unitary function profile.

| Initial function-checking limit | Bound |
| --- | --- |
| Public interface | Six logical bits; contract type trees also retain their 128-node/depth-32 limits. |
| Raw operations | 1,024 per function, counting both arms of every branch. |
| Retained flat steps | 1,024 in total per raw function, including submitted use/logical circuits. |
| Independently extracted circuit | 1,024 steps. |
| Classical branch nesting | 32 levels. |
| Checked function dependency depth | 32, including nested retained evidence. |
| Expanded function circuit | At most 1,000,000 leaf steps for each implementation and specification circuit, including nested evidence; an empty body conservatively costs one. |
| Source identity | At most 128 source records, at most 1 MiB across names and source bytes, and 4,096 bytes per name. |
| Exact work | One caller-supplied shared budget across metadata/preflight, both raw validations, extraction, and exact comparison; nested checking must not reset it. |

The profile rejects unsupported or excessive inputs before deep cloning or
recursive processing. It does not imply every shape under these individual
limits fits the shared work or exact-arithmetic budget. Source compilation
may impose additional project-wide limits. Evidence attached to a call is
reused without reevaluating dependency bodies as dense matrices.

**FC-OPAQUE — Evidence ownership.** A checked `FunctionEvidence` value is
immutable, has private fields, and is shared through `Arc`. There is no public
unchecked evidence constructor. It retains the checked circuit/operator,
both actual raw functions, their common exact signature, names, and source
records. Its existence certifies the stated finite equality; it is not itself
ownership of any runtime quantum state.

Evidence equality identifies an issued proof object, not arbitrary semantic
equivalence. A clone preserves the private proof identity. Separately checking
the same operator creates a different dependency identity. Comparing nested
evidence therefore takes constant time per dependency, rather than recursively
expanding a shared proof graph. `check_binding` compares all of its own source
records and raw snapshot fields, with nested dependencies compared by their
issued identities. Replacing even an equivalent dependency requires rebinding
or checking a new enclosing artifact.

Embedded dependencies use previously checked immutable evidence. This gives
a finite acyclic construction graph; the initial API does not load arbitrary
serialized proof graphs or permit cyclic evidence references. Raw fields and
source provenance supplied before construction remain untrusted. A function
name, an annotation, or possession of arbitrary source bytes is not sufficient
to obtain checked evidence.

**FC-CACHE — Reuse and identity.** Compilation may cache successful evidence
for a resolved implementation/specification pair within its frozen project
snapshot. Its key and validity boundary must include the common signature
and all declaration/dependency information that determines either program.
No cache entry may silently survive a changed source dependency, predicate,
output layout, or required specification.

The current frontend retains all loaded project source records in each new
artifact, including unrelated modules; this is a conservative snapshot rather
than a minimal import/declaration closure. It charges the actual source/raw
snapshot copies once per newly checked implementation/specification pair.
Within one private compiler instance, resolved declarations and checked
dependencies remain immutable, so cache hits reuse the issued evidence without
repeated byte/raw comparisons. The cache is never shared across compilations.
Public `check_binding` still compares supplied identities and raw snapshots
exactly. No digest or hash-collision assumption replaces that public check.

An already constructed immutable artifact remains a theorem about its frozen
programs after files on disk change. It does not automatically become a
theorem about the new files. Reusing it for a new compilation requires an
exact binding comparison to the new inputs or fresh checking. Source bytes
and names provide provenance and mismatch detection; they do not prove that
the compiler translated those sources correctly.

Checking an already certified call or its static transforms need not repeat
dense equivalence checking. It still validates the call's current ownership,
target axes, controls, type/interface association, and evidence binding.
Private immutable evidence supplies the previously checked semantic premise.

## 4. IR representation and transformations

**FC-IR — Contract action.** The flat circuit action is

```text
CircuitAction::Contract {
    indices,
    evidence: Arc<FunctionEvidence>,
    adjoint: bool
}
```

`indices` is the ordered placement of the evidence's public register in the
current circuit. The enclosing `CircuitStep` carries any coherent controls.
The evidence fixes the exact function signature and operator; the action
does not select a new specification by name at runtime. The boolean selects
the ordinary or adjoint operation, with its exact phase.

Independent raw verification requires a valid checked evidence value,
exact target width, distinct in-range target axes, and distinct in-range
control axes disjoint from those targets. It preserves zero-width actions:
an empty indices list can still denote a nontrivial scalar phase. The ordinary
IR ownership token is still consumed and returned for `Q<Unit>`.

The evidence object remains part of the actual action after transformations:

| Transformation | Required action/evidence behavior |
| --- | --- |
| Axis remapping | Remap every target and enclosing control axis in the declared order; retain the same evidence and adjoint choice. |
| Sequential composition | Retain each checked action and its execution order; validate matching ownership/interfaces. |
| Tensor placement | Place target axes on disjoint ordered interfaces and retain evidence for each factor. |
| Adjoint | Reverse the operation order and toggle each contract action's `adjoint` bit; preserve its evidence and controls. |
| Coherent control / `qif` | Add the distinct external control condition to the enclosing step; retain both branch contract actions and their relative phases. |
| Finite repetition | Repeat the retained action in order; count zero still performs target and evidence eligibility checks. |

These transformations must not erase the evidence and replace the action with
an unbound gate sequence. A backend may emit an equivalent circuit only under
a checked transformation record that retains the implementation/contract
relation required at its final boundary. The first retained-action path does
not specify an external backend or a portable proof serialization format.

**FC-EXECUTE — Executed operator.** Exact contract interpretation may use
the cached checked logical matrix. Reference execution runs the independently
extracted checked implementation circuit on the actual target axes, with the
recorded adjoint/control transformations. That circuit may already contain
justified substitutions for private cleanup regions. Its equality to the
retained raw physical implementation follows from the extraction premises.
The source specification is not executed as a second runtime call and no
measurement comparison supplies the equality certificate.

The per-function expansion limit is distinct from a whole-run resource limit.
The reference simulator additionally uses one `max_execution_steps` budget,
defaulting to 1,000,000, shared by all components and branches of the execution.
It charges a contract expansion before recursively executing that circuit.
Composing several individually admissible function proofs can therefore
exceed the simulator's run budget; such execution fails with a limit diagnostic.

Retaining a physical snapshot gives an inspectable implementation witness;
it does not mean every private auxiliary must be allocated by every simulator
after a proved cleanup substitution. Execution and cost reporting must state
which representation is executed, rather than reporting an optimized circuit
as the gate cost of the unmodified physical witness.

## 5. Conditional mathematical soundness

**FC-THEOREM — Whole-function equality.** Assume independent raw validity,
correct exact primitive interpretation, meaning-preserving ordered extraction,
and a successful exact comparison. Then the retained implementation and
specification satisfy `U=u` on their complete public interface.

Proof: extraction identifies each raw function with its ordered circuit.
The exact matrix leaf compares every input column and output row, including
phase. Equality of the matrices gives equality on every vector by linearity.
For an arbitrary external reference R, `U tensor I_R=u tensor I_R`, so the
same equality holds on correlated inputs and on density operators. The frame
and type/ownership premises are separate; matrix equality cannot authorize
dropping a holder.

**FC-STATIC — Preservation by known circuit transformations.** Let U=u be
the checked equality and let P transport the target axes into a surrounding
interface. Equality is preserved under

```text
P (U tensor I) P† = P (u tensor I) P†,
U† = u†,
U2 U1 = u2 u1   when U1=u1 and U2=u2,
U1 tensor U2 = u1 tensor u2,
U^n = u^n      for every finite n >= 0.
```

For a coherent control on an external disjoint axis, linearity and the
orthogonal control projectors give

```text
|0><0| tensor I + |1><1| tensor U
  = |0><0| tensor I + |1><1| tensor u.
```

The same argument applies to both specified `qif` branches and additional
controls. Scalar phases are retained even on a zero-dimensional axis list;
erasing `-I` would invalidate the controlled equation. Adjoints are available
here because both public function operators are unitary on the same exact
interface, and their known finite circuit descriptions are available. This
does not provide inverse or controlled access to an unknown external device.

Combining these identities with the action-placement and ownership rules
justifies reusing checked evidence without repeating a dense equivalence
test at every call. It is a conditional paper argument about the specified
rules. It does not formally verify the Rust exact arithmetic, extraction,
cache, source compiler, or simulator. An incomplete or resource-exhausted
checker rejects the proposed contract rather than weakening the equality.

## 6. Acceptance and rejection obligations

The minimum substitution demonstration fixes one public phase specification
and exchanges a direct implementation with an implementation using a private
computed auxiliary. Changing only the implementation selection must leave
the client's algorithmic structure and required specification unchanged.
The [runnable function-contract example](../examples/function_contracts/README.md)
uses the fixed one-bit phase operation Z, an entangled reference, and coherent
control. Its [unchanged-client regression](../tests/function_contracts.rs#unchanged_client_requires_one_specification_across_private_layouts)
checks the direct implementation and both computed-auxiliary forms.

An additional axis-sensitive check uses an asymmetric phase predicate,
for example `f(a,b)=a and not b`, and the public phase specification
`O_f|a,b>=(-1)^f(a,b)|a,b>`. With the first component on the low bit, its
matrix is `diag(1,-1,1,1)`. The
[independent raw-function regression](../tests/function_evidence.rs#legacy_computed_phase_is_checked_against_asymmetric_direct_oracle)
compares the direct operator with computed auxiliary use against that same
specification.

Use the same client under ordinary calls, coherent control, adjoint, finite
repetition, and with an entangled external reference. Inspect the final IR to
confirm retained evidence and its implementation snapshot. Compare independent
expected amplitudes or probabilities as appropriate; successful compilation
alone does not establish the intended phase-oracle behavior.

| Case | Required result |
| --- | --- |
| Equal direct and computed implementations, same exact public signature/specification | Accept after independently checking both actual function bodies. |
| Different private auxiliary widths with proved cleanup | Accept if the same public contract and finite checker limits hold. |
| Correct probabilities but a different global phase | Reject equality; control can reveal the difference. |
| Swapped output axes or changed asymmetric predicate | Reject unless the fixed public operator actually remains identical. |
| Changed implementation or specification dependency with old evidence | Reject mismatched binding or recheck the changed pair; never accept from names alone. |
| `iso`/`observe` target, classical port, multiple public quantum arguments, wrong source type tree | Reject target eligibility. |
| Duplicate ownership, old-token reuse, missing `Q<Unit>` result | Reject ordinary source/IR ownership independently of the contract equality. |
| Malformed action indices, overlapping controls, forged or cyclic evidence | Reject the malformed boundary; unchecked/cyclic evidence has no safe public constructor. |
| Inverse/control/repetition silently replacing an action without its evidence | Fail the retained-evidence requirement even if the resulting circuit is unitary. |
| Unsupported extraction, dimensions, steps, arithmetic, or checking work | Diagnose capacity/support failure without issuing evidence. |

The new path must retain the earlier certified-computed acceptance and
rejection cases: phase oracle, auxiliary H;H, simultaneous data/auxiliary X,
auxiliary-only X rejection, and exact cleanup with references. Existing
two-argument `with_computed` rules remain unchanged.

## 7. Scope and release status

This specification describes the implemented finite path for function-boundary
reuse and final transformed-IR evidence. It does not redefine v0.1 to mean
only the Rust matrix API, a mathematical example, or a source annotation.
V01-C1–C6 still require the implementation, independent checking, source/IR
binding, positive/negative examples, exchangeable implementations, and honest
publication of limits and proof status as one completed path.

Remaining general extensions include nonidentity source encodings and their
entry evidence, operation/size parameters, approximate logical contracts,
observation instruments, portable proof loading, and external backends.
Remaining general proof obligations include source/Rust adequacy and the
correctness of extraction and checking implementations. No new Lean theorem
or machine-checked whole-compiler proof follows from this supplement.
