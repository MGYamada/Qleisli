# Realization, specialization and resources

A **realization** is a claim that one emitted target artifact implements the
accepted meaning of a program under a named target profile. A realization
names a **closed specialization**: an instance of a definition in which every
choice that determines its meaning and interface is fixed. An
**engineering claim** is an approximation claim: a finite bound, in a named
metric, on the distance between an actual artifact and an exact ideal. It is
neither acceptance nor a guarantee. A **resource certificate** is a checked
quantitative bound on the resources of one emitted artifact.

This chapter specifies the boundary between the meaning of a program and a
claimed target implementation. It applies the adopted PR-2026-01 and
RS-2026-01 [interpretations](../design/initial-interpretations.md) under the
[authority hierarchy](authority.md).

The chapter fixes the request formats and the named profiles of the
[native engineering comparisons](#separate-engineering-approximation-claims).
Each of those profiles is closed and bounded, and it serves one comparison.
None is the target capability schema. The chapter defines no such schema, no
universal gate set and no synthesis algorithm, and it adds no source syntax.
The target capability schema is future work that consumes the abstract
obligations stated here.

[Status and limits](#status-and-limits) states the limits of the
implementation and of the proofs. This chapter does not discharge the
implementation and evidence obligations of the decisions that govern it.

## Semantic validity and a target realization

Semantic unitarity is a property of the exact denotation of a program.
Physical Realizability is a **forward correspondence obligation**. For an
accepted closed instance `p`, a checked realization of the actual output
artifact `C` under profile `T` must implement the accepted meaning of `p`,
subject to its explicit interface, encoding and workspace premises.

Rules:

- Semantic unitarity does not promise that the selected target can implement
  the operator, that synthesis can find an implementation, or that the logical
  wires of the source suffice.
- A failure of target synthesis must not reclassify a semantically unitary
  program as non-unitary.
- Inverse access and controlled access have their own contracts. Neither
  follows from finding one realization.
- A claim about a circuit that a search considered does not cover a different
  circuit that is emitted or executed afterwards.
- Synthesis and search produce candidates outside acceptance. An independently
  supplied candidate may qualify through the same checks. A complete synthesis
  algorithm for the entire semantic domain is not required.
- A failure to find a candidate is not evidence of impossibility. An
  impossibility claim requires an obstruction whose hypotheses match the
  target.
- Domain-wide existence or synthesis completeness is optional profile
  mathematics.

For example, Theorem 1 of Giles and Selinger establishes exact Clifford+T
synthesis with at most one clean ancilla for `2^n × 2^n` unitary matrices over
`Z[1/√2, i]`, under their specified gate and phase conventions. That result
grants no arbitrary dirty workspace, and it does not verify the output of a
particular compiler. See the
[original theorem](https://arxiv.org/html/1212.0506v3#S2).

## Observing instruments on a target

The [source instrument judgment](source-text.md#instruments-and-ordinary-feed-forward)
defines the complete outcome maps of an `Observe` expression. Realization
requires a separate judgment for the closed instance, the selected target
profile and the actual emitted artifact.

For each ordinary input `x` and declared outcome `c`, let `Φ[x,c]` be the
source map. Let `Ψ[x,c]` be the map of the emitted instrument after the
declared record projection. With the declared input and output encoding
channels `E_in` and `E_out`, the exact obligation is

```text
(Ψ[x,c] ⊗ id_R)((E_in ⊗ id_R)(ρ)) =
(E_out ⊗ id_R)((Φ[x,c] ⊗ id_R)(ρ)).
```

The equation holds for every finite external reference `R` and every joint
input `ρ` at the complete source interface.

Rules:

- The judgment fixes the ordered quantum and classical interfaces, the logical
  encodings and the projection of target records to source outcomes. It
  accounts for the initialization and the disposition of every additional
  physical owner.
- The projection assigns every target history to exactly one source outcome,
  including a history with records hidden from the source.
- The unnormalized maps fix both the outcome probabilities and the residual
  quantum state on the declared retained owners.
- The correspondence includes the consumed owners, the order of every owner
  that stays live and the action of every branch that contributes to a public
  outcome.
- The evidence states how the profile realizes each required measurement
  basis, where measurements can occur, which owners stay live, and how reset
  or repreparation obtains its stated output.
- For feed-forward, the evidence identifies the available classical outcome
  and the conditional operations. It also identifies any dynamic control,
  scheduling or latency assumption that the branch needs to execute with the
  specified live owners.
- Classical feed-forward selects a branch by a classical outcome. Coherent
  control acts on a live quantum selector and must preserve coherence between
  its sectors. Each needs its own realization evidence.
- Destructive readout accounts for the consumed owner. A retaining instrument
  requires the declared output owners and their conditional quantum state.
- A readout-and-prepare implementation qualifies only if the full
  correspondence equation holds.
- A terminal-readout-only profile may refuse a target claim that requires
  mid-circuit measurement and conditional quantum action.
- A profile that lacks a required target feature, or the evidence for it,
  fails target lowering. The source retains its instrument, type and effect.
- An engineering approximation requires the
  [explicit separate claim](#separate-engineering-approximation-claims).

For example, measuring both data qubits in Z and reporting their parity has
the same classical distribution as
[`std::measurement::parity_zz`](stdlib.md) on an even Bell state. The two
readouts lose the coherence between `00` and `11`, whereas the retaining
parity projector preserves it. Preparing computational-basis replacements
leaves that difference in the even outcome map.

This abstract obligation is an input to the future target capability schema.
QCP or another backend may express the premises in its own profile
vocabulary. Source semantics are defined independently of that vocabulary.

## Closed specialization

A generic definition describes a family. A closed specialization fixes every
choice that determines its meaning and interface:

- the resolved definition and the complete dependency and source identities;
- the ordered static arguments, including natural sizes and basis types;
- the selected providers, their types, their capability requirements and
  their Meaning bindings;
- all relevant static constraints and finite evaluation results;
- the declared constitutional edition and the applicable semantic profile.

For a target claim, the realization also fixes the target and profile, the
ordered layout and encoding, the workspace contract and any target-dependent
choices.

Rules:

- An unresolved parameter, capability requirement, constraint or budget
  expression must not be treated as a successful concrete certificate.
- A spelling, a bit width or a function name is not a specialization
  identity. The
  [exact type tree](type-model.md#structural-equality-coherence-and-physical-maps)
  is part of that identity, including Unit factors and zero-width owners.
- Generic checking must cover the admitted cases of the generic body under
  its declared premises. A favorable specialization must not excuse an invalid
  generic body or erase an obligation in an unselected branch.
- A well-typed family need not fit one fixed target at every parameter value.
- A family theorem may quantify over all admissible substitutions. Its
  statement must retain those premises. It must not describe one fixed finite
  circuit as implementing an unbounded family.
- Static totality, the computation of the resource bounds of an instance, and
  the feasibility of those bounds on a target are separate properties.

The [static language](static-language.md#definition-checking-and-closed-instances)
specifies static evaluation and the forming of closed instances.
[Diagnostics](#diagnostics) states when a failed export names the closed
specialization.

## Logical axes and physical placement

The logical interface records the ordered axes of each owner by the exact
[source type trees](type-model.md#structural-equality-coherence-and-physical-maps).
A physical layout assigns the live axes to target locations. For example, the
ordered pair of logical axes can occupy the physical locations `(17,4)`. The
first axis stays the first logical axis.

For a pure instance with semantic action `U` and actual target action `C`, a
correspondence with encodings `E_in` and `E_out` has the form
`C ∘ E_in = E_out ∘ U`.

Rules:

- Nested products and `Bits<n>` retain their declared axis order and owner
  order. A zero-width owner retains its interface identity and contributes no
  physical location.
- A target realization records the initial and the final placement, or their
  equivalent ordered encodings.
- The encodings include the specified workspace and its boundary state where
  required. The equation extends to arbitrary joint inputs with an untouched
  reference.
- An observing realization uses the
  [outcome maps](#observing-instruments-on-a-target). It records the placement
  and the disposition of the owners that are live at each interface, including
  any retired locations where the profile supports them.
- Routing may change the placement from `(17,4)` to `(4,17)` by an emitted
  physical SWAP, provided the evidence tracks each logical axis into its
  location after the SWAP. The SWAP contributes to the target cost.
- A metadata relabeling changes the description of the layout and leaves the
  physical state in place. The encoding evidence must justify that relabeling.
- A source-level axis permutation changes the logical action. It must be
  included in `U` with its specified order and phase.
- An emitted implementation of a logical SWAP must realize that action under
  its declared encodings.
- The placement evidence identifies each routing step. It accounts for the
  live locations that routing and synthesis workspace use.

The target model may expose this relation to QCP routing analysis. The future
target capability schema consumes this abstract correspondence. The
[bounded routing check](#quantitative-resource-claims) covers literal physical
SWAP intervals and their stated placement premises.

## Workspace and exact correspondence

Source `clean` and `dirty` workspace is part of the author's program contract
and owner accounting. Backend workspace is additional implementation storage
that realizes that meaning.

For a clean-workspace unitary instance, a representative equation is

```text
(C ⊗ I_E)(encode_in ⊗ I_E)(|0>_W ⊗ ψ)
  = (encode_out ⊗ I_E)(|0>_W ⊗ (U ⊗ I_E)ψ)
```

Here `ψ` belongs to `L_in ⊗ E`, and `U` maps `L_in` to `L_out`. The isometric
encodings map `W ⊗ L_in` and `W ⊗ L_out` to the respective physical
interfaces. The reference `E` stays last and is untouched. Each side therefore
uses the same explicit order of workspace, data and reference.

Rules:

- Backend storage must not become an implicit source owner or a permission to
  discard a source value. The realization claim must state its
  initialization, lifetime, restoration and physical cost.
- The equality is exact, including scalar phase. `W` starts and finishes in
  the specified pure zero state.
- A type width, an owner name or an example input does not prove this
  equation.
- For other encodings, or for differing input and output interfaces, the
  realization must state its corresponding typed equation explicitly.
- Dirty workspace requires the declared identity action on its unknown state
  and on all reference correlations. Returning its marginal state on a few
  inputs is insufficient.
- An observing implementation requires the complete unnormalized,
  outcome-indexed instrument correspondence, including the declared classical
  result assembly. A normalized selected branch or matching measurement
  probabilities must not replace it.
- Projective equality differs from exact operator equality. Dropping a global
  phase can change a coherently controlled operation. The exact contract does
  not quotient by that phase.
- A different equality relation must identify its boundary and its
  compositional obligations explicitly. The exact contract of this chapter has
  no approximate acceptance and no error budget.

The exact clean and dirty requirements come from the adopted QS
interpretation. [Exact target-domain membership](#exact-target-domain-membership)
and [Separate engineering approximation claims](#separate-engineering-approximation-claims)
state the rules of the exact and the approximate profiles.

## Controlled target realizations

The coherent Meaning of `controlled(U)` is the ordered direct sum `I ⊕ U`,
with inactive sector zero and active sector one. Semantic unitarity
establishes the operator property of `U`. The static `Controllable(U)`
judgment separately governs source use under the
[operation type rules](type-model.md#general-pure-operation-arrows).

Rules:

- Target lowering additionally requires a checked realization of the exact
  direct sum on the selected target.
- For a transparent implementation, a structural derivation must check each
  original gate or named implementation with its control, dependencies, axis
  order and exact phase.
- The implementation must act as the identity in the inactive sector and
  must implement the requested operation in the active sector.
- Composition and powers may compose those exact sector equations when the
  interfaces and the control match. Provider calls and the controlled powers
  that QPE uses carry the same obligations.
- A realization certificate binds the original operation and Meaning, the
  actual emitted implementation, the target profile, and the ordered control,
  data and workspace encodings. It identifies where native controlled gates
  are used and where additional synthesis steps are needed.
- Physical counts include workspace preparation, live width, restoration,
  generated inverse steps and routing when the implementation requires them.
- An opaque provider requires explicit controlled evidence bound to the
  requested operator and the emitted artifact.
- A scalar phase that multiplies only the active block changes its phase
  relative to the inactive block. Projective agreement or channel equality
  for the uncontrolled operation therefore must not supply the controlled
  equation.
- An engineering approximation to a controlled operator must bound its error
  against the intended controlled Meaning itself. It retains the exactness
  distinction of
  [Separate engineering approximation claims](#separate-engineering-approximation-claims).

## Isometries and initialized target interfaces

A semantic isometry `V: A -> B` satisfies `V† V = I_A`. The basis trees of `A`
and `B` can differ, including in width.

For a target that implements the isometry with a unitary dilation, let
`E_in: A -> P_in` and `E_out: B -> P_out` be the exact input and output
isometric encodings. Let `C: P_in -> P_out` be the action of the actual target
circuit. On every joint input `ψ` with external reference `R`, the realization
must establish

```text
(C ⊗ I_R)(E_in ⊗ I_R) ψ = (E_out ⊗ I_R)(V ⊗ I_R) ψ.
```

The mathematical adjoint reverses `V` on its image. On the full output space,
`V V†` is the projector onto that image. For an exact unitary dilation,
`C† E_out V = E_in`, including under an arbitrary external reference. An
available checked reverse circuit therefore recovers the encoded input on that
image.

Rules:

- A realization of `Op<A -> B>`, or of its refinement `Op<A -> B, M>`,
  retains both exact ports and the requested Meaning.
- Sequential composition matches the middle tree exactly. Tensor composition
  preserves the declared order of both ports.
- The input encoding specifies any initialized backend wires and their
  ordered placement.
- The output encoding identifies the retained logical output. It fixes the
  state of every backend wire that the claim returns clean. Other physical
  degrees of freedom require an explicit output contract.
- Isometry typing introduces no implicit discard and no partial trace.
- Source `clean` and `dirty` contracts bind source owners separately.
- A target claim accounts for every physical wire that the dilation uses,
  including initialized backend workspace. It also accounts for the
  preparation, realization, cleanup and routing that the selected target model
  requires.
- A dilation existence theorem supplies a candidate. The accepted artifact
  requires the displayed correspondence.
- An application outside the established image needs its own contract.
- The static `Adjointable` capability and the physical realization of a
  reverse operation require independent evidence under the
  [operation type rules](type-model.md#general-pure-operation-arrows).

## Exact target-domain membership

`M ∈ ExactDomain(P)` is an abstract judgment about the requested exact Meaning
`M` and a specified target profile `P`.

Rules:

- The evidence identifies the profile and its version, the literal gate
  vocabulary, the coefficient and parameter domain, the ordered interface and
  the phase convention. It also states the admitted initialization, encoding,
  workspace and restoration assumptions. Same-wire and clean-workspace
  profiles can therefore have different exact domains.
- Physical Realizability requires evidence of this premise for an accepted
  exact target realization.
- A checked exact witness for the profile may establish membership and bind
  the actual emitted artifact to the same Meaning.
- An existence theorem or a coefficient test may support this judgment within
  its own hypotheses. A necessary condition alone does not authorize a
  candidate.
- A search failure or a capacity refusal leaves the claim unproved.
- A target-domain refusal concerns the requested realization. The source
  retains its exact meaning and typing.
- A failed exact request does not select the engineering path implicitly. An
  engineering approximation requires an
  [explicit separate claim](#separate-engineering-approximation-claims) with
  the applicable metric, a closed budget and the correspondence to the actual
  artifact.
- This judgment is independent of any eventual QCP implementation. The future
  target capability schema may use it.

For example, take a profile whose gates and computational-basis coordinates
have coefficients in `Q(ζ8)`. Every entry of the gate product lies in that
field. Appending clean zero workspace and taking the corresponding returned
coordinate selects entries of the same product. A controlled phase of one
sixteenth of a turn has coefficient `ζ16` at its active diagonal entry, which
is outside `Q(ζ8)`. The obstruction applies for any number of such clean axes.

A target with a declared native sixteenth-turn gate requires its own
exact-domain evidence. The eighth-root execution profile reports an
unsupported exact phase for such a request.

## Separate engineering approximation claims

The adopted EXACT-2026-01 interpretation governs this boundary. An
epsilon-bound approximation is an engineering synthesis or export claim. It
lies outside the constitutional semantic truth conditions of edition 2026.

Rules:

- An engineering claim must not replace the exact source Meaning, semantic
  equality, or the obligations of phase and control, of owner and effect, and
  of clean and dirty restoration.
- An approximation bound grants no purity, no inverse access, no controlled
  access and no exact release.
- A checked engineering claim must identify the exact ideal, the actual
  artifact, the interface, the target and profile, the metric, the finite
  bound, the input and reference domain, and the composition assumptions.
- An instrument claim must retain the complete public outcomes and the
  residual outputs with arbitrary external references.
- Sampling, algorithmic resolution, synthesis and numerical-runtime
  information are distinct. An absent claim does not mean zero error.
- Engineering receipts, and their API and CLI claim kinds, must stay
  mechanically distinct from exact correspondence evidence and from resource
  evidence.
- Neither a small bound nor a reported `epsilon = 0` bypasses the independent
  exact gates or automatically discharges constitutional PR or target RS.
- An actual circuit may independently obtain ordinary acceptance for its own
  exact meaning. That acceptance does not identify its meaning with the source
  ideal.
- Reusing engineering evidence through a Meaning or an operation interface
  must not weaken the exact promise of that interface.
- Numerical, interval and approximate search methods may construct an exact
  artifact or proof. That result is eligible for the separate exact
  correspondence and resource checks. The spelling of a search parameter does
  not decide its claim kind.
- Exact cost accounting for an approximate artifact does not supply its
  missing exact correspondence to the source.
- Neither engineering validation nor this section creates an interpretation,
  a guarantee admission or a broader discharge of QS, PR or RS.

The bounded engineering profiles below implement these contracts within their
stated domains. They define no universal approximation metric. Each bounded
literal OpenQASM resource profile uses its own closed engineering budget.

### Common rules of the native comparisons

Five `qleisli engineering` commands check an engineering claim through the
**native checker**, the Lean checker executable. Each command takes one
positional file and these options:

| Option | Meaning |
| --- | --- |
| `--edition=2026` | Required. It selects the constitutional edition. |
| `--against=REQUEST` | Required. It names the UTF-8 JSON request. |
| `--lean-kernel=PATH` | Optional. It selects the native checker. Without it, the command uses the checker that `QLEISLI_KERNEL` names. |
| `--format=json` | Optional. The command writes the [result envelope](diagnostics.md#the-result-envelope) in place of text. |

Rules:

- Every `engineering` comparison requires `--edition=2026`. A command without
  it fails with the code `edition`.
- A command with neither `--lean-kernel` nor `QLEISLI_KERNEL` fails with the
  code `kernel`. A missing, incompatible or failed checker fails the
  comparison. No comparison falls back to another checker.
- A command line with a repeated option, an unlisted option or an extra
  positional argument fails with the code `usage` and exit status 2. Every
  other failure has exit status 1.
- Each request and each QIRF artifact must hold at least 1 byte and at most
  16 MiB (`limit`). The QLV3 envelope retains its 64 MiB limit.
- A request must hold exactly the fields of its format, with the fixed values
  of its profile. An unknown or missing field, an unknown version or another
  profile value is refused (`format`).
- Each comparison accepts execution scope only. It refuses inspection scope
  and caller scope.
- A report names the selected checker path. The checker identity is unpinned
  under the provenance limitation. A hash identifies the reported bytes. It
  establishes neither the correctness of the native binary nor human
  authority.
- Serialized CLI output is an inert report. It is never reusable native
  acceptance.

### Native pure engineering comparison

```text
qleisli engineering compare-pure ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]
```

`ACTUAL` is an original finite QIRF artifact. `REQUEST` holds the separate
original ideal artifact, both independently specified matrices and ordered
ports, the common complete domain and codomain type trees, and a closed
canonical nonnegative dyadic budget.

The request has exactly these fields:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-pure-request`, `1` |
| `claim_kind` | `engineering` |
| `metric` | `pure-euclidean-operator-norm-v1` |
| `checker_profile` | `frobenius-r8-pure-leaf-v1` |
| `target_profile` | `qirf-r8-pure-v1`, an IR profile rather than a hardware claim |
| `composition` | `single-component-v1` |
| `error_category` | `implementation-distance` |
| `domain`, `codomain` | Full QIRF Basis objects, for example `{"tag":"bit"}` |
| `actual`, `ideal` | Objects with exactly `input`, `output` and `matrix` |
| `epsilon` | `{"numerator":"7","denominator_bits":3}` means 7/8; use reduced signed decimal data, with zero encoded as `"0"` and exponent 0 |
| `expected_artifact` | Original UTF-8 ideal QIRF text, including its original byte spelling |

Rules:

- Ports and matrices use the native pure-leaf request encodings.
- The exact finite-matrix carrier is R8. The profile adds no arbitrary-angle
  syntax and no coefficient extension.
- A malformed or open budget, a false body matrix and insufficient arithmetic
  or work capacity are refused.
- Hidden observation, reset or discard must not acquire a pure label through
  this path, even when the requested budget is large.

The checker establishes:

- Each original artifact passes its ordinary check and then a fresh exact
  PureLeaf check against its own independent matrix request. Both complete
  type trees and the ordered ports are checked. The matrices are compared only
  after these checks.
- A sufficient squared Frobenius witness, over canonical rectangular R8
  matrices, meets the closed nonnegative dyadic budget. The witness is
  sufficient for the explicitly selected Euclidean operator norm.

The checker does not establish:

- A successful conservative witness is an inequality, not a completeness
  claim. A witness failure does not establish that no approximation or
  synthesis exists.
- Neither check changes the exact equality gate.
- The result does not establish source preservation, exact source
  correspondence, an instrument bound or a target-resource bound. The report
  states each of them as unestablished.
- The report has no conversion to `AcceptedProgram`, a Meaning, inverse or
  controlled access, cleanup evidence or resource evidence, including at
  epsilon 0.

Text and JSON identify the engineering metric, the bound, the profiles, the
composition, the digests of the original artifacts and of the request, and the
selected checker path. They report sampling, algorithmic resolution and
numerical-runtime errors separately as `not-claimed`. Those errors are not
silently zero.

> **Implementation note.** The Rust `interchange::engineering_pure` API
> constructs data-only requests. It returns a private, allocation-bound
> `EngineeringPureReport` after a fresh native check. Its serialized
> convenience entry independently decodes the same typed request. The native
> checker compares the typed context and both fresh graphs with the actual
> retained Rust execution description. A separate native engineering protocol
> binds both checks to the actual invocation and to both retained host graphs.
> The engineering response uses a distinct header and cannot enter an exact
> accepted-handle constructor.

### Native ordered pure tensor comparison

```text
qleisli engineering compare-pure-tensor ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]
```

This comparison combines exactly two ordered pure comparisons. It checks six
original QIRF artifacts afresh: the actual and ideal parents, the actual and
ideal left components, and the actual and ideal right components.

The request has exactly fourteen top-level fields:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-pure-tensor-request`, `1` |
| `claim_kind` | `engineering-pure-tensor-bound` |
| `metric` | `pure-euclidean-operator-norm-v1` |
| `checker_profile` | `tensor-additive-r8-pure-leaf-v1` |
| `target_profile` | `qirf-r8-pure-v1` |
| `composition` | `ordered-tensor-two-v1` |
| `error_category` | `implementation-distance` |
| `actual`, `ideal` | Parent leaf objects with exactly `input`, `output`, `matrix` |
| `left`, `right` | Component objects described below, in that order |
| `epsilon` | Canonical nonnegative dyadic, exactly the sum of the two component budgets |
| `expected_artifact` | Original UTF-8 ideal parent QIRF text |

Each component object has exactly `domain`, `codomain`, `actual`, `ideal`,
`epsilon`, `actual_artifact` and `expected_artifact`.

Rules:

- Types, leaf requests and budgets use the encodings of the pure comparison.
  Both artifact fields of a component hold the original UTF-8 QIRF text.
- Each body retains its own dependency order, exact matrix request, ordered
  ports and full type trees.
- Both parent interfaces must be the complete products of the component
  interfaces. `Unit` nodes are retained even when they occupy no physical
  wires. The checker derives the parent type trees from the ordered
  components. A width-only claim does not supply them.
- The exact parent equations use the low-first coordinates
  `left + left_dimension * right`. Both parent matrices must equal the ordered
  tensors of their respective component matrices.
- Missing or extra components, altered profiles, noncanonical or open
  budgets, a stale total budget, false body matrices, and arithmetic or work
  exhaustion are refused. A false parent tensor equation is refused
  (`contract`).
- The per-file, envelope, matrix and work limits of the pure comparison apply.

The checker establishes:

- The checker adds the two closed component bounds exactly and requires
  equality with the explicitly requested total bound.
- It does not repeat the sufficient whole-parent Frobenius inequality. An
  additive component certificate may succeed when that whole-matrix witness
  is too loose.
- All six body checks, the component inequalities, the parent equations and
  the bounded addition share one work counter.
- The checked additive operator bound extends to every finite external
  reference, including entangled inputs, under the freshly checked exact
  isometry premises.

The checker does not establish:

- The result supplies no exact equality between the parents, no source
  preservation, no inverse or controlled access, no cleanup, no
  emitted-target correspondence and no resource certificate, including at
  total epsilon zero.
- This comparison supplies only its stated additive bound for two components
  in one ordered tensor. It checks no recursive, sequential, controlled or
  instrument composition.
  [Support of the native comparisons](#support-of-the-native-comparisons)
  lists the composition that each comparison checks.

Text and JSON report this engineering bound and its composition profile. They
carry the same separate unclaimed error categories and the same preservation
and resource disclosures as the pure comparison.

> **Implementation note.** In the dedicated QLV3 invocation, the native
> checker compares its freshly decoded typed request and all six graphs with
> the retained Rust QDV1 view. The order is parent-actual, parent-ideal,
> left-actual, left-ideal, right-actual, right-ideal. The private Rust report
> binds the immutable artifacts, the original request and the selected checker
> path. A changed component, matrix, budget or parent cannot reuse it.

### Instrument engineering comparison

```text
qleisli engineering compare-instrument ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]
```

The instrument comparison uses a **complete adjoint Euclidean operator
bound**. For actual and ideal Kraus families, it bounds the difference between
their adjoint actions on every joint observable family `B`, for every finite
external reference `R` and classical input `x`:

```text
norm(sum_y,h (K_actual[x,y,h] tensor I_R)^dagger B[y]
             (K_actual[x,y,h] tensor I_R)
   - sum_y,k (K_ideal[x,y,k] tensor I_R)^dagger B[y]
             (K_ideal[x,y,k] tensor I_R)) <= epsilon * norm(B)_infinity
```

The norms on operators are explicitly Euclidean operator norms. The family
norm is the supremum over public outcomes. Hidden-history sets may differ. The
bound quantifies joint observables, including reference correlations, without
a reference-dimension factor and without branch renormalization. The metric is
not advertised as a diamond norm without a separate norm-duality proof.

The request has exactly fourteen fields:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-instrument-request`, `1` |
| `claim_kind` | `engineering-instrument-bound` |
| `metric` | `complete-adjoint-euclidean-operator-norm-v1` |
| `checker_profile` | `choi-l1-r8-instrument-v1` |
| `target_profile` | `qirf-r8-instrument-v1`, an IR profile, not hardware |
| `composition` | `single-component-v1` |
| `error_category` | `implementation-distance` |
| `actual_signature`, `expected_signature` | The complete requested signatures |
| `identity` | The original identity data |
| `epsilon` | Closed dyadic data, for example `{"numerator":"1","denominator_bits":2}` for `1/4` |
| `majorants` | The witness described below |
| `expected_artifact` | The original ideal QIRF text |

Rules:

- The witness assigns a canonical nonnegative closed dyadic `q` to every
  complex CP-coefficient difference. The order is fixed: public outcome,
  output row, input column, other output row, other input column.
- All actual and ideal public labels contribute. An absent label denotes
  zero. The witness length must be exact.
- Malformed dimensions or coefficients, noncanonical or negative budgets,
  insufficient witnesses, and arithmetic or work exhaustion are refused. An
  `epsilon` that the majorants exceed is refused (`contract`).
- No producer-supplied outcome labels, matrices, probabilities or success
  flags replace reconstruction.
- Old outer frames and cross-kind replies are refused.

The checker establishes:

- On both bodies, the checker reuses the ordinary root and dependency checks,
  the equality with the requested complete signature, the ordered result
  projection, the principal Observe checks and the complete Kraus and Gram
  reconstruction.
- Each coefficient is freshly reconstructed from all matching hidden
  histories. Exact R8 arithmetic checks its squared magnitude against `q*q`.
  Exact summation checks `sum(q) <= epsilon`. Both `q` and `epsilon` have
  unsquared norm units.
- The profile has one quantum input owner, empty classical inputs and the
  bounded dense reconstruction. The independent metric also defines general
  finite classical input families, for later composition work.

The checker does not establish:

- Pure phase agreement, source preservation, inverse or controlled access,
  cleanup, resources and constitutional PR or RS are unestablished, including
  at epsilon zero. No instrument bound grants exact release.
- Requested source and type trees are distinct from source-to-IR
  preservation.
- The profile is single-component. It issues no composed certificate, and it
  checks no resource limit. A comparison of emitted target bytes requires the
  [literal OpenQASM profile](#literal-openqasm-target-comparison).
- Sampling, algorithmic resolution and numerical runtime error are separate
  unclaimed categories. The pure comparison reports instrument bounds as
  unestablished.

Text and `--format=json` disclose the complete instrument bound, the digests
of the actual inputs and the unpinned checker identity. For example:

```sh
qleisli engineering compare-instrument actual.qirf --edition=2026 --against=comparison.json --lean-kernel=PATH
```

> **Implementation note.** The Rust request uses validated
> `InstrumentSignature` and `InstrumentResult` data. Its private
> `EngineeringInstrumentReport` retains both immutable artifacts, the original
> request and the selected checker path. The native QLV3 invocation compares
> both fresh graphs, the signatures, the identity and the complete budget and
> witness data with the Rust execution view. A preflight on the work that is
> left precedes the allocation of the Cartesian witness. The work counter
> bounds verification. It is separate from program resources and target
> resources.

### Literal OpenQASM target comparison

```text
qleisli engineering compare-openqasm3 TARGET --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]
```

`TARGET` holds the actual emitted bytes. The closed profile accepts this
literal ASCII structure, with zero to eight ordered gate lines between the
reset and the measurement, and a final newline:

```text
OPENQASM 3.0;
include "stdgates.inc";
qubit[1] q;
bit[1] c;
reset q;
h q[0];
c[0] = measure q[0];
```

The ordered gate word constructs the actual instrument. The instrument
consumes an explicit zero-width `Q<Unit>` owner, initializes one qubit, applies
the word, and then consumes that qubit with a terminal Z measurement.

`REQUEST` has the fourteen field names of the
[instrument request](#instrument-engineering-comparison) and the same
signature, identity and dyadic encodings. These fields have distinct fixed
values:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-openqasm-request`, `1` |
| `claim_kind` | `engineering-target-instrument-bound` |
| `metric` | `complete-adjoint-euclidean-operator-norm-v1` |
| `checker_profile` | `canonical-target-choi-l1-r8-v1` |
| `target_profile` | `openqasm3-canonical-one-qubit-terminal-r8-v1` |
| `composition` | `single-component-v1` |
| `error_category` | `implementation-distance` |

Rules:

- Each gate line must be exactly `h`, `x`, `y`, `z`, `s`, `sdg`, `t` or `tdg`,
  followed by ` q[0];`.
- The target must hold at most 1,024 bytes and eight gates (`limit`).
- Changed whitespace, headers, includes or operands, additional results,
  gates after the measurement and unsupported syntax are refused.
- The include line is a fixed token. Checking loads no external include file.
- The full interface is exactly `Unit -> Bit`, with a classical result and the
  principal Observe effect. Both complete signatures of the request must equal
  this interface. Equal widths do not admit `Bits<0>`, products of Unit or
  other result trees.
- `expected_artifact` retains the independently supplied original ideal QIRF,
  including all original dependencies. No fixed H ideal and no
  producer-supplied actual matrix substitutes for it.
- The standard gate interpretation is an explicit specification assumption.
  The adapter reuses the exact Raw and std meanings. It introduces no semantic
  primitive and no constitutional interpretation.
- An `epsilon` that the majorants exceed is refused (`contract`).
- A cross-kind checker is refused without fallback.

The checker establishes:

- The unchanged exact instrument gates reconstruct both complete Kraus
  families and Gram equations. The checker then checks the closed epsilon and
  every Choi coefficient majorant.
- The complete-adjoint bound covers every finite external reference and joint
  observable, without branch normalization.
- Kernel-checked matrices and the original-body bridge preserve the sign of H,
  the literal Y phase, the S/SDG direction and the T/TDG direction before the
  terminal observation.

The checker does not establish:

- This deliberately bounded profile is not a general OpenQASM parser, and it
  is no hardware-conformance claim. It adopts no external reference
  specification and proves no general OpenQASM execution semantics.
- This closed terminal experiment grants no open pure or controllable map.
- Source or export preservation, exact source correspondence, pure phase
  agreement, inverse or controlled access, exact cleanup and constitutional PR
  or RS are unestablished, even at epsilon zero.
- Sampling, algorithmic resolution and numerical runtime errors are
  separately unclaimed.
- Version 1 checks the instrument bound alone.

Text and JSON report the target-bound instrument inequality and the digests
of the actual inputs.

> **Implementation note.** The independent byte reader imports the Raw meaning
> data without acceptance definitions. The native mode is
> `--engineering-openqasm-check`. Its QLV3 body holds the literal target bytes.
> Its QDV1 comparison binds the typed request, the original byte array, the
> ordered word, the generated actual graph and the original ideal graph.
> Decoding is charged before traversal. It shares one work counter with the
> ideal reader, the exact instrument reconstruction and the metric check.

> **Implementation note.** The private `EngineeringOpenQasmReport` retains the
> immutable target, ideal and request bytes, the full contract and the checker
> path. Its actual graph is data, without a Rust accepted-program constructor.

### Literal OpenQASM engineering resource limits

Version 2 of the same request uses the claim kind
`engineering-target-instrument-resource-bound` and adds one required field:

```json
"resource_limits": {"model":"openqasm3-one-qubit-literal-gates-v1","gates":2,"t_gates":2}
```

`gates` bounds the emitted gate lines. `t_gates` bounds the subset `t` and
`tdg`.

Rules:

- Both limits must be closed integers from 0 through 8.
- The required literal header, reset and terminal readout fix one reserved
  qubit, one reset and one measurement.
- The model charges the literal one-qubit vocabulary. It excludes compiler
  work, synthesis search, hardware timing and cross-component composition.
- The metric, the epsilon and the single-component contract stay required.
- Changing the actual artifact, the original ideal or the request requires a
  fresh comparison.
- A timed-out or rejected check emits no certificate.

The checker establishes:

- The native checker checks the limits against the independently decoded word
  that the engineering instrument inequality uses.
- Text and JSON reports include the checked counts and limits, with the
  identities of the actual artifact, the original ideal and the request.

The checker does not establish:

- The engineering receipt supplies no exact cleanup, no phase-sensitive
  coherent control and no constitutional PR or RS.

> **Implementation note.** The typed execution view includes the model and the
> limits.

### Literal OpenQASM gate comparison with resource limits

```text
qleisli engineering compare-openqasm3-gate TARGET --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]
```

`TARGET` is a complete canonical OpenQASM 3.0 gate definition:

```text
OPENQASM 3.0;
include "stdgates.inc";
gate implementation a, b {
cx a, b;
}
```

For the general definition syntax, see the
[OpenQASM 3.0 specification](https://openqasm.com/versions/3.0/language/gates.html#hierarchical-gates-definitions).

Rules:

- The header and the include line must have the literal spellings shown. The
  fixed include selects the standard gate meanings of the profile.
- The declaration must be either `gate implementation a {` or
  `gate implementation a, b {`.
- A body instruction starts at the first column, uses one space after the
  mnemonic and after a comma, and ends with a semicolon and LF. The closing
  brace occupies its own line with an LF. The body may be empty.
- The admitted mnemonics are `h`, `x`, `y`, `z`, `s`, `sdg`, `t`, `tdg`, `cx`,
  `cz` and `swap`, with their exact ordered formal operands.
- The checker reads at most 1,024 bytes and eight gate lines (`limit`).
- The ports are `Bit` or the ordered pair `(Bit, Bit)`. Formal `a` is the low
  coordinate and formal `b` is the high coordinate.

The request fields common to both compositions are:

| Field | Value |
| --- | --- |
| `format`, `version` | `qleisli.engineering-openqasm-gate-request`, `1` |
| `claim_kind` | `engineering-target-operator-resource-bound` |
| `metric` | `pure-euclidean-operator-norm-v1` |
| `checker_profile` | `canonical-gate-frobenius-r8-v1` |
| `target_profile` | `openqasm3-canonical-ordered-gate-r8-v1` |
| `composition` | `ordered-sequential-two-v1` or `controlled-low-selector-v1` |
| `error_category` | `implementation-distance` |
| `epsilon` | Closed canonical nonnegative dyadic with `numerator` and `denominator_bits` |
| `resource_limits` | Object with model `openqasm3-ordered-gate-literal-gates-v1` and integer `gates` and `t_gates` ceilings from 0 through 8 |

An ideal description has exactly `expected_artifact` and `leaf`. The former
is the original UTF-8 QIRF text. The latter holds exactly `input`, `output`
and `matrix` in the finite pure-leaf format. The canonical dyadic and finite
coefficient encodings match `compare-pure`.

Each composition adds its own fields:

- `ordered-sequential-two-v1` additionally requires `split`, `first` and
  `second`. `split` is the number of literal instructions in the first slice.
  `first` and `second` each have exactly `ideal` and `epsilon`. The two
  comparisons use the same full port tree. The checked dyadic sum of the
  component budgets must equal the requested total. The same decoded slices
  constitute the whole word, in first-then-second order.
- `controlled-low-selector-v1` additionally requires `ideal` over one `Bit`.
  The desired action on `a, b` is the identity on selector zero and exactly
  the ideal operator on selector one. The checker compares the entire literal
  two-wire matrix with that controlled operator. Scalar phase in the active
  sector enters the metric as a relative phase.

The checker establishes:

- The checker verifies each original ideal independently against its exact
  port and matrix request.
- The native checker reconstructs the literal actions over the exact R8
  carrier. It uses the sufficient Frobenius comparison for the selected
  operator metric.
- For the sequential composition, the additive bound applies to the
  composition for every finite external reference. For the controlled
  composition, the norm bound extends to arbitrary finite external references.
- The checker checks the reported literal counts under the same request and
  the same work counter. The resource report counts formal wires, literal gate
  lines and the `t`/`tdg` subset.

The checker does not establish:

- The engineering result is scoped to the named approximation and the literal
  resource bounds. Hardware scheduling and compiler or search work use
  separate measures.
- Exact target correspondence, source capabilities and constitutional PR or
  RS require their own checks. This holds when a numerical search selected the
  circuit, and when the engineering epsilon is zero.

Changing any of the artifact, profile, metric, budget, split or ideal requires
a fresh check. Timeouts and refusals return an error.

> **Implementation note.** The execution view holds the original bytes, the
> decoded ordered instructions, the closed budgets and the fresh ideal graphs.

## Quantitative resource claims

A resource certificate states a checked bound for one emitted artifact. The
subsections below describe the bounded checks of the canonical terminal
OpenQASM profile.

Rules:

- A resource certificate must identify the actual closed instance, the
  emitted artifact, the target and profile, the resource measures, the
  schedule or interpretation of those measures, and the checked bounds.
- Changing providers, layout, target, workspace or output bytes invalidates
  reuse, unless a checked correspondence establishes the changed claim.
- A content hash establishes identity, not the bound.
- The
  [provider resource contract](functional-boundary.md#provider-selection-and-quantitative-resource-evidence)
  applies to each selected body and composition. An external, opaque or
  device-native implementation must meet the same admission requirements.
- Gate count, depth and non-Clifford cost require declared target
  conventions. Literal IR T-word counts are not automatically physical or
  optimal T counts.
- Compiler memory, checker work limits, static termination, ownership safety
  and target resource bounds are different claims. In particular, the
  ownership-only predicate does not discharge quantitative RS.
- An admitted symbolic family bound may strengthen RS within edition 2026. It
  needs the corresponding current proof and the actual compilation and
  resource binding.
- A family or construct may be admitted later with resource behavior outside
  current coverage. Its bound and its preservation obligations must be
  discharged before it is certified. Existing guarantees stay in force.
- A failure to meet a target budget rejects that target claim. It does not
  change the mathematical denotation of the program.

The QCP implementation and concrete target schemas have a separately
scheduled scope. This chapter is not their implementation.

### Physical live width

Rules:

- Physical live width includes logical data, explicit source workspace,
  backend synthesis workspace, and routing and target storage.
- A count takes each actual physical location once. It accounts for the
  lifetime of the location and its permitted reuse.
- Peak width is the maximum simultaneous live count. A sum of separate peaks
  is a conservative upper bound, not necessarily the realized peak.
- Logical width alone does not bound the physical implementation width.

### Routing segments

A **fixed-occupancy SWAP segment** records the ordered placement of all
occupied locations. The record includes any source, synthesis and routing
scratch that is live during the segment.

Rules:

- Each literal SWAP must name two distinct occupied locations that are
  connected in the declared profile.
- A SWAP moves both locations in the placement and leaves every other location
  alone. It counts as one operation even when a later SWAP cancels it.
- The final placement preserves the logical axis order and the exact joint
  coefficients with any reference.
- The check of a segment does not establish that the interval is used for
  routing, or that its entry placement is correct. A complete certificate
  establishes both. It also checks the other target operations, allocation,
  release and reuse.

> **Implementation note.** The native checker independently decodes the
> declared register width and the literal SWAP instructions from a designated
> byte interval of canonical OpenQASM output. It also checks the target
> capacity.

### The canonical terminal profile

The canonical terminal profile reserves all declared physical locations and
resets them before its first gate. It keeps the reservation through terminal
measurement.

Rules:

- The independent complete-artifact reader counts reserved and reset wires,
  gates, literal SWAPs, T/TDG and measurements from the output bytes.
- An exact finite workspace check may compare a designated gate interval with
  the independently checked original clean or dirty body. The comparison uses
  the declared ordered placement of data and scratch. The physical register
  must cover the checked Raw peak.
- The checker can derive the ordered locations of the workspace from the
  checked original Raw frame and its complete injective physical placement.
- A fresh scratch must occupy a location absent from that frame. For a fresh
  scratch wire, the checker can verify that nothing touches it between the
  initial reset and workspace entry, or after exact restoration.

### Placement replay

For a closed straight-line Raw prefix with zero preparations, structural owner
operations and finite gates, the checker derives the original frame by replay.
It replays the original prefix and the decoded target gate word.

Rules:

- Marked routing operations must match connected physical SWAPs in the
  emitted word. An ordinary Raw SWAP is matched as a gate and does not move
  the encoding.
- The derived original frame must equal the checked workspace entry,
  including zero-width ports.
- With one checked workspace interval and literal gates, the checker can
  carry the original exit owners through the target suffix. It uses the
  resulting placement to verify the emitted terminal measurements in classical
  output order.
- All original quantum owners must be consumed by the end. Discarded owners
  and measurements outside the classical outputs do not add to the emitted
  readout.
- The single-interval check requires an exclusive lifetime for fresh scratch.
- Outside a workspace interval, the checker can compare a single original
  circuit event against a decomposed target word. It derives the ordered
  support from the original operands and controls. It compares the complete
  exact operators on that support, up to six axes.
- Gates on other wires and phase changes are rejected. Matrix checking spends
  the same cumulative work as the surrounding replay.
- The replay can align a target word with several consecutive Raw circuit
  events and structural owner operations. It reads the actual owner
  transitions and checks the combined operator on the ordered support.
  Preparation, observation and source workspace boundaries require their own
  alignment.
- A structural basis lift updates the physical placement only when its
  complete table is an axis permutation. It contributes zero gates. A routing
  SWAP must occupy a literal gate position.
- For a `Q<Bits<n>>` data register, each original `take_bit` or `put_bit`
  index determines the ordered wire selection or insertion. The Raw
  repartition retains the other owners, including a distinct `Q<Bits<0>>`
  remainder. Repartition inside a workspace body is part of its independently
  evaluated exact operator.

### Synthesis scratch

A gate decomposition may use allocated synthesis scratch.

Rules:

- The physical locations of the scratch must be declared and separate from
  all live owners.
- The checker compares the full target word on the data and the scratch with
  the original operator, under the canonical zero embedding at both ends. The
  executable check keeps the same zero encoding at entry and exit.
- The six-axis bound includes scratch.
- A slice of several aligned events that uses synthesis scratch has the same
  zero-return check.
- A complete trace may reserve locations for several disjoint synthesis
  slices. Original allocation, routing, source workspace and readout must not
  touch these locations. Every slice that uses them checks its own zero
  return.
- An individual slice may instead use exclusive scratch. The checker verifies
  that the scratch is untouched everywhere else.

### Reuse of clean scratch

A physical scratch location may be reused across ordered, disjoint, clean
intervals.

Rules:

- The checker requires an exact zero-return equation for each interval. A
  zero-gate interval also checks that equation, and no gate touches the
  location in it.
- Every gate that touches the location must lie in one of those intervals.
  The location must be absent from terminal readout.
- The literal multi-interval check derives every entry placement from the
  preceding original owners and target word. It reserves each designated
  scratch location across the complete trace. It keeps the location out of
  ordinary preparations, routing and terminal readout.
- Each reuse interval must be bound to its own checked original workspace.
- The written logical operation and the workspace body use the same admitted
  workspace source fragment. An independently checked controlled phase may
  therefore appear in the declared logical operation and in the body. Their
  exact restoration equation checks the complete data and scratch action.

A successful native placement check has these properties:

- Each reusable clean wire is in the counted reset register.
- Every gate that touches that wire belongs to a checked restoration
  interval, with one operator step per decoded gate in the interval.
- A routing action before a workspace or in the terminal suffix points to a
  literal SWAP on an allowed edge at a counted gate index.
- The reported SWAP total includes the literal routing gates and any ordinary
  SWAP instructions in the target word.

> **Implementation note.** The typed-source adapter reads workspace intervals
> from the original checked root and named calls. It binds each local interval
> to the identical Raw operations at its position in the root. It checks the
> selected and returned ports against the full caller frame and retains all
> untouched spectator ports. The exporter preserves the interval boundaries
> across exact rewrites. It proposes the corresponding gate positions and
> scratch locations. The native checker checks the proposal against the
> original source, including the clean and dirty intervals and the terminal
> result order.

### The checked resource report

```sh
qleisli interop emit-qasm <source> --input=qli --resources
```

The command gives the checked resource report for a closed typed program. The
program has workspace scopes in its root or in a statically named call, or it
has a protected computed scope.

Rules:

- The JSON result contains the emitted text, the exact work spent in the
  placement check, the reserved qubits, the reset wires, the gates, the
  literal SWAPs, the T/TDG operations and the measurements.
- The counts come from the decoding of the returned text by the native
  checker.
- The placement check has one exact-work budget of 20,000,000. Exhausting it
  returns a limit rejection (`limit`) with no resource payload.
- The report covers the supported canonical terminal profile and its declared
  physical register.
- For `--resources`, the terminal emitter supplies the emitted register width
  as the capacity of the packet.

> **Implementation note.** The internal packet binds the complete original
> QLV3 request and the literal target bytes. The native checker rechecks the
> original source, decodes the target and replays placement under the one
> budget.

### Computed scopes

For a source-checked structural `with_computed` interval, the Raw resource
read counts the full live frame plus one private scratch wire at peak. It
counts one preparation, one clean release and both predicate passes. The
literal circuit count includes every forward step, inverse step and protected
use.

The terminal OpenQASM placement check can read this event in a closed original
source root. This includes a pure interval before or after an explicit
workspace.

Rules:

- The check places the ordered source wires, followed by a private predicate
  wire. It reconstructs the whole forward, protected-use and inverse word from
  the Raw operation.
- The decoded target word must agree on the complete support, including the
  predicate wire, with exact phase.
- If the target decomposition uses additional scratch, the same synthesis
  check requires the scratch to start at zero and return to zero.
- The predicate and synthesis wires are reserved from source allocation,
  routing and terminal readout.
- Counts include the resets of those wires, the physical compute and inverse
  gates, and any additional synthesis gates.
- This check uses the bounded terminal operator profile and its shared work
  budget.

For an admitted finite-table computed scope, the exporter uses the retained
table rows to emit controlled XOR flips of the private auxiliary bits. It
emits the protected operations on the ordered source, target and auxiliary
coordinates. It then repeats the XOR flips to restore the auxiliary bits.

Rules:

- For resource reporting, the source program must retain its original checked
  typed request.
- The native checker builds the original table permutation and the protected
  word from the checked Raw event of that request. It compares them to the
  complete decoded target interval.
- The same bounded operator profile covers these comparisons.

> **Implementation note.** The Raw interval reader charges owner checks and
> issuance-history checks separately from literal circuit validation. Its
> circuit charge covers the full forward and inverse fields and the operand
> checks in each forward step and protected use. Both charges consume the same
> shared work budget. The source-bound compute and inverse comparisons consume
> exactly `16 * (1 + sum(2 * control_count + 7))`, summing over the predicate
> clauses. This charge depends on the literal circuit fields.

> **Implementation note.** The original runtime plan retains the predicate and
> the auxiliary action that the native checker computes for the exact source
> occurrence. Both the structural path and the finite-table path use those
> source results and check the actual literal action independently.

## Phase words and target-dependent costs

In the eighth-root finite profile, let `ω = exp(2πi/8)`. The one-axis phase
with residue `r` is exactly `diag(1,ω^r)` on the declared axis. This includes
an action on an input that is entangled with a reference.

Rules:

- A supported source `phase[j,d]` has `r = 8j / 2^d` when this quotient is an
  integer. The [primitive contract](primitive-boundary.md) specifies the
  source and profile limits.
- Adjoint changes the exponent to `-r` modulo eight. Repetition adds the
  residue on each action.
- A scalar `ω^r I` differs from a one-axis phase. It can become a relative
  phase under coherent control.
- The finite format represents the one-axis phase by a monomial with the
  chosen axis, the identity permutation `[0,1]` and the phase exponents
  `[0,r]`. The action of the historical word of `r` T gates is the same
  diagonal.
- A decoder must keep decoding the gate and circuit constructors in their
  versioned profiles. The equivalent monomial representation requires no
  dedicated Phase constructor and no change to the established encoding of a
  T word.

For the canonical terminal OpenQASM vocabulary, the selected one-axis words
and their literal `t` or `tdg` counts are

| Residue | Emitted word | Literal T/TDG |
| --- | --- | ---: |
| 0 | empty | 0 |
| 1 | T | 1 |
| 2 | S | 0 |
| 3 | S, T | 1 |
| 4 | Z | 0 |
| 5 | S†, T† | 1 |
| 6 | S† | 0 |
| 7 | T† | 1 |

Rules:

- These counts apply to the specified one-axis words. A coherent branch or
  control requires the complete ordered action on each sector with its
  original phase. For example, the terminal export uses two T instructions,
  one T† and two CX instructions for controlled S.
- A negative control can introduce additional X gates.
- A conjunction-based lowering includes its live scratch, preparation,
  computation and full reverse chain.
- A model that decomposes CCX must include that decomposition. In the
  canonical terminal profile, CCX is a single literal gate. It is outside the
  `t_gates` counter, which counts exactly the emitted T and T† instructions.
- Literal source-IR word counts, optimized target instruction counts and
  resource bounds are separate claims.
- A certificate binds the actual emitted word and the checked decomposition
  to its profile. It includes the required workspace and routing.
- An exponent, an operation name or a normalized phase word supplies no bound
  for a different target and no optimal cost claim.

## Small obstruction examples

Embedding a `k`-qubit gate `G` into `n` wires, under a fixed ordered basis,
gives determinant `det(G)^(2^(n-k))`. Determinants multiply under composition.
Consequently a target generator set restricts same-wire determinants.

Rules:

- This restriction is a necessary condition. Sufficiency requires a separate
  theorem for that precise generator, phase and workspace profile.
- For a basis-permutation vocabulary, signs multiply under composition. An
  even-only vocabulary therefore excludes odd permutations on the same wires.
- Precomputed generator determinant classes, or the parity of an available
  permutation table, may reject a candidate before synthesis.
- The obstructions use the stated generator vocabulary, controls and
  workspace premises.

The repository retains two exact small examples:

| Operator | Semantic property | Same-wire obstruction for the stated profile |
| --- | --- | --- |
| Positive-exponent three-qubit Fourier operator `F8` | Unitary, with `det(F8) = i` | The embedded H/T/X and NCT generators considered by the regression have determinants only `±1` on three wires. |
| Four-bit `c3x` basis permutation | A bijection with one transposition, hence determinant `−1` | Those embedded generators have determinant `+1` on four wires. |

Both programs are semantically accepted. The regression
`tests/static_semantics.rs::review_same_wire_obstructions_do_not_reject_semantic_unitaries`
checks the original four-bit table, the complete exact F8 operator and the
embedded-generator determinant calculation. The original source is retained at
`tests/fixtures/review_v023/c3x.qli`. The regression reads the corresponding
current fixture at
`tests/fixtures/frontend_v030/coherent-basis/current/ordinary-type-cutover/current/review_v023/c3x.qli`.

<a id="current-production-status-and-diagnostics"></a>

## Diagnostics

A diagnostic for a failed realization claim or resource claim reports a
restriction on the realization. [Diagnostics and recovery](diagnostics.md)
gives the codes and the fields.

Rules:

- The diagnostic must identify the closed instance, the requested profile and
  the failed premise.
- It must distinguish a proved obstruction from unsupported synthesis and from
  exhausted checking capacity.
- An unsupported target operation or a target-width error must not be
  presented as a failure of semantic unitarity.
- The terminal exporter reports an unsupported operation (`unsupported`) and
  the capacity limit of the synthesis workspace (`limit`). It reports its own
  target refusal after source checking has completed.
- For a source project export, a failure at a Raw operation emitted inside a
  closed generic body identifies the specialization and points to the original
  expression.
- Terminal export can identify the closed specialization and the original
  source expression when a rejected operation has a single retained origin.
  This includes steps from an explicit clean or dirty workspace body.
- When a rewrite combines several expressions, the enclosing Raw operation can
  provide its own origin.
- For a failed native workspace equation, the checker supplies the original
  Raw interval, and the host checks it against the retained workspace. The
  diagnostic can name the enclosing specialization, or a single specialization
  shared by all steps in the checked body.
- Packet-wide errors and ambiguous bodies leave the specialization
  unspecified.
- Imported artifacts have no original project diagnostics.
- A location supplies no realization and no resource certificate.

## Status and limits

The [production inventory](production-boundary.md) identifies the actual
native acceptance, proposal, execution and export routes. Ordinary native
acceptance does not itself issue a target realization or a resource
certificate. An engineering result is not acceptance and not a guarantee.

### Limits

| Limit | Value |
| --- | --- |
| A request or a QIRF artifact of a native comparison | 16 MiB |
| The QLV3 envelope | 64 MiB |
| The literal target of either OpenQASM comparison | 1,024 bytes and 8 gate lines |
| `gates` and `t_gates` of a `resource_limits` object | 0 through 8 |
| Exact operator comparison of the placement replay | 6 axes, including synthesis scratch |
| Exact-work budget of the placement check behind `--resources` | 20,000,000 |
| Contract expansion of the terminal exporter | 1,000,000 steps |
| Allocated qubits of the terminal exporter | 12 |

Contract expansion shares the 1,000,000-step function limit across the whole
export. That limit is a producer work limit, not a target-resource bound. Flat
steps keep the flat input limit and the emitted-gate limit of the exporter.

### Support of the native comparisons

| Command | Compared | `composition` | Resource limits |
| --- | --- | --- | --- |
| `compare-pure` | Two original pure QIRF artifacts | `single-component-v1` | None |
| `compare-pure-tensor` | Two parents and their two ordered components | `ordered-tensor-two-v1` | None |
| `compare-instrument` | Two original instrument QIRF artifacts | `single-component-v1` | None |
| `compare-openqasm3` | Literal one-qubit terminal OpenQASM bytes and an original ideal instrument | `single-component-v1` | Version 2 only: model `openqasm3-one-qubit-literal-gates-v1` |
| `compare-openqasm3-gate` | A literal OpenQASM gate definition and original ideal pure artifacts | `ordered-sequential-two-v1` or `controlled-low-selector-v1` | Required: model `openqasm3-ordered-gate-literal-gates-v1` |

Unsupported:

- No native comparison checks a recursive composition.
- No native comparison checks a composed instrument. Both instrument profiles
  are single-component.
- Sequential and controlled composition are checked only for a literal
  OpenQASM gate definition of at most two formal wires and eight gate lines.
- The two resource models above are the only target-resource checks of an
  engineering claim. Each bounds the literal gate lines and the `t`/`tdg`
  subset of one bounded target. Neither discharges the constitutional
  quantitative RS obligation, which is pending.
- The source compiler consumes no engineering claim. The language has no
  source epsilon annotation.
- A request for another composition or another profile value is refused
  (`format`).

### The terminal exporter

- The terminal exporter in `src/interop/export.rs` performs bounded untrusted
  rewrites after program verification.
- The exporter explicitly allocates and uncomputes conjunction scratch. It
  rejects output that exceeds its physical qubit capacity (`limit`).
- For an accepted single-bit certified compute with an all-zero predicate,
  the exporter emits the physical body with the data axes followed by a
  separately reserved clean scratch wire. It reuses that wire after a complete
  verified zero return.
- The terminal OpenQASM exporter can consume the original accepted handle of
  a closed typed source program. It emits a wire-level projection of a Unit
  result, or of a positive-width product of measured bits, in the verified SSA
  output order.
- Nominal results, zero-width components of products and source parameters
  are outside this projection (`unsupported`). Typed QIRF transport is a
  separate obligation.
- A nontrivial uncontrolled scalar has no realization in this gate vocabulary
  (`unsupported`).
- External schema entries stay disabled until their binding gates are
  completed.
- The OpenQASM 3 and QIR adapters are experimental test features. They are
  not suitable for real quantum hardware.

> **Implementation note.** A borrowed cursor expands the actual retained
> function circuits, including nested controls, adjoints and ordered axis
> maps. The exporter then merges adjacent diagonal actions.

### Code, tests, proof, preservation and specification review

Code:

- The native comparisons, the placement replay and the resource report are
  bounded implementation checks. Each covers the profile that its section
  states.
- General specialization certificates and general diagnostic coverage are
  open work.

Tests:

- The regression named in
  [Small obstruction examples](#small-obstruction-examples) covers the two
  obstruction examples.
- A Rust and Lean regression binds the same emitted OpenQASM bytes to two
  original clean intervals. It checks their placement, exact restoration and
  readout.
- The independent `scripts/test_review_v024.py` oracle checks emitted small
  QFT and control circuits, including complex phase, output axes and
  zero-return scratch. Such bounded numerical validation is distinct from a
  general transformation proof and from a resource certificate.

Proof, for the QPTL library:

- `controlled_mul` proves the operator identity that composes the exact
  sector equations of a controlled composition.
- `controlled_pow` proves the corresponding operator identity for powers.
- `controlled_phase_ne` proves that a scalar phase on the active block alone
  changes the controlled operator. It holds for any nontrivial scalar on a
  nonzero operator.
- `dilation_recover_reference` derives the image-restricted recovery equation
  of an isometry from the exact forward square and the unitary implementation
  law.
- `extracted_sixteenth_ne` proves the coefficient obstruction of
  [Exact target-domain membership](#exact-target-domain-membership).
- `QPTL.FiniteMatrix.det_embedded` proves the determinant formula of an
  embedded gate, for finite matrix bases and simultaneous reindexing of both
  interfaces.
- `QPTL.FiniteMatrix.exact_same_wire_obstruction` covers a product of
  generators whose determinants lie in a multiplication-closed set that
  contains one. Such a product cannot equal a requested matrix with
  determinant outside that set. The premises retain the chosen target
  vocabulary, layout and exact phase.

Proof, for source workspace on the finite one-scratch checker:

- `WorkspaceTargetAction.clean_checked_separates` uses the exact checked
  insertion and output coefficients with the fixed-scratch law of QPTL. The
  joint output density has support only in the zero-scratch block, for every
  input density on data and a reference.
- `WorkspaceTargetAction.dirty_checked_promotion` binds every coefficient of
  the actual body to the logical operator promoted on the ordered data axes.
- `WorkspaceTargetAction.dirty_checked_reference` applies that action to each
  joint reference column. It proves that every selected input coordinate
  retains the scratch bit of the output.
- `Qleisli.WorkspaceTargetAction.decoded_action` connects the exact action of
  a decoded workspace slice to the literal Raw body on its full ordered data
  and scratch interface. The equality preserves the original phase for
  arbitrary reference columns.
- `native_clean_access_counted_once` covers each reserved clean wire. It
  links native placement success to the literal reset of the wire and to one
  unique restoration interval for every emitted gate that touches it. It also
  places the interval inside the counted target gates and excludes the scratch
  wire from terminal readout.

Proof, for synthesis scratch:

- `WorkspaceTargetAction.synthesis_action` connects the actual decoded gate
  word to the original local operator under the canonical zero encoding. It
  proves equality with full phase on every external reference column, with
  zero amplitude whenever any synthesis scratch bit is nonzero. The checked
  placement replay recovers this evidence at the original Raw position and
  physical gate offset, for a single circuit event or an optimized span.
- `WorkspaceTargetAction.bound_synthesis_action` connects the replay before a
  source workspace to that exact action.
- `WorkspaceTargetAction.native_suffix_synthesis_action` connects the
  terminal suffix of the native decision to that exact action.
- In both theorems, the equation uses the original circuit steps on the
  recovered support with their dependencies. Reindexing the checked local
  steps by the ordered layout of data and synthesis scratch recovers the same
  emitted instruction slice. The decoder establishes the arity and the
  distinct, in-range operands of each instruction.
- The full physical register action on a fixed spectator slice therefore
  agrees with the checked local word, for arbitrary input amplitudes and
  external references. The literal gate interval and its synthesis scratch
  locations are within the reported gate and register counts.

Proof, for the resource report:

- A Lean theorem proves that the decoded register width bounds the maximum
  Raw live width over the workspace occurrences that the replay visits. The
  bound includes caller spectators and temporary clean wires.
- The native reply theorem binds the reported counts to the exact target
  bytes. It proves that the reserved width is within the requested target
  capacity.
- `Qleisli.TerminalPlacement.native_terminal_correspondence` relates the same
  successful native decision to the selected original Raw root. Immediately
  before terminal measurement, after all decoded gates have run from reset,
  the entire physical complex column agrees with the corresponding pure Raw
  prefix under its ordered placement, including phase and restored scratch.
- By the same theorem, the final measurement distribution agrees for every
  public result word after summing the original hidden outcomes. The theorem
  also binds the resource counts of the reply and its workspace peak bound to
  that same checked packet.

Proof, for computed scopes:

- `Qleisli.RuntimeComputedResources.structural_counts` binds the counts of a
  structural `with_computed` interval to the same original source-checked Raw
  occurrence. It retains caller spectators in the peak width.
- `QleisliKernel.Qirf.StructuralComputedRaw.read_work` proves the debit of
  the executable Raw interval reader.
- `QleisliKernel.Qirf.StructuralComputedUse.read_circuit_work` identifies the
  work state after the source-bound compute and inverse comparisons and before
  the check of the emitted auxiliary action.
- The same literal XOR factorization proves the logical action for the
  independently checked Raw event, even for an arbitrary caller amplitude
  function. The source-bound theorem additionally identifies the predicate and
  the phase from the original body. The complete pure Raw event fold uses the
  local logical action without constructing a global matrix.
- `BoundSegment.structural_paid` and `FinishedTrace.suffix_structural_paid`
  each recover the checked placement and the gate interval from the executable
  replay.
- `StructuralPlacement.literal_costs` binds that interval, and the distinct
  data and scratch locations, to the decoded gate and reset counts.
- `ProtectedTablePlacement.literal_costs` ties the decoded interval of a
  finite-table computed scope, and its distinct physical locations, to the
  reported gate and reset counts.

Proof, for engineering claims:

- The proof of the pure comparison bounds the explicitly selected Euclidean
  operator norm, including arbitrary finite external references and literal
  scalar phase.
- Pure composition proofs establish additive sequential and ordered tensor
  error rules for the same Euclidean metric, under the stated exact isometry
  premises, including arbitrary references.
- The coherent-control corollary additionally requires equal domain and
  codomain and the independent access meanings.
- These mathematical rules do not change the single-component profile, and
  they supply no compiler or lowering preservation.
- Independent mathematical composition of instruments uses the actual Kraus
  families. Full Gram completeness implies adjoint contraction at every finite
  reference.
- A literal pure operator gap `delta` and both pure Gram equations imply the
  one-way instrument bound `2*delta`. No phase information is recovered.
- Feed-forward composition retains the public `(y,z)` outcomes and the hidden
  `(h,k)` histories. Ordered tensor composition retains the declared left and
  right input, output, public and hidden products through explicit proved
  reference regrouping.
- Both constructions have additive `epsilon_1 + epsilon_2` bounds under their
  stated component bounds and Gram premises.
- Separate completeness theorems require both original Gram equations. A
  bound alone does not establish them.
- These results provide no compiler consumption and no composition-preservation
  proof for original source or QIRF.

Preservation:

- An engineering result does not establish source preservation or target
  preservation. A location in a diagnostic supplies no certificate.
- The two admitted QLV1 guarantees cover original-root ownership and
  classical scope. They do not certify source lowering, target emission or
  quantitative bounds.
- QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 are pending, as the
  [initial guarantees](../design/initial-guarantees.md) record. No statement
  of this chapter discharges one of them, and this chapter admits no
  guarantee.

Specification review:

- The standard gate interpretation of the literal OpenQASM profiles is an
  explicit specification assumption. This chapter records no specification
  review of its rules.

## History

- This chapter was written as the 0.3.0 boundary between the meaning of a
  program and a claimed target implementation. Its governing decisions are
  [#120](https://github.com/MGYamada/Qleisli/issues/120),
  [#121](https://github.com/MGYamada/Qleisli/issues/121),
  [#127](https://github.com/MGYamada/Qleisli/issues/127),
  [#280](https://github.com/MGYamada/Qleisli/issues/280) and
  [#281](https://github.com/MGYamada/Qleisli/issues/281). #280, which reserves
  the Resource Safety theorem inside edition 2026, is open.
- [#124](https://github.com/MGYamada/Qleisli/issues/124) separated instrument
  semantics from target measurement and feed-forward realizability.
  [#126](https://github.com/MGYamada/Qleisli/issues/126) defined the
  correspondence between logical axes and the physical layout.
- The future
  [target capability schema](https://github.com/MGYamada/Qleisli/issues/179)
  is open work of 0.4.0. QCP and concrete target schemas are scheduled in
  [#103](https://github.com/MGYamada/Qleisli/issues/103), which is also open.
- [#28](https://github.com/MGYamada/Qleisli/issues/28),
  [#44](https://github.com/MGYamada/Qleisli/issues/44) and
  [#47](https://github.com/MGYamada/Qleisli/issues/47) tracked the static
  language and the specialization implementation. All three are closed.
- The exact clean and dirty requirements come from
  [#70](https://github.com/MGYamada/Qleisli/issues/70),
  [#156](https://github.com/MGYamada/Qleisli/issues/156) and
  [#157](https://github.com/MGYamada/Qleisli/issues/157).
- [#31](https://github.com/MGYamada/Qleisli/issues/31) fixed the boundary
  between exact and approximate semantics.
  [#123](https://github.com/MGYamada/Qleisli/issues/123) defined exact
  target-domain membership. Both are closed.
- The human-adopted EXACT-2026-01 interpretation is recorded in
  [#311](https://github.com/MGYamada/Qleisli/issues/311).
- [#163](https://github.com/MGYamada/Qleisli/issues/163) required closed
  approximation budgets before target resource certification. It is closed.
  The changelog records the native comparisons and the resource limits of the
  literal OpenQASM comparison under 0.3.0-beta. It records the literal
  OpenQASM gate comparison after that release, under #163.
- [#165](https://github.com/MGYamada/Qleisli/issues/165) defined the exact
  phase words and the target-dependent non-Clifford costs. It is closed.
- General specialization certificates and diagnostic coverage are part of the
  Language Reference work in
  [#48](https://github.com/MGYamada/Qleisli/issues/48), which is open. #120
  and #127 are closed.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
