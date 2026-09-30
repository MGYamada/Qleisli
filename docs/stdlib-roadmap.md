# Standard-library direction

## Adopted library goal

The adopted goal is a BLAS/LAPACK-like quantum-computing foundation combining
reusable components, a quantum-information textbook and formal specifications.
Readers should be able to learn quantum information by reading the library:
concept/motivation → mathematical meaning and premises → readable `.qli` source
→ examples/counterexamples → checking and proof status.

Until v0.5.0, generally add algorithms to corpus. From v0.5, grow stdlib as a
mathlib-style open-source project under [STDLIB.md](../STDLIB.md). Its [template](stdlib-contract-template.md)
and [public ledger](stdlib-contracts.md) fix contribution/contract responsibilities.
The comprehensive module hierarchy and generalized APIs remain open; current
[modules and sealed primitives](standard-library.md) keep their contracts.
`qlippy` remains a future tool, and general borrowing a separate language decision.

Readable and optimized implementations may share a phase/encoding-fixed contract
only through independently checked correspondence. Review mathematical intent
separately from implementation conformance. Report ownership, effects, entry
premises, access, complete instruments, exact scratch return, approximation and
resources explicitly; tests, source preservation and actual-IR proofs are separate.

## 2. Seven library areas

These areas classify concepts; the names below are not a decision to add those
names to `std::`. Start with ordinary `.qli` definitions and identify any parts
requiring language forms for static operation transformations. New primitives
require their own semantics and IR checks.

| Area | Candidate standard vocabulary | Classification, dependencies, and contract focus |
| --- | --- | --- |
| Quantum primitives | Preparation, unitary operations, measurement, reset, discard | Build on sealed operations in `std::quantum` and `std::observe`; derived preparation and measurements are ordinary definitions. Do not introduce a `unitary` primitive executing arbitrary matrices. |
| Structural combinators | Control, inverse, repeat, tensor, compose, compute/uncompute | Inverse and control correspond to `adjoint` and `qif`; their finite forms already exist, while generalization remains proposed. Consider static transformations through language forms first, with composition expressed by ordinary definitions. Check phase, effects, complete resource transfer, finite expansion, and zero return. |
| Quantum data structures | Qubit, QReg n, quantum integers, indices, ancilla | Start from `Q<Bit>` and finite products. Sized types are language-form candidates; integer operations are ordinary-definition candidates. Specify width, signedness, bit order and valid subspaces; distinguish classical indices from quantum ownership. |
| Arithmetic | Reversible addition/multiplication, modular arithmetic, comparison | Ordinary definitions. State total basis functions and reversible extensions, overflow, modulus, and work regions. Define the action on the entire register space, including values outside valid residues modulo N. |
| Transforms | Hadamard transforms, QFT, basis changes, block encoding | Transform circuits are ordinary definitions. Block encoding needs an additional contract between the full unitary and a projected block. Preserve phase, axis order, approximation error, and normalization. |
| Algorithmic skeletons | Phase estimation, amplitude amplification, quantum walk, LCU, QSVT | Candidates for families of ordinary definitions. The static operation-parameter mechanism is undecided. Make input models, success conditions, iteration, precision, and costs public contracts. |
| Hybrid patterns | Measurement and feed-forward, variational iteration, syndrome extraction | One quantum trial is an ordinary `observe` definition. Trials, statistics, and optimization require separate host-side planning; host APIs are not `.qli` standard functions. |

`Qubit` and `QReg n` do not turn quantum states into copyable values. Ancillas
also remain linear resources; neither a name nor a lifetime proves zero
return. Separately owned registers may be entangled.

## 4. First algorithm skeleton contracts

The following is **design metanotation**. `U_A` describes a phase-fixed unitary
on `H(A)`, `Prep_A` is a repeatable fresh-preparation procedure, and `CBits[m]`
is a classical result sequence. These are not current first-class source types.
Distinguish operation descriptions that capture no quantum resources from
`Q<A>` owners consumed linearly at runtime. Arbitrary free-vector-space `bind`
is not adopted; strict monad laws for Kleisli-style composition remain a
separate proof question.

<a id="41-amplify-準備と判定から増幅を構成する"></a>

### 4.1 amplify: amplification from preparation and a predicate

```text
amplify(P: U_A, good: A -> Bit, k: StaticNat) : () -[Iso]-> Q<A>
```

**Proposed classification:** a family of ordinary `.qli` definitions, dependent
on static operation parameters. `good` is a total basis function. A specified
`|0_A⟩` and preparation unitary `P` produce `|ψ⟩=P|0_A⟩`.

```text
Π_good = Σ_{x:good(x)=1} |x⟩⟨x|
O_good = I - 2Π_good
R_ψ = P (2|0_A⟩⟨0_A| - I) P†
G = R_ψ O_good
output = G^k |ψ⟩
```

The result is fresh data ownership with effect `Iso`; internal `G` has effect
`Unitary`. Measurement and selecting a successful result form a separate
`Observe` procedure. Close auxiliary regions only after checked zero return,
or explicitly include their ownership in the output.

For initial success probability `a=⟨ψ|Π_good|ψ⟩=sin²θ`, the ideal success
probability is `sin²((2k+1)θ)`. An unknown `a` does not automatically supply an
optimal `k`; strategies for unknown probability and fixed-point variants need
separate contracts. [Primary amplitude-amplification reference](https://arxiv.org/abs/quant-ph/0005055).

- **Candidate acceptance:** two-bit uniform preparation, one marked item,
  `k=1`; `k=0` means preparation only, and an empty good set has success zero.
- **Candidate rejection:** inverting a `P` that measures, constructing a
  reflection from an owned unknown state alone, or identifying an unchecked
  phase oracle with `good`.
- **IR direction:** expand preparation and the checkable phase oracle, `P†`,
  zero-state reflection, and `P` into a finite static sequence and reverify.
  Retain the operator's global phase.

This contract needs a preparation procedure and an iteration policy.
`Oracle A -> Predicate A -> Q<A>` alone omits both and the source of ownership.

<a id="42-phase_estimate-位相に関するインストルメント"></a>

### 4.2 phase_estimate: an instrument for phase information

```text
phase_estimate(U: ControlledAccess<U_A>, m: StaticNatPositive;
               q: Q<A>) -[Observe]-> (CBits[m], Q<A>)
```

**Proposed classification:** a family of ordinary `.qli` definitions.
`ControlledAccess` is candidate wrapper notation for checked access evidence
for phase-fixed controlled powers. The [selected semantic model](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/decisions/2026-09-27-v1-path.md#static-operations-and-capability-representation)
uses constraints on static operation descriptions; the wrapper, `requires`
predicates and evidence builders are distinct surface roles, not three
competing notions of control. The [M1 grammar](next-minor-spec.md) now selects
static parameters and access constraints; sized QPE syntax remains future work. Possession of an
unknown black-box `U` alone is not evidence of controlled access.

Consume `q` and return the postmeasurement target. Measure and consume only
the freshly prepared phase register; a variant disposing of the target needs
an explicit `discard`. For `M=2^m`, fix the ideal finite-QPE contract for
classical outcome `y` as follows:

```text
K_y = (1/M) Σ_{r=0}^{M-1} exp(-2π i r y/M) U^r
E_y(ρ_AR) = (K_y ⊗ I_R) ρ_AR (K_y† ⊗ I_R)
```

When `U|u⟩=exp(2πiφ)|u⟩`, the probability is
`|(1/M)Σ_r exp(2πir(φ-y/M))|²`; if `φ=j/M`, outcome `y=j` has probability one.
General inputs have eigencomponent-dependent distributions and postmeasurement
changes. The contract does not deterministically read one eigenphase from an
unknown state. [Primary QPE reference, Section 5](https://arxiv.org/abs/quant-ph/9708016).

- **Candidate acceptance:** a known controllable unitary, an owned target,
  and a positive static bit count. Without an eigenstate promise, interpret
  the result through the full instrument above.
- **Candidate rejection:** an `Observe` operation used as a controlled power,
  overlapping control/target wires, or implicit loss of target ownership.
- **IR direction:** expand phase-register preparation, controlled `U^(2^j)`,
  inverse QFT, and measurement, then reverify. Publish bit weights, display
  order, and angle signs.

A variant parameterized by accuracy `ε` and failure probability `δ` requires
proof of the relation between necessary `m`, approximate-gate errors, and query
cost before adoption. A result containing `m` bits alone does not promise arbitrary accuracy
or confidence. A coherent premeasurement version returning the phase register
would have a separate contract.

<a id="43-simulate-時間発展の近似とアクセスモデル"></a>

### 4.3 simulate: approximate time evolution and access models

```text
simulate(H: HamiltonianAccess<A>, t: Real, ε: Positive;
         q: Q<A>) -[Unitary]-> Q<A>
```

**Proposed classification:** a family of ordinary `.qli` definitions. Require
Hermitian `H` and access through a local-term decomposition or a checkable block
encoding. Construct a finite circuit `U_t` and return ownership. The contract
specifies time units, the sign in `exp(-iHt)`, and the phase-sensitive operator
norm target `‖U_t-exp(-iHt)‖ ≤ ε`.

This signature covers methods constructing a data-space unitary `U_t` without
auxiliaries or with exact auxiliary zero return for all inputs and references.
If auxiliaries return only approximately, use a separate contract that returns
their ownership, or an `Observe` procedure with explicit discard and channel
error. A small approximation error does not justify pure release.

- **Candidate acceptance:** contracted term evolutions and a static subdivision
  count satisfying the product-formula error bound.
- **Candidate rejection:** non-Hermitian matrices, missing access or error
  evidence, or expansion exceeding the synthesis budget.
- **IR direction:** expand to a checked unitary sequence and bind approximation
  evidence and resource estimates. Independently distinguish IR unitarity from
  approximating the specified `H` within the stated error.

Start with product formulas and account for errors due to noncommuting terms.
LCU and qubitization variants require different access contracts.
[Product-formula error analysis](https://arxiv.org/abs/1912.08854),
[qubitization](https://arxiv.org/abs/1610.06546).

<a id="44-estimate-新規準備を繰り返して観測量を推定する"></a>

### 4.4 estimate: repeated fresh preparation for observable estimation

```text
estimate(prep: Prep_A, observable: Observable<A>, plan: SamplingPlan)
    -> HostResult<Estimate>
```

**Proposed classification:** a host-side planning API. Check each quantum trial
as an ordinary `.qli` `Observe` definition. `Prep_A` creates fresh resources
for each trial; it is not ownership of one unknown state.

Finite Pauli sums are the initial candidate scope. Estimate `tr(Oρ)` for the
prepared density operator `ρ`. Return the estimate, trial count, justification
of error/confidence, preparation and measurement assumptions, and host execution
failures. Separate sampling error from circuit approximation and device error.

- **Candidate acceptance:** fresh preparation on each trial, a measurable
  observable decomposition, a finite trial count, and an aggregation method.
- **Candidate rejection:** copying one `Q<A>` to increase trial count, reporting
  a single sample as the expectation itself, or unsupported confidence intervals.
- **IR direction:** lower each preparation/basis-change/measurement trial to
  verified IR; keep trial management and statistics on the host.

Variational loops update parameters on top of this procedure. The estimation
contract is separate from a claim that optimization converges to the ground
energy. [Primary VQE reference](https://arxiv.org/abs/1304.3061).

<a id="後続の契約候補"></a>

### Further contract candidates

Record transition access and target subspaces for quantum walks; coefficients,
normalization and success flags for LCU; and block encodings, polynomial
boundedness/parity, phase sequences, and approximation error for QSVT. These
remain candidate ordinary-definition families and evidence contracts. Extracting
a success block must not become an unconditional pure operation.
[Primary QSVT reference](https://arxiv.org/abs/1806.01838).

For syndrome extraction, record returned data and consumed meters, the commuting
checks measured, code space, correctable-error set, and classical-decoder
premises. The existing [bit-flip correction](algorithm-routines.md) does not
establish general QEC or fault tolerance.

<a id="5-標準への採用とaiからの還流"></a>

## 5. Standard adoption and feedback from AI exploration

1. **Candidate:** propose a structure from the corpus and multiple uses;
   explain its relation to existing components.
2. **Experimental implementation:** supply a contract ledger entry, ordinary
   definitions, IR correspondence, and acceptance/rejection cases. Publish
   unchecked assumptions. Connect the implementation to an explanation of its
   quantum-information concept, derivation and examples under the adopted
   library goal.
3. **Reuse evaluation:** assess at least two different uses and a problem not
   used to extract the abstraction. Check preservation of ownership, phase,
   error, and cost contracts.
4. **Standard adoption:** review contract stability and validation evidence;
   review computational reuse, the concept-to-code reading path and the explicit
   specification/evidence together. Establish public names, compatibility, and
   migration. Do not register
   numerical example agreement as a general proof.
5. **Continuing evaluation:** return frequent patterns found by humans or AI
   to the candidate stage. Frequency alone does not justify adoption; apply
   the same verification and reuse evaluation.

Promoting a component to an ordinary definition does not automatically enlarge
the sealed primitive set or verifier trust boundary. A needed language form
or primitive requires separate review of its necessity, meaning, and checking
rules.

The ledger should support finding components by resources, effects, access
capabilities, premises, and error budgets. This designs **units for AI search**.
Evaluate any reduction in search cost on the same problem set and computation
budget, comparing valid-candidate rates, failed checks, generated-circuit costs,
and reuse rates. Do not claim a demonstrated search-space reduction or discovery
of new algorithms without such results.

Current fixed-width `std::routines` APIs are an experimental starting point.
Provide a migration policy when stabilizing them. Changes in ownership,
effects, bit order, phase, error, or success conditions change the contract.
Retain the current compiler-bundled version model as the distribution baseline;
external package management needs separate design.


## 6. Entry conditions and future work order

L0–L5 classify library work, not releases or a requirement to complete every
candidate for v1. Generalization follows the language/evidence gates; finite
implementations do not establish generalized APIs or standard adoption.

| Area | Entry condition | Deliverables and completion status |
| --- | --- | --- |
| L0: contract-ledger design | Use current A0/A1 as input. | Twelve ordinary definitions registered in document format v1; track status, premises, implementation, validation, and cost. Machine-readable conversion has not begun. |
| L1: structural and data foundations | Specify `adjoint`, control, and finite repetition in A2. | Static inverse/control/finite repetition of functions with identical input/output types are implemented and checked, with fixed finite-product bit order and phase. Sized types and general static parameters remain open. |
| L2: first algorithm skeletons | L1 rules, IR correspondence, and substitution meaning contracts are available. | Fixed-width QPE usage examples are implemented. Generalized Grover/QPE structure and Shor's reuse are v1 targets, unimplemented. General `amplify`/QPE standard APIs and reuse in amplitude estimation/quantum counting remain open. |
| L3: arithmetic and hybrid plans | Establish A3 arithmetic, angles, observables, and host boundaries. | [Fixed arithmetic, N=15 order finding, and classical factor extraction](arithmetic-order-finding.md) are connected; retry conditions and probabilities are checked. General arithmetic, automatic retries, and shared `estimate` use in VQE/QAOA remain unimplemented. |
| L4: advanced skeletons with evidence | Finite exact meaning/auxiliary contracts come first as required by v0.1. Generalization needs A4 preservation effects, projected blocks, and error contracts. | Finite exact checker, three-argument computed form, public-function contract reuse, final-IR retention, and substitution are implemented and checked. Walk, LCU, QSVT, `simulate`, and general syndrome extraction remain later candidates; record each method's premises and verification status in the ledger. |
| L5: standardization and feedback into search | Establish reuse evidence across multiple uses and previously unused evaluation problems. | Manage public API versions and conformance checks; apply the same review from AI-generated candidate through adoption. Decide adoption separately for each component. |
