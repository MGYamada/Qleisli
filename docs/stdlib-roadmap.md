# Standard-library direction

Adopted direction; comprehensive generalized APIs are not selected.

## Adopted library goal

Build a BLAS/LAPACK-like foundation that teaches quantum information through concepts/derivations, readable source, examples/counterexamples and formal contracts with explicit proof status. Until v0.5 add algorithms to corpus; from v0.5 grow stdlib as a mathlib-style community effort under [STDLIB.md](../STDLIB.md). Keep specification intent review independent of implementation conformance; qlippy and general borrowing are future work.

## 2. Seven library areas

Areas classify concepts; candidate names are not new std APIs. Prefer ordinary definitions and specified static transformations; primitives need independent semantic/checking obligations.

| Area | Candidate standard vocabulary | Classification, dependencies, and contract focus |
| --- | --- | --- |
| Quantum primitives | Preparation, unitary operations, measurement, reset, discard | Build on sealed operations in `std::quantum` and `std::observe`; derived preparation and measurements are ordinary definitions. Do not introduce a `unitary` primitive executing arbitrary matrices. |
| Structural combinators | Control, inverse, repeat, tensor, compose, compute/uncompute | Inverse and control correspond to `adjoint` and `qif`; their finite forms already exist, while generalization remains proposed. Consider static transformations through language forms first, with composition expressed by ordinary definitions. Check phase, effects, complete resource transfer, finite expansion, and zero return. |
| Quantum data structures | Qubit, QReg n, quantum integers, indices, ancilla | Start from `Q<Bit>` and finite products. Sized types are language-form candidates; integer operations are ordinary-definition candidates. Specify width, signedness, bit order and valid subspaces; distinguish classical indices from quantum ownership. |
| Arithmetic | Reversible addition/multiplication, modular arithmetic, comparison | Ordinary definitions. State total basis functions and reversible extensions, overflow, modulus, and work regions. Define the action on the entire register space, including values outside valid residues modulo N. |
| Transforms | Hadamard transforms, QFT, basis changes, block encoding | Transform circuits are ordinary definitions. Block encoding needs an additional contract between the full unitary and a projected block. Preserve phase, axis order, approximation error, and normalization. |
| Algorithmic skeletons | Phase estimation, amplitude amplification, quantum walk, LCU, QSVT | Candidates for families of ordinary definitions. The static operation-parameter mechanism is undecided. Make input models, success conditions, iteration, precision, and costs public contracts. |
| Hybrid patterns | Measurement and feed-forward, variational iteration, syndrome extraction | One quantum trial is an ordinary `observe` definition. Trials, statistics, and optimization require separate host-side planning; host APIs are not `.qli` standard functions. |

## 4. First algorithm skeleton contracts

The following is design metanotation for contract candidates, not current source types. Operation descriptions capture no owners; input resources stay linear. Arbitrary free-vector bind is not adopted.

<a id="41-amplify-準備と判定から増幅を構成する"></a>

### 4.1 amplify: amplification from preparation and a predicate

A phase-fixed unitary preparation P defines |psi>=P|0>. Use exact oracle/reflection signs, access to P and P†, and an explicit finite iteration policy; success is sin²((2k+1)theta) for a=sin²theta. An unknown state or a mere Iso initializer supplies no reflection inverse. Measure separately and discharge all scratch exactly.

```text
amplify(P: U_A, good: A -> Bit, k: StaticNat) : () -[Iso]-> Q<A>
```

```text
Π_good = Σ_{x:good(x)=1} |x⟩⟨x|
O_good = I - 2Π_good
R_ψ = P (2|0_A⟩⟨0_A| - I) P†
G = R_ψ O_good
output = G^k |ψ⟩
```

- **Candidate acceptance:** two-bit uniform preparation, one marked item,
  `k=1`; `k=0` means preparation only, and an empty good set has success zero.
- **Candidate rejection:** inverting a `P` that measures, constructing a
  reflection from an owned unknown state alone, or identifying an unchecked
  phase oracle with `good`.
- **IR direction:** expand preparation and the checkable phase oracle, `P†`,
  zero-state reflection, and `P` into a finite static sequence and reverify.
  Retain the operator's global phase.

<a id="42-phase_estimate-位相に関するインストルメント"></a>

### 4.2 phase_estimate: an instrument for phase information

General phase estimation requires independently checked phase-fixed control/power access and the complete outcome/residual/reference instrument. Eigenstate promises, precision, bit order, error and decoding are explicit. Existing [sized source](sized-corpus-source.md) is bounded and experimental, not the complete candidate API.

```text
phase_estimate(U: ControlledAccess<U_A>, m: StaticNatPositive;
               q: Q<A>) -[Observe]-> (CBits[m], Q<A>)
```

```text
K_y = (1/M) Σ_{r=0}^{M-1} exp(-2π i r y/M) U^r
E_y(ρ_AR) = (K_y ⊗ I_R) ρ_AR (K_y† ⊗ I_R)
```

- **Candidate acceptance:** a known controllable unitary, an owned target,
  and a positive static bit count. Without an eigenstate promise, interpret
  the result through the full instrument above.
- **Candidate rejection:** an `Observe` operation used as a controlled power,
  overlapping control/target wires, or implicit loss of target ownership.
- **IR direction:** expand phase-register preparation, controlled `U^(2^j)`,
  inverse QFT, and measurement, then reverify. Publish bit weights, display
  order, and angle signs.

<a id="43-simulate-時間発展の近似とアクセスモデル"></a>

### 4.3 simulate: approximate time evolution and access models

Simulation needs an explicit Hamiltonian/access model, actual unitary realization, whole-space action and composition/error budgets. A mathematical Hermitian matrix or an imported name does not grant efficient access. Exact cleanup remains separate.

```text
simulate(H: HamiltonianAccess<A>, t: Real, ε: Positive;
         q: Q<A>) -[Unitary]-> Q<A>
```

- **Candidate acceptance:** contracted term evolutions and a static subdivision
  count satisfying the product-formula error bound.
- **Candidate rejection:** non-Hermitian matrices, missing access or error
  evidence, or expansion exceeding the synthesis budget.
- **IR direction:** expand to a checked unitary sequence and bind approximation
  evidence and resource estimates. Independently distinguish IR unitarity from
  approximating the specified `H` within the stated error.

<a id="44-estimate-新規準備を繰り返して観測量を推定する"></a>

### 4.4 estimate: repeated fresh preparation for observable estimation

Each trial freshly prepares resources; destructive measurement returns classical data for host aggregation/statistical error. Do not copy an unknown state or turn expectation values into individual outcomes. Host optimizers and retries are outside current std APIs.

```text
estimate(prep: Prep_A, observable: Observable<A>, plan: SamplingPlan)
    -> HostResult<Estimate>
```

- **Candidate acceptance:** fresh preparation on each trial, a measurable
  observable decomposition, a finite trial count, and an aggregation method.
- **Candidate rejection:** copying one `Q<A>` to increase trial count, reporting
  a single sample as the expectation itself, or unsupported confidence intervals.
- **IR direction:** lower each preparation/basis-change/measurement trial to
  verified IR; keep trial management and statistics on the host.

<a id="後続の契約候補"></a>

### Further contract candidates

Further block-encoding, walk/QSVT and preservation contracts require their own projectors, normalization, full unitary completion, capabilities, approximation and evidence rules. A successful projected block is not an unconditional pure operator.

<a id="5-標準への採用とaiからの還流"></a>

## 5. Standard adoption and feedback from AI exploration

Adopt only with a fixed public contract, readable implementation, multiple executable clients, independent semantic/fault tests, actual-IR binding/proof status and specification review. Record unmet gates in Issues; informed authoring is not a model benchmark.

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

## 6. Entry conditions and future work order

Library work follows actual programs and reusable verified components. [Public ledger](stdlib-contracts.md), [template](stdlib-contract-template.md), [static forms](static-operations.md) and v1/S05/PR/RS gates govern promotion. Comprehensive hierarchy and general operation/borrowing APIs remain open.

| Area | Entry condition | Deliverables and completion status |
| --- | --- | --- |
| L0: contract-ledger design | Use current A0/A1 as input. | Twelve ordinary definitions registered in document format v1; track status, premises, implementation, validation, and cost. Machine-readable conversion has not begun. |
| L1: structural and data foundations | Specify `adjoint`, control, and finite repetition in A2. | Static inverse/control/finite repetition of functions with identical input/output types are implemented and checked, with fixed finite-product bit order and phase. Sized types and general static parameters remain open. |
| L2: first algorithm skeletons | L1 rules, IR correspondence, and substitution meaning contracts are available. | Fixed-width QPE usage examples are implemented. Generalized Grover/QPE structure and Shor's reuse are v1 targets, unimplemented. General `amplify`/QPE standard APIs and reuse in amplitude estimation/quantum counting remain open. |
| L3: arithmetic and hybrid plans | Establish A3 arithmetic, angles, observables, and host boundaries. | [Fixed arithmetic, N=15 order finding, and classical factor extraction](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md) are connected; retry conditions and probabilities are checked. General arithmetic, automatic retries, and shared `estimate` use in VQE/QAOA remain unimplemented. |
| L4: advanced skeletons with evidence | Finite exact meaning/auxiliary contracts come first as required by v0.1. Generalization needs A4 preservation effects, projected blocks, and error contracts. | Finite exact checker, three-argument computed form, public-function contract reuse, final-IR retention, and substitution are implemented and checked. Walk, LCU, QSVT, `simulate`, and general syndrome extraction remain later candidates; record each method's premises and verification status in the ledger. |
| L5: standardization and feedback into search | Establish reuse evidence across multiple uses and previously unused evaluation problems. | Manage public API versions and conformance checks; apply the same review from AI-generated candidate through adoption. Decide adoption separately for each component. |
