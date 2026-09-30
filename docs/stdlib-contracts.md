<a id="l0-同梱標準部品の契約台帳"></a>

# L0: Contract ledger for bundled standard-library definitions

Status: **Ledger format v1; 12 public definitions recorded** (2026-09-26).
This is the initial ledger for the [Layer 3 plan](stdlib-roadmap.md). It covers
ordinary bundled `.qli` definitions; the [module/API specification](standard-library.md)
lists sealed APIs separately. This English edition is authoritative and replaces
the earlier Japanese edition. The three arithmetic entries below complete the
record of already implemented APIs; they introduce no new definitions or rules.
This ledger is not yet a machine-readable public function-contract schema.
The [finite semantic-contract kernel](semantic-contracts-v0.1.md) now checks
typed operator contracts and a scoped source form, while
[function evidence](function-contracts-v0.1.md) connects explicit client
specifications to retained implementation proofs. Automatic conformance
checking of all ledger entries, including observations and isometries, remains open.

Ledger **format v1** is not the product's **v1 release milestone**. The
[release plan](release-milestones.md) requires finite compositional meaning
contracts with independently checked implementation evidence for v0.1;
the bounded checking path is implemented separately. Documentation and
regression evidence in this ledger do not automatically issue those proofs.

Under the [adopted library goal](stdlib-roadmap.md#adopted-library-goal), this
ledger supplies the explicit specification/evidence part of an integrated
computational foundation and quantum-information textbook. Future component
reviews must connect these contracts to conceptual explanations, derivations,
readable implementations and worked examples. Existing entries retain their
recorded status; documentation coverage and open proofs must remain visible.
This direction does not change ledger format v1 or claim complete coverage.

The 2026-09-30 [contribution conventions](../STDLIB.md) supply a short template
and filled QFT2/Add2/corpus phase-oracle contracts. Their CI linter checks
documentation sections, scoped status dimensions and links; it neither converts
this whole ledger to a machine evidence schema nor proves conformance. Until
v0.5.0, new algorithms generally remain in corpus; from v0.5.0, reviewed
mathlib-style library growth uses those conventions. Existing entries stay
experimental with their current contracts and proof status.

**Source-documentation follow-up (2026-09-28):** all four bundled files have
module documentation and their twelve public/three private definitions have
English docstrings. [The documentation extension](documentation-comments.md)
retains descriptions outside executable IR; no public `.qli` signature, effect,
meaning, ledger contract version or adoption status changes. The
[`every_bundled_module_and_public_or_private_definition_has_documentation`](../tests/documentation.rs)
regression checks coverage, not semantic truth of the prose. Existing semantic
regressions and independent verification remain required.

<a id="共通項目"></a>

The 0.2.0 [machine-interface host APIs](machine-interface-spec.md#020-host-api-mapping) are tracked separately from these twelve ordinary bundled definitions. Sized `qft`, `qpe`, preparation and `CBits` helpers remain corpus/local candidates, unimplemented as public standard APIs. Their production source/IR gates follow the [staged continuation](verification-migration-v0.2.md); standard adoption generally waits until v0.5.0 and requires separate implementation, verification and proof status in the ledger.

## Common contract fields

The [QLT plan](https://github.com/MGYamada/Qleisli/issues/50) selects a future test surface for independent
mathematical references, structural cost regressions and doctests. QFT2/3 and
modular increment are its [initial source drafts](../tests/fixtures/qlt_design/README.md).
This is planned tooling, not a new public `.qli` API or additional verification
authority. All entries still undergo ordinary checking. QLT results will be
recorded separately from implementation, contract verification and proof;
an exact Rust test result will not be labelled a Lean certificate. No current
ledger contract version, adoption state or historical result changes here.

The [0.2.0 tuple correction](tuple-shapes.md) does not change these twelve
definitions' explicit binary signatures, ownership or numerical contracts.
Their types follow the [structural equality rules](type-system.md); n-ary callers
must convert explicitly. This migration adds no public standard-library API,
and does not upgrade an entry's proof or adoption status.

- **Classification, version, and adoption:** Every entry is an ordinary `.qli`
  definition, contract version 1, with **experimental API** status. It ships
  with the compiler. Revise its contract when its public name, type, ownership,
  effect, phase, or bit order changes. Inclusion in this ledger does not confer
  generalized standard-API status. Broader reuse, explicit assumptions,
  conformance evidence, and the [adoption criteria](stdlib-roadmap.md) remain
  necessary for that decision.
- **Checking entry points:** `check_project` / `compile_project` check all
  declarations; each ordinary quantum function's IR passes independent `verify`.
  Bundled origin grants no exemption.
- **Quantum interface:** Consume the input ownerships and return only those
  present in the result. Extend each operator or instrument by the identity on
  unmentioned reference systems. Separate ownership does not imply a product state.
- **Evidence status:** Bodies are implemented. The finite cases cited below
  have numerical regression evidence, using `f64` with algorithm tolerance
  `1e-12`. Such evidence is distinct from the specified exact operator, and does
  not prove general source-to-IR meaning preservation or algorithm correctness.
  Those general machine-checked guarantees remain incomplete.
- **Capacity and capabilities:** The implementation limits individual finite
  tables and registers to 12 bits. Static transformations share the
  [expansion budget](static-operations.md). The reference executor is supported;
  physical synthesis cost and external-device guarantees are unevaluated.

<a id="登録項目"></a>

## Registered definitions

Use the document-only abbreviations `B2=(Bit,Bit)`, `B3=(B2,Bit)`, and
`B4=(B2,B2)`. These are finite product types, not source aliases or sized types.
Bits carry weights `1,2,4,8` from left to right. A mathematical product domain
does not merge source parameters: `xor2` and `and2` take two `Bit` arguments,
and `parity_zz` takes two `Q<Bit>` arguments. Every other public definition in
this ledger takes one quantum argument.

| ID and API | Type and effect | Meaning, assumptions, and phase | Body and contract |
| --- | --- | --- | --- |
| B001 `std::basis::xor2` | Two `Bit` arguments → `Bit`; basis function | Total `(x,y) ↦ x xor y` on all four inputs; noninjective as a product-domain map. Not a quantum primitive. | [basis.qli](../stdlib/src/basis.qli), [basis-call and lifting boundary](standard-library.md#位相オラクル) |
| B002 `std::basis::and2` | Two `Bit` arguments → `Bit`; basis function | Total `(x,y) ↦ x and y` on all four inputs; noninjective. May supply a predicate for reversible XOR computation into an auxiliary; does not produce a measurement result. | [basis.qli](../stdlib/src/basis.qli), [basis grammar](syntax-v0.md) |
| R001 `std::routines::hadamard2` | `Q<B2> -> Q<B2>`, `Unitary` | `H⊗H`; no state promise. Used independently by Grover and Bernstein–Vazirani. | [routines.qli](../stdlib/src/routines.qli), [routine contracts](algorithm-routines.md) |
| R002 `std::routines::reflect_uniform2` | `Q<B2> -> Q<B2>`, `Unitary` | `D=2\|s⟩⟨s\|-I`, `\|s⟩=(H⊗H)\|00⟩`. The private total predicate `nonzero2` and a label-preserving Z certify the auxiliary's zero return. | [routines.qli](../stdlib/src/routines.qli), [reflection phase](algorithm-routines.md#反射の位相) |
| R003 `std::routines::measure_x` | `Q<Bit> -> CBit`, `Observe` | Measure X eigenvalue `(-1)^b` and consume the target. Interpret the instrument on the whole system, including references. | [routines.qli](../stdlib/src/routines.qli), [routine contracts](algorithm-routines.md) |
| R004 `std::routines::measure_z2` | `Q<B2> -> (CBit,CBit)`, `Observe` | Consume both data wires. Return left then right results; their register weights are 1 and 2. | [routines.qli](../stdlib/src/routines.qli), [routine contracts](algorithm-routines.md) |
| R005 `std::routines::parity_zz` | Arguments `Q<Bit>,Q<Bit>` → `((Q<Bit>,Q<Bit>),CBit)`, `Observe` | Projective measurement with `P_s=(I+(-1)^s Z⊗Z)/2`. Return both data wires and consume the meter; preserve coherence within each parity subspace. | [routines.qli](../stdlib/src/routines.qli), [whole-system instrument](algorithm-routines.md#パリティ測定の全体系での意味) |
| F001 `std::transforms::qft2` | `Q<B2> -> Q<B2>`, `Unitary` | `F_4\|x⟩=Σ_y exp(2πixy/4)\|y⟩/2` on every input, including its phase and output-bit reversal. | [transforms.qli](../stdlib/src/transforms.qli), [static operations and QPE](static-operations.md) |
| F002 `std::transforms::qft3` | `Q<B3> -> Q<B3>`, `Unitary` | `F_8\|x⟩=Σ_y exp(2πixy/8)\|y⟩/√8`, with `x=a+2b+4c`. No general-size or approximate-QFT API. | [transforms.qli](../stdlib/src/transforms.qli), [static operations and QPE](static-operations.md) |
| A001 `std::arithmetic::increment2` | `Q<B2> -> Q<B2>`, `Unitary` | `\|y⟩ ↦ \|(y+1) mod 4⟩` for all `0≤y<4`, with amplitude +1. Overflow wraps. Consume and return both wires; no auxiliary, measurement, or state promise. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [arithmetic contracts](arithmetic-order-finding.md#通常定義の算術契約) |
| A002 `std::arithmetic::add2` | `Q<(B2,B2)> -> Q<(B2,B2)>`, `Unitary` | `\|x,y⟩ ↦ \|x,(y+x) mod 4⟩` for all `0≤x,y<4`, with amplitude +1. The first pair is `x`, the second `y`; retain `x` and return all four wires in those positions. No auxiliary, measurement, or state promise. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [arithmetic contracts](arithmetic-order-finding.md#通常定義の算術契約) |
| A003 `std::arithmetic::mul2_mod15` | `Q<B4> -> Q<B4>`, `Unitary` | `\|y⟩ ↦ \|2y mod 15⟩` for `0≤y<15` and `\|15⟩ ↦ \|15⟩`, each with amplitude +1. Return all four wires in order `(d,a,b,c)` from input `(a,b,c,d)`. No residue-range promise, auxiliary, or measurement. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [full-space arithmetic contract](arithmetic-order-finding.md#通常定義の算術契約) |

For B001/B002, noninjectivity of the full product-domain map is a mathematical
obstruction to an isometric lift. The surface call `xor2(p)` or `and2(p)` with
`p:(Bit,Bit)` is instead an arity error: the declaration has two parameters and
calls do not implicitly uncurry a tuple. Explicitly destructure the lift input
with `do (a,b) <- q; pure xor2(a,b)` (or `and2(a,b)`) to reach the injectivity
check, which rejects the full noninjective product-domain map. Calls with two
`Bit` expressions are valid basis syntax; injectivity belongs to the complete
map of the enclosing `do/pure` expression. `with_computed` can use either named
predicate on its semantic product domain.

<a id="受理拒否費用ir検証根拠"></a>

## Acceptance, rejection, cost, IR, and evidence

Costs below are for the stated finite source bodies and logical IR. They do not
give a physical backend's gate count. All emitted IR is independently verified.

| ID | Acceptance / rejection | Logical cost and IR correspondence | Regression evidence |
| --- | --- | --- | --- |
| B001–B002 | Accept ordinary basis calls and auxiliary predicates. Reject a noninjective complete lift map; distinguish the arity error above. | Enumerate four basis inputs. A basis declaration alone emits no quantum IR. Calls contribute to a surrounding `LiftBasis` table or a named `ComputeUseUncompute` predicate table. | [`bundled_basis_functions_control_a_product_register`](../tests/compile.rs); [`basis_call_arity_is_distinct_from_lift_injectivity`](../tests/specification_boundaries.rs). |
| R001 | Accept a two-bit product; reject wrong types and consumed ownership. | Two H gates, no auxiliary: `Split; Gate; Gate; Join`. | [`bernstein_vazirani_recovers_every_two_bit_secret`](../tests/algorithms.rs), [`grover_all_targets_and_iteration_counts_match_amplitude_amplification`](../tests/algorithms.rs). |
| R002 | Accept the positive uniform reflection; reject wrong types and ownership reuse. | Four H gates, predicate computation/uncomputation, one Z, and one logical auxiliary. `ComputeUseUncompute` checks the structure; reference execution uses the factorized effective action. | Grover iteration test above; [`grover_reflection_and_its_negative_are_distinguished_under_control`](../tests/static_operations.rs). |
| R003–R004 | Accept observation; reject calls in a `unitary` body and old ownership after measurement. | R003: one H and one `MeasureZ`. R004: one `Split` and two `MeasureZ` operations, consuming both wires. | [algorithm tests](../tests/algorithms.rs), especially [`derived_routines_cannot_bypass_ownership_effect_or_basis_type_checks`](../tests/algorithms.rs). |
| R005 | Accept separately owned, possibly correlated data. Reject duplicate input ownership and implicit discard of returned data. | One `Init0`, two `Cnot`, one `MeasureZ`. At most the two data wires and one internal meter are live within this routine. | [`parity_measurement_keeps_coherence_within_each_parity_sector`](../tests/algorithms.rs), [`single_bit_flip_recovery_preserves_entanglement_with_a_reference`](../tests/algorithms.rs). |
| F001–F002 | Accept the exact product types. Reject wrong types, implicit discard, and aliased control/target resources. | F001: two H and two controlled T gates plus output-axis reversal. F002: three H and five controlled T gates plus reversal. No auxiliary; expand ordinary calls and `ApplyUnitary`. Inverse/control expansion budgets include axis-permutation tables. | [static-operation tests](../tests/static_operations.rs): all eight QPE phases, off-grid phase distributions, references, and rejection cases. |
| A001 | Accept every two-bit input, including 3→0. Reject `Q<Bit>` and reuse after `increment2(q)`. | One `Split`, one `Cnot`, one `Gate(X)`, one `Join`; two data wires, zero auxiliary. Static inverse/control/repetition use the checked finite-circuit path. | [`increment_and_add_match_modular_arithmetic_on_every_basis_input`](../tests/order_finding.rs) covers all four inputs; [`arithmetic_and_order_finding_obey_types_effects_and_ownership`](../tests/order_finding.rs) covers type/reuse rejection. |
| A002 | Accept every pair of two-bit values and arbitrary correlated inputs. Require the exact product tree; reject wrong types, duplication, and implicit discard. | Three `Split`, one `Toffoli`, two `Cnot`, three `Join`; four data wires, zero auxiliary. Carry uses the original low bits. Static transformations preserve the specified order. | [`increment_and_add_match_modular_arithmetic_on_every_basis_input`](../tests/order_finding.rs) covers all 16 basis inputs; [`arithmetic_round_trip_preserves_four_entangled_references`](../tests/order_finding.rs); shared rejection test above. |
| A003 | Accept all 16 values, including 0 and 15. Reject wrong product types and resource misuse. There are no modulus or multiplier parameters. | Three `Split` and three `Join` encode a four-axis rotation, with no primitive gates in an ordinary call. Static inverse/control/repetition materialize a 16-entry, zero-phase permutation in `ApplyUnitary`; physical routing/synthesis is not free by this assertion. Four data wires, zero auxiliary. | [`modular_multiply_powers_and_inverse_cover_the_full_register_space`](../tests/order_finding.rs) covers all 16 inputs, powers 0–4, and inverse; the reference round-trip and rejection tests above; [`qpe_preserves_reference_coherence_in_the_degenerate_fixed_subspace`](../tests/order_finding.rs). |

The arithmetic phase contracts follow the specified X/CNOT/Toffoli permutations
and ordered wire interfaces. Basis-output distributions and inverse round trips
alone are not a general proof of exact operator phase or compiler correctness.
The three entries remain experimental fixed-width APIs; the N=15 example does
not establish general efficient arithmetic or Shor implementation.

Algorithm success probabilities do not follow automatically from these types.
Grover's marked-set size, Bernstein–Vazirani's linear-oracle promise, the error
model for correction, and QPE precision are separate assumptions recorded in the
[corpus](algorithm-corpus.md) and example contracts.

This ledger records all 12 public definitions in its initial format.
Generalized `amplify`/`phase_estimate` APIs, evaluation on multiple previously
unseen tasks, and automatic evidence-schema checking remain L2-and-later work.

## Sized corpus candidates before standard adoption

The [corpus-first continuation](../corpus/sized/README.md) supplies two ordinary
source definitions through an experimental development compiler. These are
case-local candidates, not additions to the twelve bundled APIs or a frozen
module hierarchy. The [source contract](sized-corpus-source.md) distinguishes
language forms, sealed operations and ordinary definitions.

| Candidate | Contract and scope | Current verification | Standard adoption condition |
| --- | --- | --- | --- |
| `xor_into[n]` | Two `Q<Bits<n>>` owners in and out; unitary, phase +1, corresponding-bit XOR, n=1/2/4/8 plus local n=0. No zero-input promise. | Actual generated hierarchy independently inspected; every basis column and coherent reference columns compared to the formula. | Production source/call support and independently bound algorithm contract, preservation/compatibility gates and a reviewed public module/API. |
| `ghz[n]` | One `Q<Bits<n>>` owner in and out; unitary H on low bit then controlled X fanout, n=1/2/3/8. GHZ preparation requires all-zero input. | Full circuit checked on every basis input, beyond the preparation premise, plus coherent reference columns. | Same source/contract gates; keep full unitary meaning distinct from the zero-input preparation claim. |

The source comments and corpus explanation form the initial reading surface.
General natural-size proofs and source preservation remain open; native tests
are not those proofs. Keep source-specific licenses before any standard adoption.

The [QFT continuation](../corpus/sized/qualtran_qft/README.md) adds the case-local
`fourier[n]: Q<Bits<n>> -> Q<Bits<n>>`, unitary with the positive Fourier
matrix, and `inverse_fourier[n]`, an ordinary imported adjoint client. Widths
1/2/3/4/8 have native reconstruction and complete forward/inverse numerical
columns; forward artifacts also match independently requested Fourier meaning.
Repeated calls share the compiled body, and a framed call preserves reference
correlations. These remain experimental source candidates with production
integration, general source preservation and independently named inverse binding
open. Record the 255 width-eight H/phase applications separately from 160
forward definitions and the source's 36 H/controlled-phase operations; sharing
does not certify an execution cost reduction. Existing bundled APIs are unchanged.

The [coherent QPE continuation](../corpus/sized/qualtran_qpe/README.md) adds
ordinary case-local `hadamard_bits`, `evolve` and `estimate` candidates.
`hadamard_bits[n]` implements H tensor n on arbitrary input. `evolve[n,j,d]`
phases the low target bit by `exp(2*pi*i*j/2^d)` and preserves the rest.
`estimate[n,m,U]` is unitary, consumes/returns both quantum registers, and
requires declared Controlled access to its transparent `Op<Bits<n>>` provider.
Its complete Walsh/DFT/operator-power contract and zero-phase-input specialization
are in the corpus explanation. Small cases pass full-column/reference and
diagnostic branch-vector checks, including off-grid and global-phase probes.
The 2026-09-30 user decision defers further maximum-size validation. Standard
adoption still needs independent named QPE binding, initialization/measurement
into `CBits`, production source/runtime integration and reviewed public APIs;
these definitions do not extend the bundled library or claim instrument proof.

The [shared arithmetic continuation](../corpus/sized/qualtran_arithmetic/README.md)
adds five case-local ordinary candidates, each with unitary effect and phase +1
on its stated permutation. All input owners are returned, with no scratch.

| Candidate | Contract | Verification and adoption |
| --- | --- | --- |
| `all_ones[n]` | `(Q<Bits<n>>,Q<Bit>)` maps to the same owner group, flipping the target iff all control bits are one; true for the local empty case. | Recursive actual controls; small native/finite checks and complete basis/reference tests. |
| `increment[n]` | `Q<Bits<n>>` maps to itself with modular addition by one. | Coherent carry before low-bit updates; wrong-order/missing-carry counterexamples detected. |
| `add_k[n,K]` | Same register type, modular addition by K, including zero and wraparound. | Shared increment K times; nK X applications, without an efficient synthesis claim. |
| `invert_bits[n]` | Same register type, XOR with `2^n-1`. | Shared complement used twice in equality; phase-sensitive regression coverage. |
| `equals[n]` | `(Q<Bits<n>>,Q<Bits<n>>,Q<Bit>)` maps to the same owner group, `t` becoming `t xor [x=y]`. | Both input registers restored; both target values and coherent references checked, including missing restoration and extra phase faults. |

Widths 0–3 pass the [recorded tests](../corpus/sized/arithmetic-validation.json);
zero width is a local boundary test. These candidates require production
source/call integration, independently bound arithmetic contracts, preservation
and compatibility gates, reviewed cost expectations and a public module/API
decision before standard adoption. The twelve bundled definitions are unchanged.

The [local QPE clients](../tests/fixtures/sized_clients/README.md) add six
Qleisli-authored integration candidates, also outside the bundled APIs:

| Candidate | Unitary contract and premises | Verification/adoption status |
| --- | --- | --- |
| `order_phase[n,m,U]` | Same complete quantum phase/target group in and out; shared QPE for phase-fixed U with declared Controlled access. Order interpretation requires a specified permutation/orbit and zero phase input. | Tested with the actual `mul_two` provider; no generic order-recovery or measured API claim. |
| `mul_two[n]` | Same `Q<Bits<n>>`, scalar +1 modular doubling for residues below `2^n-1`, fixing the unused all-ones label; n>=2. | Full small-input/reference checks including n=4,N=15; not general modular synthesis. |
| `prepare[n,j,d]` | Same register, low-bit `H P(j,d) H` with spectator identity; n>=1 and normalized dyadic phase bounds. | Complete circuit phase retained; from zero, low-bit success is `sin(pi*j/2^d)^2`. |
| `reflect_low[n]` | Same register, phase-fixed low-bit Z with spectator identity. | Exact dyadic rule; not a general n-qubit zero-state reflection. |
| `grover[n,j,d]` | Same register, `A Z A† Z` for that exact shared A. | Actual source calls and inverse; wrong sign/conjugation detected by full-state tests. |
| `amplitude_phase[n,m,j,d]` | Same phase/target group, first A on target then shared QPE of G. Probability interpretation additionally requires zero initial phase/target. | p=0/1, aligned/off-grid and spectator cases pass; numerical decoder is diagnostic only. |

The [record](../tests/fixtures/sized_clients/validation.json) covers 432 basis
and 31 coherent/reference columns. These clients still require initialization,
measurement into `CBits`, classical-result integration, independently bound
algorithm contracts, production source/runtime and compatibility gates before
standard adoption. They do not fix a general library module organization.
