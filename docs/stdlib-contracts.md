<a id="l0-同梱標準部品の契約台帳"></a>

# L0: Contract ledger for bundled standard-library definitions

Ledger format v1 covers twelve implemented experimental ordinary public definitions, not all sealed APIs or product v1. [Module contract](standard-library.md), [contribution template](../STDLIB.md) and [library goal](stdlib-roadmap.md) govern adoption. Each has English source docs; documentation/linter coverage is no semantic certificate. Finite operator/function evidence exists separately; automatic full ledger conformance (especially iso/observe), general source preservation and generalized adoption remain open. Add algorithms to corpus until v0.5. Host APIs/sized helpers/QLT drafts are separate; QLT implementation is deferred until v0.4 after the type-system work.

<a id="共通項目"></a>

## Common contract fields

All entries contract v1, shipped experimental; change contract when name/type/owner/effect/phase/order changes. check_project/compile_project check every declaration and independent IR, no bundled exemption. Consume/return specified owners, full correlated reference identity; disjoint ownership does not imply separation. Cited f64 regressions use1e-12, distinct from exact mathematical contracts/general proofs. Finite table/register12 bits and shared static-expansion limits apply; physical/device costs unevaluated. Binary signatures retain structural tree, n-ary callers convert explicitly. Planned [QLT](https://github.com/MGYamada/Qleisli/issues/50)/[drafts](../tests/fixtures/qlt_design/README.md) add no current authority.

<a id="登録項目"></a>

## Registered definitions

Document abbreviations B2=(Bit, Bit), B3=(B2, Bit), B4=(B2, B2), bit weights1, 2, 4, 8 left-to-right. They are not source aliases/sized types. xor2/and2 have two classical arguments, parity_zz two quantum, others unary. Full table retains exact operators/instruments and all premises.

Calling xor2(p) with one product is arity error; explicit do(a, b)<-q;pure xor2(a, b) reaches full-map injectivity and rejects. Valid two-argument basis calls need no injectivity alone; with_computed uses semantic product domain. Noninjective lift and scoped XOR compute are different contracts.

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
| A001 `std::arithmetic::increment2` | `Q<B2> -> Q<B2>`, `Unitary` | `\|y⟩ ↦ \|(y+1) mod 4⟩` for all `0≤y<4`, with amplitude +1. Overflow wraps. Consume and return both wires; no auxiliary, measurement, or state promise. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [arithmetic contracts](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md#通常定義の算術契約) |
| A002 `std::arithmetic::add2` | `Q<(B2,B2)> -> Q<(B2,B2)>`, `Unitary` | `\|x,y⟩ ↦ \|x,(y+x) mod 4⟩` for all `0≤x,y<4`, with amplitude +1. The first pair is `x`, the second `y`; retain `x` and return all four wires in those positions. No auxiliary, measurement, or state promise. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [arithmetic contracts](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md#通常定義の算術契約) |
| A003 `std::arithmetic::mul2_mod15` | `Q<B4> -> Q<B4>`, `Unitary` | `\|y⟩ ↦ \|2y mod 15⟩` for `0≤y<15` and `\|15⟩ ↦ \|15⟩`, each with amplitude +1. Return all four wires in order `(d,a,b,c)` from input `(a,b,c,d)`. No residue-range promise, auxiliary, or measurement. | [arithmetic.qli](../stdlib/src/arithmetic.qli), [full-space arithmetic contract](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md#通常定義の算術契約) |

<a id="受理拒否費用ir検証根拠"></a>

## Acceptance, rejection, cost, IR, and evidence

Costs below concern stated logical source/IR, not hardware. All emitted IR independently verified. Arithmetic full-space phase follows X/CNOT/Toffoli/ordered routing; distributions/inverse round trips alone prove no general exact compiler phase. N=15 is fixed-width, not general Shor. Algorithm promises/precision/error models live in examples. General amplify/phase_estimate/new-task/evidence-schema adoption stays open.

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

## Sized corpus candidates before standard adoption

Tables record case-local candidates, outside bundled APIs; [sized source](sized-corpus-source.md) and retained corpus/fixture READMEs carry executable source, complete equations and measured costs. Historical large cases are preserved, no new maximum-size prerequisite.

[QFT](../corpus/sized/qualtran_qft/README.md): positive Fourier/inverse ordinary adjoint, full columns/reference and independently requested forward check; shared calls do not certify lower execution cost. [Coherent QPE](../corpus/sized/qualtran_qpe/README.md): arbitrary-input H layers/low-bit phase/provider-controlled QPE, both quantum registers returned, full phase/reference and off-grid tests. [Arithmetic](../corpus/sized/qualtran_arithmetic/README.md): full phase+1 permutations, no scratch; AddK repeats increment, not efficient synthesis. [Order/amplitude clients](../tests/fixtures/sized_clients/README.md): shared QPE, transparent modular/Grover providers, preparation prefix and separate interpretation promises. [Measured continuation](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md) adds small initialized/readout/classical clients; this is no generalized std API.

Before adoption require production source/runtime/independent named contract binding, source preservation/compatibility, reviewed resource/capability expectations, public module/API and separate proof/status records. Native numerical tests are not natural-size proofs. Keep upstream licenses and existing twelve contracts unchanged.

| Candidate | Contract and scope | Current verification | Standard adoption condition |
| --- | --- | --- | --- |
| `xor_into[n]` | Two `Q<Bits<n>>` owners in and out; unitary, phase +1, corresponding-bit XOR, n=1/2/4/8 plus local n=0. No zero-input promise. | Actual generated hierarchy independently inspected; every basis column and coherent reference columns compared to the formula. | Production source/call support and independently bound algorithm contract, preservation/compatibility gates and a reviewed public module/API. |
| `ghz[n]` | One `Q<Bits<n>>` owner in and out; unitary H on low bit then controlled X fanout, n=1/2/3/8. GHZ preparation requires all-zero input. | Full circuit checked on every basis input, beyond the preparation premise, plus coherent reference columns. | Same source/contract gates; keep full unitary meaning distinct from the zero-input preparation claim. |

| Candidate | Contract | Verification and adoption |
| --- | --- | --- |
| `all_ones[n]` | `(Q<Bits<n>>,Q<Bit>)` maps to the same owner group, flipping the target iff all control bits are one; true for the local empty case. | Recursive actual controls; small native/finite checks and complete basis/reference tests. |
| `increment[n]` | `Q<Bits<n>>` maps to itself with modular addition by one. | Coherent carry before low-bit updates; wrong-order/missing-carry counterexamples detected. |
| `add_k[n,K]` | Same register type, modular addition by K, including zero and wraparound. | Shared increment K times; nK X applications, without an efficient synthesis claim. |
| `invert_bits[n]` | Same register type, XOR with `2^n-1`. | Shared complement used twice in equality; phase-sensitive regression coverage. |
| `equals[n]` | `(Q<Bits<n>>,Q<Bits<n>>,Q<Bit>)` maps to the same owner group, `t` becoming `t xor [x=y]`. | Both input registers restored; both target values and coherent references checked, including missing restoration and extra phase faults. |

| Candidate | Unitary contract and premises | Verification/adoption status |
| --- | --- | --- |
| `order_phase[n,m,U]` | Same complete quantum phase/target group in and out; shared QPE for phase-fixed U with declared Controlled access. Order interpretation requires a specified permutation/orbit and zero phase input. | Tested with the actual `mul_two` provider; no generic order-recovery or measured API claim. |
| `mul_two[n]` | Same `Q<Bits<n>>`, scalar +1 modular doubling for residues below `2^n-1`, fixing the unused all-ones label; n>=2. | Full small-input/reference checks including n=4,N=15; not general modular synthesis. |
| `prepare[n,j,d]` | Same register, low-bit `H P(j,d) H` with spectator identity; n>=1 and normalized dyadic phase bounds. | Complete circuit phase retained; from zero, low-bit success is `sin(pi*j/2^d)^2`. |
| `reflect_low[n]` | Same register, phase-fixed low-bit Z with spectator identity. | Exact dyadic rule; not a general n-qubit zero-state reflection. |
| `grover[n,j,d]` | Same register, `A Z A† Z` for that exact shared A. | Actual source calls and inverse; wrong sign/conjugation detected by full-state tests. |
| `amplitude_phase[n,m,j,d]` | Same phase/target group, first A on target then shared QPE of G. Probability interpretation additionally requires zero initial phase/target. | p=0/1, aligned/off-grid and spectator cases pass; numerical decoder is diagnostic only. |
