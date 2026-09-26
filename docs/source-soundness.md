# Ideal soundness of the finite source derivation system

Status: **paper soundness theorems for the explicit mathematical rules**
(2026-09-26). This English document assembles the
[typing rules](source-typing-rules.md), [resource invariant R1](source-resource-rules.md),
[source semantics S1–S4](source-semantics.md), and
[static operator lemmas F1–F5](static-semantics.md). Its cases include the
current typed lift patterns and ordinary CBit literals/Boolean operations;
it introduces no additional language form, acceptance rule, or library API.

Q1 proves deterministic classical output and exact isometry/unitarity for pure
derivations. Q2 gives the finite instrument composition identities. Q3 proves
instrument soundness for all successful derivations of the stated rules.
These are general mathematical results with the premises in §1, not claims
about every program accepted by the Rust implementation. Establishing that
implementation correspondence remains an explicit obligation. The small Lean
component in §8 checks matrix algebra used in Q2, not the whole source theorem.

**2026-09-27 extension:** the three-argument computed form has a separate
[semantic-contract specification and local paper derivation](semantic-contracts-v0.1.md).
The additional leaf and conditional induction case below connect that rule
to this framework. The earlier Q1–Q3 proof and test record do not establish
the new Rust exact checker, lowering, or static substitution. No corresponding
Lean extension is claimed.

The later [function-contract supplement](function-contracts-v0.1.md) adds a
conditional FC-APPLY leaf and retained-action transformation argument. It
assumes independently checked actual-function equality and correct ordered
extraction. Those implementation premises and general source adequacy remain
open; the original Q1–Q3 or Lean results do not discharge them.

## 1. The theorem domain and complete interfaces

Fix a finite, acyclic declaration environment `D` checked by the explicit
type/effect/name rules, and a successful derivation

```text
D ; m ; E ; F ; R ; H |- e => v:T ! eps ; E' ; R' ; H' |> P.
```

Use these premises throughout:

1. Types, name lookup, declaration effects, exact parameter/result trees,
   scope projection, and all branch/auxiliary side conditions are those of
   the typing supplement. Every referenced declaration and both checked arms
   meet those rules, including targets of zero repetitions.
2. Resource transitions and issued-ID/SSA visibility conditions are R1's.
   `WF(E,F,R)` holds initially, so R1 provides `WF(E',F++[v],R')`. Every quantum
   holder is accounted for, including pending values and zero-width slots.
3. The ideal interpretation uses the exact matrices and Kraus operators in
   §3, the source composition equations in S1–S3, and the explicit layouts
   below. A table lift uses its checked total injection; a computed scope
   uses its all-input zero-return certificate.

These are premises of the **mathematical derivation and its interpretation**.
They do not assume the desired isometry or completeness of a composite source
program. The leaf identities are proved in §3 and combined below. They also
do not assume that Rust `verify`, `Lowerer`, or `sim` establishes all these
premises. Numeric capacity rejection and floating-point execution are outside
the ideal successful-derivation theorem.

The input quantum interface contains **all** live leaves of `(E,F)`, in a
fixed holder order. The output contains all live leaves of `(E',F,v)`.
Use each leaf's exact basis tree and the low-bit-first label convention of
S1–S4. R1 gives a bijection between these holders and live slots, and their
wire lists partition the physical axes. The coordinate maps between physical
axes and holder order are therefore unitary permutations. `Q<Unit>` contributes
a one-dimensional factor and one ownership obligation, not a removable value.

A classical input `gamma` assigns bit values to the available classical
leaves, consistently where IDs are shared. Output records are **decoded
classical values**, including the returned value, retained environment, and
unchanged classical projection of the opaque frame;
generated SSA names are not canonical mathematical outputs. Records are
classical alternatives, never superpositions. At expression boundaries the
typing rules fix the full quantum interface. When discussing internal
histories, allow a history-dependent intermediate Hilbert space `H_h`; only
after complete layout transport may their final maps be grouped together.

No product-state premise is imposed on the owned system, its opaque frame,
or an arbitrary finite external reference `K`. The frame is not discarded
when evaluating an argument, entering a callee, or leaving a block.

## 2. Finite interpretation and the induction measure

Basis T1 evaluates each basis expression on its finite carrier. The source
declaration graph is acyclic. Give declarations a dependency rank and use
structural recursion on expression, argument-list, statement-list, and block
derivations at each rank. Entering a callee or a static target decreases rank;
checking component expressions decreases derivation size. Each static
repetition count and each observation outcome set is finite.

Typed basis-pattern binding recurses on a finite pattern and decodes each
label in the original finite input carrier. Ordinary Boolean operands recurse
on smaller expressions in a fixed eager order, and truth-table updates are
total on their `CBit` inputs. These cases preserve the same finite measure.

This defines a finite ideal interpretation. In particular, no theorem below
infers termination from trace preservation. There is no dynamic loop,
unreported postselection, or exceptional successful execution that silently
drops probability mass in this derivation system.

For fixed input `gamma`, keep complete execution histories initially. Each
history `h` carries a decoded visible record, a quantum output layout, and
an operator `K_h` from the input interface to that history's output interface.
Measurement contributes a public bit; discard and reset may contribute
**private Kraus indices**. They are bookkeeping for summation, not source
values. A continuation may depend on its visible classical record, not on
an inaccessible private index or on quantum amplitudes. Classical copying
duplicates a bit value, not an execution history or its probability weight.

Intermediate coordinates are matched by the prescribed unitary layouts.
Keep subnormalized states throughout: neither a zero-probability history nor
any other history is divided by its trace. When several histories export the
same public value, sum their CP maps after aligning their quantum interfaces.

## 3. Exact semantic leaves

Every displayed local operator is embedded into the complete interface, with
identity on other live axes and `K`, and the input/output coordinate maps.
Such identities and permutations preserve the identities proved below.

### Pure leaves

`UNIT`, classical copy, quantum move, tuple construction, pattern binding,
and scope projection do not alter the physical quantum state. Their holder
coordinates may change by a permutation. R1 forbids a hidden quantum partial
trace at a wildcard, expression statement, or block exit.

For each fixed classical record `gamma`, a Boolean constant or truth-table
update has exactly one output record and quantum operator `I`. `true/false`
provide bits 1/0, and ordinary `not/and/xor` deterministically read visible
`CBit` values. Thus their singleton quantum Kraus family is complete and
unitary. Even noninjective classical `and` is admissible: the quantum operator
is identity for each fixed record, and the theorem does not demand reversible
classical processing. Operand computations remain separate preceding stages;
they may contain observation and cannot be erased by a constant truth result.

The sealed H, X, Z, and T matrices are exactly those in the language
specification. H is real symmetric with `H^2=I`; X exchanges the two basis
vectors; Z has diagonal entries `1,-1`; T has diagonal entries `1,zeta`,
where `zeta=exp(i*pi/4)` has unit modulus. Hence each has both inverse
identities `U†U=UU†=I`. CNOT and Toffoli are involutive permutations of their
complete bases. `split/join` are ordered tensor identifications; different
function input/output order contributes a permutation, not erasure.

Preparation is `J|x⟩=|x,0⟩` in the chosen order, so `J†J=I`. For a checked
injection `f:L_A->L_B`, the lift is

```text
V_f = sum_a |f(a)⟩⟨a|,
⟨a|V_f†V_f|b⟩ = ⟨f(a)|f(b)⟩ = delta_(a,b).
```

Thus the lift is an isometry. Equal bit count makes its finite injection
surjective, hence unitary. Greater width is an isometry without a surjectivity
claim. T1 supplies totality; type formation or linear ownership alone does
not supply injectivity.

With a typed basis pattern, `f(a)=eval(b,eta_p(a))` for every `a` in the
**original** `L_A`. The BP pattern induction and T1 supply a unique well-typed
valuation and result for each such label. Wildcards can forget labels during
this finite computation, but they do not change the domain of the displayed
inner-product calculation. Distinct-input equality of outputs still rejects
the lift. Removing a singleton Unit factor is compatible with injection;
forgetting an independent Bit is not. This is basis-label manipulation, not
quantum weakening or a new partial-trace leaf.

If a lower-rank static target has exact unitary body operator `U`, its
adjoint `U†` and every finite power `U^r`, including `I` at zero, are unitary.
For `qif`, the disjoint control gives

```text
C = |0⟩⟨0| tensor U0 + |1⟩⟨1| tensor U1,
C†C = |0⟩⟨0| tensor U0†U0 + |1⟩⟨1| tensor U1†U1 = I,
CC† = I.
```

The target's final return permutation and scalar phase are part of `U`.
F1–F5 establishes the corresponding **mathematical circuit algorithms** under
their interface premises. Q1 below obtains target unitarity from the body
induction; it does not infer source-body correctness merely from verifying
some unitary IR. That would conflate unitarity with meaning preservation.

For the source computed certificate, let `f:A->Bit` be total, and let the
expanded auxiliary chain have `z` Z gates and `t` T gates. With
`r=(4z+t) mod 8`, its checked compute/use/uncompute factorization is

```text
C_f† W C_f |x,0⟩ = zeta^(r f(x)) |x,0⟩,
D|x⟩ = zeta^(r f(x)) |x⟩.
```

All diagonal coefficients of `D` have unit modulus, so `D` is unitary. For
`sum_x |x⟩ tensor |r_x⟩` on source plus reference, the final auxiliary factors
as `|0⟩` independently of all `|r_x⟩`. This is R1/F3's all-input certificate.
It justifies the **whole atomic scope**; a standalone `bra(0)` release is not
a semantic leaf. `A=Unit` may still produce a scalar phase.

For the new `CERTIFIED-COMPUTED` leaf, use the distinct SC-COMPUTED premise.
The logical target u is a fixed unitary and the ordered body W is unitary;
the source rule additionally requires the exact equation `W Ef=Ef u`, where
`Ef=Cf E0` and `E0|x>=|x,0>`. Therefore

```text
Cf† W Cf E0 = Cf† W Ef = Cf† Ef u = E0 u.
```

The whole clean scope has operator u, hence both unitary identities. Tensor
the equation with an arbitrary reference identity to obtain zero return and
separation without a product-input premise. This proves the local mathematical
leaf even when W changes both data and auxiliary. The resource rule separately
requires the complete returned data/auxiliary ownership interface. An exact
matrix relation cannot establish those holder obligations or prove that the
Rust body extraction computed the correct W. These are explicit premises of
this extension, rather than consequences of earlier finite tests.

For FC-APPLY, the specification has fixed unitary operator u and the checked
implementation has U=u. The retained action therefore denotes that same
unitary, extended by identity on the caller frame/reference. Exact ordered
axis transport is unitary conjugation, and inverse/control/repetition preserve
the equality by the [FC-STATIC identities](function-contracts-v0.1.md#5-conditional-mathematical-soundness).
Neither function is applied to a duplicate runtime input. This supplies the
supplemental pure leaf assuming the function checker and extraction premises;
source bytes or names alone do not supply it.

### Observation leaves

For a one-bit target `q`, define `M_b=bra(b)_q tensor I_rest`. Measurement
returns visible bit `b` and consumes `q`. For a wider discarded register use
all its basis labels `x`; reset prepares a fresh zero target after consuming
the old one, with `N_b=ket(0)_(q') bra(b)_q tensor I_rest`.

```text
sum_b M_b†M_b = I,
sum_x (bra(x) tensor I)†(bra(x) tensor I) = I,
sum_b N_b†N_b = I.
```

Each identity follows from `sum_b |b⟩⟨b|=I` and `bra(0)ket(0)=1`.
Discard and reset hide the label after forming the corresponding Kraus sum.
Their maps are respectively `tr_q(rho)` and
`ket(0)bra(0)_(q') tensor tr_q(rho)`, in the stated output order. They remain
`Observe` even if a particular input makes their result pure. Zero-width
discard has one identity Kraus operator while still ending logical ownership.

## 4. Q1: pure determinacy, isometry, and unitarity

**Q1.** Under §1, if `eps <= Iso`, then for each fixed classical input `gamma`:

1. There is one decoded output classical record `d(gamma)`, independent of
   the quantum input state. It may forget or duplicate classical information.
2. The entire quantum output is given by an exact linear operator
   `V_gamma:H_in->H_out` with `V_gamma†V_gamma=I`.
3. If `eps=Unitary`, also `V_gamma V_gamma†=I`.

All statements extend with identity on any external reference. The claim is
per fixed classical input; it is not reversibility of a joint classical
register, and it does not identify operators that differ by scalar phase.

**Proof.** Use mutual induction with the measure of §2 and the strengthened
complete-interface invariant of §1. T3's effect upper bound excludes every
observation leaf and every call declared `Observe` from a pure derivation.
Ordinary `CBit` values are inputs, constants, copies/selected phis, or total
Boolean functions of previously available classical values. In a pure
derivation, the operand induction makes those values deterministic functions
of `gamma`; eager `not/and/xor` therefore produce one determined record.
Basis labels in a lift are coherent
indices, not reads into the ordinary classical environment. Thus value and
pure leaf cases return classical data determined by `gamma`.

The following structural cases simultaneously preserve this determinacy and
the claimed operator identities:

| Rule | Pure induction step |
| --- | --- |
| Pair, argument list, LET, SEQ | The first result record is determined. Apply the continuation hypothesis with that record and the complete pending frame; compose its operator with the first. |
| C-CONST, C-NOT, C-BOOL | Constants have exact operator `I`. Evaluate every operand once in order, compose their inductively determined operators, then apply the deterministic Boolean record update with operator `I`. Its noninjectivity on classical values does not affect quantum isometry. |
| Pattern and BLOCK/Close | Classical data is copied/forgotten deterministically; quantum holders are rearranged by a coordinate isomorphism. R1 and T2b prevent loss or resurrection of a quantum value. |
| Ordinary CALL | Arguments are evaluated once. Fresh value binding in the defining module preserves their decoded values; S1's source equation identifies the body instantiation. Use the lower-rank body hypothesis and S2's frame extension. T3 bounds its body effect by the declared call effect. |
| Classical IF | The pure condition returns one bit fixed by the input classical record. Use only the selected arm's operator, followed by its complete phi permutation as in S3. Both arms meet the static premises. No coherent sum of arms is used. |
| Sealed operation / lift | Use the pure identities of §3; initialization or width growth is at least `Iso`. |
| BP-NAME, BP-WILD, BP-PAIR within LIFT | Uniquely construct the isolated label valuation for each full-domain input. These compile-time steps add no operator; the ensuing lift still requires the same full-domain injection identity of §3. |
| Static forms | Evaluate inputs first, retaining their frame; use lower-rank unitary target hypotheses and the adjoint/power/control algebra of §3. |
| COMPUTED | Evaluate its source first; apply the certified `D` of §3. The internal auxiliary is removed only by that factorization. Its body has checked effect `Unitary`. |
| CERTIFIED-COMPUTED, supplemental case | Evaluate its source first; under SC-SOURCE's complete interface and SC-COMPUTED's exact equation, use the unitary u established by the new local leaf. Restore the untouched frame and close only the proven-zero auxiliary. |
| FC-APPLY, supplemental case | Evaluate its input once; use the fixed unitary u from independently checked U=u, with exact placement and the untouched caller frame. Input effects remain in the enclosing derivation. |

For compositions, `(WV)†(WV)=V†W†WV=I`; if both factors are unitary, the
other product is identity as well. Tensoring an isometry with an identity
and composing with coordinate permutations preserves these equations. Pure
classical selection chooses one such map for each fixed record.

When `eps=Unitary`, the effect rules exclude preparation and width-increasing
lifts, including those hidden in arguments or calls. Every surviving local
operator is unitary; structural interfaces and phi maps have complete equal
dimensions. The stronger identity follows by the same induction. Endpoint
dimension equality by itself is not the proof. Finally, declaration closure
removes only names/classical data and exposes all quantum leaves through the
result, so the statement applies to general ordinary declarations, not just
the unary signatures eligible for static transformation. This proves Q1.

## 5. Q2: finite adaptive instruments and hidden histories

A complete finite Kraus family has operators `A_h:H0->H_h` satisfying
`sum_h A_h†A_h=I_H0`. For every history `h`, including histories with zero
probability on a particular input, its continuation has operators
`B_(h,j):H_h->G_(h,j)` with
`sum_j B_(h,j)†B_(h,j)=I_(H_h)`. Source continuations actually depend only on
the visible part of `h`; allowing a separate family for each `h` makes the
algebra general enough to cover that restriction. It does not expose private
Kraus indices to source code.

**Q2a (adaptive completeness).** The composite family
`C_(h,j)=B_(h,j) A_h` is complete:

```text
sum_(h,j) C_(h,j)† C_(h,j)
 = sum_h A_h† (sum_j B_(h,j)†B_(h,j)) A_h
 = sum_h A_h† I_(H_h) A_h
 = I_H0.
```

This calculation uses only finite sums, adjoints, associativity, and the
displayed completeness premises. It does not require all `H_h` or `G_(h,j)`
to have the same dimension. Left multiplication of each `C_(h,j)` by an
isometry preserves the equation. In particular, complete output-layout phi
permutations preserve it. Repeating the calculation handles any finite
sequence and adaptive branch tree.

After transport into a common typed output space `Hout`, let `g(h)` select
the public classical value exported by history `h`. Define

```text
E_b(rho) = sum_(h : g(h)=b) K_h rho K_h†.
```

**Q2b (instrument properties).** If the transported full family is complete,
then every `E_b` is completely positive and trace non-increasing on positive
inputs, and `sum_b E_b` is trace preserving.

**Proof.** For arbitrary finite `K`, extension replaces each summand by
`(K_h tensor I_K) rho (K_h† tensor I_K)`. Positive `rho` remains positive
under each sandwich and their sum: its quadratic form on `v` is a sum of
nonnegative quadratic forms of `rho`. This proves complete positivity.
The sets `g^(-1)(b)` partition all histories exactly once. Cyclicity of the
finite-dimensional trace and completeness give

```text
sum_b tr(E_b(rho)) = tr(rho sum_h K_h†K_h) = tr(rho).
```

For a fixed `b`, its omitted operator sum is positive:
`I-sum_(g(h)=b) K_h†K_h = sum_(g(h)!=b) K_h†K_h >= 0`.
Equivalently its nonnegative trace contribution is at most the total.
This proves trace non-increase, also after reference extension. No step
normalizes a history, so zero-probability outcomes are included without a
special inverse or division.

Hiding internal records or discarding classical values changes `g` and groups
summands. Repeating a classical bit in the output changes the tuple label,
not the multiplicity of its history. In general
`sum_h K_h rho K_h†` is **not**
`(sum_h K_h) rho (sum_h K_h)†`; the latter introduces interference between
classical alternatives and can lose or gain trace.

Deterministic Boolean computation is another record function of this kind:
every history is assigned its truth result once. Different records may export
the same result of `and` or `xor`; then their CP maps are summed, never their
amplitudes. If operands observe, first use Q2a for **both** eager operand stages,
then group by the truth result using Q2b. A result such as constant false does
not erase those histories or permit skipping their quantum operations.

## 6. Q3: instrument soundness of all source rules

**Q3.** Under §1, for every fixed classical input and successful derivation,
there is a finite complete Kraus interpretation on its complete holder
interfaces. Grouping by the decoded output record gives a CP,
trace-non-increasing map for each record and a trace-preserving sum. These
properties hold with an arbitrary external reference. They apply to every
effect class; `Observe` need not contain an actual observation.

**Proof.** Induct mutually over the same successful derivations as Q1. Carry
the stronger assertion that all private histories remain available for the
completeness equation until any requested public grouping. The cases are:

- A pure leaf or a pure whole derivation has the singleton Kraus family
  `{V}`. Q1 or the corresponding leaf identity gives completeness.
- `C-CONST` has the singleton identity family and one fixed record. For
  `C-NOT/C-BOOL`, the operand induction supplies complete families; compose
  them in their strict evaluation order using Q2a, retain the pending frame,
  and append the deterministic identity leaf. Q2b groups histories by the
  resulting classical values. Neither absorbing Boolean values nor repeated
  classical input IDs remove or duplicate a history's probability weight.
- Measurement, discard, and reset have the complete families in §3, with
  the required visibility or hiding of the outcome label.
- Pair/argument evaluation and statement sequencing retain prior pending
  holders and use the continuation corresponding to each visible record.
  All intermediate types/layouts match by the resource and typing rules.
  Q2a composes their complete families, including any already hidden indices.
- Pattern binding, variable copy/move, and block exit only rename/reorganize
  interfaces or regroup classical records. R1 excludes quantum weakening;
  coordinate permutations and Q2b preserve completeness and public maps.
- A call evaluates its arguments once and uses the lower-rank body with
  values bound to fresh formals. S1's source instantiation equation and S2's
  extension over suspended caller holders give the correct full maps. Apply
  Q2a. A stronger declared effect is an upper bound, not an extra physical
  instruction; even an `Observe` declaration can have a singleton family.
- A classical `if` first gives condition histories. For each history its
  bit selects exactly one of the two fully checked arm interpretations.
  Each selected arm is complete by induction. S3's complete output phi adds
  a unitary transport; frozen classical phi assignments give the public
  grouping. Q2a and Q2b establish the result. The histories of the two arms
  are not coherently added, and their private intermediate dimensions need
  not be identified before the final typed interface.
- A lift, static operation, or certified computed scope follows its input
  expression with the isometry/unitary from §3. Apply singleton completeness
  and Q2a. This includes input expressions with observations and the pending
  `qif` control; the resulting whole effect can be `Observe`.
  In the lift case, typed pattern binding changes only the valuation used to
  construct the table, whose injectivity is still checked on every original
  input label. No measurement or hidden index is introduced by a basis wildcard.

For the new three-argument computed form, that last case is conditional on
the supplemental exact leaf and resource rule above: its singleton family
`{u}` is complete, and Q2a composes it after all source-expression histories.
This is a local extension of the paper argument, not a proof that the new
Rust checker, circuit extraction, or numerical interpreter meets its premises.
FC-APPLY contributes the singleton complete family `{u}` under its own
supplemental equality/extraction premises; compose it after input-expression
histories using Q2a. Sharing its immutable evidence does not duplicate a
history's probability or a runtime quantum holder.

In particular, observing a subsystem while evaluating a `qif` target can
change the pending control's conditional state through entanglement. Its
holder remains in the frame, but no unchanged-state or product-state claim
is used. The whole-interface induction covers this case as well.

Basis declarations introduce no runtime outcome; T1 supplies the checked
tables used by the lift/computed cases. These cases cover all expression,
statement, pattern, declaration, and auxiliary rules of the typing supplement.
Classical-output hiding at any boundary groups the already complete family,
and Q2b gives the stated public properties. This proves Q3.

S1–S3's **source interpretation equations** are used here, not their separate
source-to-IR correspondence premise. No assumption that source and compiled
Rust IR already agree is needed to prove soundness of this mathematical
source interpretation. Proving that agreement is subsequent work.

**Closed-entry corollary.** A checked parameterless `observe fn main()->C`
has no remaining quantum ownership by R1. Starting in the scalar vacuum state
of trace one, Q3 gives a normalized probability distribution on `C`.
It does not follow that finite-precision `run_closed` returns exact probabilities.

## 7. Source-to-IR obligations and limits of the result

| Source case | Exact semantic equation / remaining correspondence |
| --- | --- |
| Sealed preparation/gates/observation | Raw constructors must realize the matrices/Kraus operators of §3 on the recorded axes. Check source arity/type and independently verified IR interfaces separately. |
| Ordinary classical constants and Boolean operations | `ClassicalConst/Not/And/Xor` must realize the deterministic record update and quantum identity. Each operand fragment must occur once in source order; SSA inputs must be visible and outputs fresh. Noninjective classical functions are distinct from noninjective quantum lifts. |
| Basis lift | The emitted total table must equal T1's evaluation after the typed pattern valuation at every original source label, with the exact product encoding and preserved input-wire order. Wildcards must not reduce the enumerated domain. |
| Computed scope | The expanded checked chain and predicate table must be the same `W,f` as the atomic raw certificate, including all phase exponents. |
| Certified computed scope | SC-IR must retain the actual body W, fixed logical u, complete predicate f, and output-axis transport; the raw verifier must independently establish `W Ef=Ef u`. Static replacement by u uses that exact equation. Type trees and every private/outer holder remain separate correspondence obligations. |
| Function contract application | FC-CHECK independently validates/extracts both actual raw functions and checks U=u. FC-IR retains bound evidence, target placement, adjoint choice, and controls through final transformations. Source provenance is separate from a proof of source compilation. |
| Static forms | The body correspondence and ordered input/output interfaces must meet F1–F5. Unitarity of some emitted circuit does not establish that it is the intended body. |
| Ordinary call, pending frame, classical branch | S1–S4 composes already corresponding subderivations with complete layouts and decoded classical records. Rust snapshots, fresh-ID bookkeeping, and phi construction still need adequacy proofs. |

The semantic leaves and constructor induction are now proved for the
mathematical rule system. Coverage by syntax cases and an implementation
audit are not a universal relation between Rust acceptance and these
derivations. Q1/Q3 do not assert that all raw IR is expressible in source v0,
that a simulator is exact, or that algorithms and hardware meet their separate
contracts. Full Stage 1 completion still requires the stated source/checker
and translation obligations, recorded in the [roadmap](../ROADMAP.md).

## 8. Lean and finite implementation evidence

The targeted [Kraus module](../lean/Qleisli/Kraus.lean) uses exact finite
rectangular complex matrices. It checks the completeness algebra underlying
Q2a, with explicit completeness/isometry hypotheses. Its fixed intermediate
matrix dimensions are one instance of the history-dependent paper equation.
It is separate from the existing ownership-accounting projection and does
not formalize source typing, positivity, trace, hidden-history grouping,
arbitrary reference extension, or the Q1/Q3 induction. See the
[Lean theorem ledger](lean-resource-proof.md) for exact declarations and checks.

[tests/source_soundness.rs](../tests/source_soundness.rs) checks selected
compiled source programs against independent analytic expectations. These
finite numerical regressions exercise hidden observation histories, adaptive
branching with a correlated frame, coherent width growth, reset, and
zero-probability paths. They support the implementation audit, not the paper
theorems or universal source-to-IR equivalence.

| Regression | Independent analytic expectation |
| --- | --- |
| `hidden_measurement_histories_add_weights_despite_opposite_final_phases` | Two hidden Bell-measurement histories end in opposite-phase copies of zero; their probabilities sum to one without amplitude cancellation. |
| `adaptive_observation_preserves_joint_weights_correlations_and_coarse_graining` | Z/Z or X/X observations of `cos(pi/8)\|00⟩+sin(pi/8)\|11⟩` give six explicit joint weights and an independently computed marginal after hiding earlier records. |
| `injective_growth_keeps_reference_coherence_while_reset_erases_it` | A phase-bearing GHZ state gives X-parity weights `(1 ± 1/sqrt(2))/8`; resetting one subsystem instead gives eight uniform X outcomes. |
| `zero_probability_histories_do_not_execute_or_normalize_an_inactive_arm` | Either deterministic control polarity follows one history under a one-component budget; an inactive random arm cannot contribute weight or consume that budget. |

The four tests cover seven compiled fixtures. They compare all public outcome
weights and the unnormalized total with tolerance `1e-12`; the comparison
does not renormalize a possibly incorrect distribution.

For the subsequent lift-pattern/CBit extension, finite boundary evidence includes
[`basis_patterns_reject_wrong_shapes_duplicate_names_and_lost_bits`](../tests/specification_boundaries.rs),
[`ordinary_cbit_literals_and_operators_have_their_truth_tables`](../tests/specification_boundaries.rs),
and [`boolean_operands_are_eager_and_preserve_pending_quantum_ownership`](../tests/specification_boundaries.rs).
The exact finite checks
[`product_pattern_lift_is_a_full_basis_permutation_under_inverse_and_control`](../tests/static_semantics.rs)
and [`closed_classical_computation_selects_static_branches_and_preserves_output_axes`](../tests/static_semantics.rs)
exercise phase-sensitive static use. These examples do not prove R1/T1–T3,
S1–S4, Q1–Q3, or Rust adequacy; the paper case arguments above are separate.

Historical validation before that extension (2026-09-26): all four original
tests and all 134 Rust tests passed,
as did formatting and Clippy with warnings denied. Lean build and the
456-declaration axiom audit passed. Documentation checks covered 377 local
targets, six root-imported Lean modules, and 32 tables in ten changed documents.
The paper Q1–Q3 proof was reviewed separately; these test counts do not mean
it was checked by Rust or Lean.

The new source-rule cases have not been added to Lean. Its ownership projection
and targeted Kraus algebra retain their previously recorded scope.
