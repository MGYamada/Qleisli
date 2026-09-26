# Exact semantics of finite static transformations

Status: **conditional paper proofs and implementation correspondence** (2026-09-26).
This English document establishes operator equations for the mathematical
algorithms corresponding to finite circuit flattening, inversion, coherent
control, and repetition. The source contracts and typing premises are in
[static operations](static-operations.md); the surrounding compositional
semantics are in [S1–S4](source-semantics.md). No language form or API is added.

The proofs assume the verifier properties listed below. They do not establish
that every Rust execution satisfies those properties, or prove full source
soundness. Exact finite regression checks support the implementation audit;
they are not a machine-checked proof of the algorithms. Lean is unchanged.

## 1. Scope and coordinates

Consider a resolved target with exact type `Q<A> -> Q<A>` and declared effect
`Unitary`. It has no classical parameters or captured caller values. The
frontend lowers its complete body in a fresh environment, checks its result,
and independently verifies the resulting IR before flattening. The temporary
IR has exactly one quantum input, one quantum output, no classical ports,
and declared effect `Unitary`. Successful flattening additionally requires
the opcode subset in §3. Verification alone does not imply this shape or
membership in that subset.

Let `n = bits(A)`. Enumerate the input wires as axes `0,...,n-1`, and encode
`x` by `x = sum_j x_j 2^j`. An ordered local axis list `a` extracts the label

```text
extract_a(x) = sum_j bit(x,a[j]) 2^j.
```

The first component is the low-order component. In particular, the `qif`
control is axis 0 and the target label begins at axis 1. Tensor notation here
uses this explicit encoding; it does not import an array library's ordering.
For an injective axis list `a` with entries in `0,...,n-1` and length equal
to the local width of `U`, write `embed_a(U)` for applying `U` on those
ordered axes and the identity on the complementary axes. This definition
allows arbitrary entanglement with the complement.

Let `zeta = exp(i*pi/4)`. A monomial table has a permutation `p` of all local
labels and exponents `k(x)` in `Z/8Z`:

```text
M(p,k)|x> = zeta^k(x) |p(x)>.
```

Each circuit step has distinct controls, each disjoint from its action axes.
It acts by its H or monomial action when all control bits match, and by the
identity otherwise. These are exact linear operators. Equality modulo global
phase, or equality only of induced density maps, is insufficient here.

An empty action axis list still has one basis label. Its table `p=[0], k=[r]`
denotes the scalar `zeta^r`, not necessarily the identity. Likewise, `Q<Unit>`
has one owned logical port even though it has zero axes.

## 2. F1: axis transport and the flattening invariant

The mathematical flattening state consists of a token map `R` and a list of
emitted circuit steps. Initially `R(input)=[0,...,n-1]` and the list is empty.
After any processed prefix, require:

1. `dom(R)` is exactly the set of live quantum tokens of that prefix.
2. `R(t)` is the token's ordered wire list expressed in original input axes.
   The lists are individually injective and jointly partition all `n` axes.
   Empty lists belong to distinct live tokens and are not dropped.
3. If the emitted sequence is `s_1,...,s_m`, its operator
   `V = U(s_m)...U(s_1)` equals the raw prefix's effective operator on the
   fixed physical input axes. Internal clean auxiliaries are eliminated only
   by the factorization in §4. Regrouping token interfaces adds no physical
   operation.

**Axis transport lemma.** Replacing every local action index and every local
control index in a step by its image under an injective list `a` gives
`embed_a(U(step))`. For a sequence, transporting each step gives the embedding
of its product.

**Proof.** On every computational basis vector, the transported controls test
the same local bits. A monomial extracts the same ordered local label, applies
the same phase and permutation, and writes the resulting bits to the image
axes. H changes the selected image bit with the same two coefficients. All
other bits are preserved. Linearity proves the step equality, including on
superpositions. Embedding respects multiplication, giving the sequence case.
Injectivity preserves distinctness and disjointness of controls and targets.
This is the obligation implemented by `circuit::remap`; transporting only
action indices would fail for nested controlled operations.

## 3. F2: flattening and final output order

The accepted raw subset and the prefix-induction cases are:

| Raw operation | Map update and emitted operator |
| --- | --- |
| `Gate` | Replace the input token by its output on the same one axis. Emit H, X, Z, or T, with X permutation `[1,0]`, Z exponents `[0,4]`, and T exponents `[0,1]`. |
| `Cnot`, `Toffoli` | Replace the distinct one-bit tokens on the same axes. Emit X controlled by the one or two input control axes. |
| `Split` | Replace one list by its specified prefix and suffix. Emit no step; ordered tensor coordinates account for the split. |
| `Join` | Replace two distinct tokens by their concatenated lists. Emit no step. Concatenation order is preserved in `R`. |
| Equal-width `LiftBasis` | Keep the axes and replace the token. Emit the verified total injection table as a permutation with zero phases. |
| `ApplyUnitary` | Replace the token on the same axes. Transport every verified nested step through the current ordered list using F1. |
| `ComputeUseUncompute` with no work targets and only protected Z/T gates | Keep the source axes and replace its token. Emit the diagonal table proved in F3. |

For a lift, verification checks the old wires as an ordered prefix of the new
wires. Any increase has effect `Iso` and is incompatible with the temporary
program's `Unitary` declaration. Thus this case preserves width and wires;
a total injection between equally sized finite bases is a permutation.
Equal endpoint dimensions alone would not justify each intermediate case.

Raw initialization, observation, classical instructions or branches,
`QuantumIf`, and other protected-use forms are outside this flattening subset.
Some are valid independently verified IR but are rejected by flattening.
In particular, a valid raw controlled protected phase is not accepted by
this converter. No theorem here asserts acceptance of every unitary IR.

**Prefix proof.** The verifier's ownership premises ensure that each consumed
token is present, distinct inputs do not alias, and outputs are fresh. Each
row preserves the ordered partition and denotes the same physical operation
by its stated matrix, F1, or F3. Split and join only reorganize the partition.
Induction therefore establishes all three invariants in §2.

At the output, verified coverage and the single-output shape imply that its
list `a=R(output)` is a permutation of all input axes. This includes `a=[]`
when `n=0`. The function's result is expressed in this **output interface
order**, while the accumulated operator `V` still uses physical input order.
Define

```text
P_a |x> = |extract_a(x)>.
```

**Claim F2.** The complete flat operator is exactly `P_a V`. Append the
monomial permutation `p(x)=extract_a(x)` on axes `[0,...,n-1]`, with zero
phases, unless `a` is already that identity list.

**Proof.** In the physical state `|x>`, output component `j` is physical axis
`a[j]`. Its output label is precisely `extract_a(x)`. Transporting the prefix
operator to the output interface is therefore left multiplication by `P_a`.
Appending this circuit step realizes that multiplication. Both are linear,
so the equality holds for all inputs. The direction is consequential:
for `a=[1,2,0]`, input label 1 maps to 4; the inverse permutation maps 1 to 2.
A two-axis swap alone would not distinguish these orientations.

The output permutation is part of the target's operator. It must participate
in inversion, repetition, and coherent control just like the earlier gates.

## 4. F3: eliminating a restricted computed auxiliary

Let `f` be the complete, range-correct predicate table from an `n`-bit source
to an `m`-bit auxiliary. It need not be injective. The auxiliary is fresh and
starts in `|0^m>`. Define the reversible computation

```text
C_f |x,y> = |x, y xor f(x)>.
```

Assume no work targets and a use sequence consisting only of Z/T on protected
source or auxiliary bits. For each use gate `g`, put `e_g=4` for Z and `e_g=1`
for T. Define

```text
k(x) = sum_(g on source bit i) e_g bit(x,i)
     + sum_(g on auxiliary bit j) e_g bit(f(x),j)       (mod 8),
D_f |x> = zeta^k(x) |x>.
```

**Claim F3.** Compute, use, and uncompute maps
`|psi> tensor |0^m>` to `(D_f|psi>) tensor |0^m>`, including any external
reference. It therefore admits pure auxiliary release and the emitted
identity-permutation monomial has exactly the same operator.

**Proof.** On input `|x,0>`, computation gives `|x,f(x)>`. Every use is
diagonal and leaves both labels intact, multiplying by `zeta^k(x)`.
Uncomputation XORs the same `f(x)` and returns the auxiliary to zero.
For a joint vector `sum_x |x> tensor |r_x>` with arbitrary, possibly
nonorthogonal reference vectors, the output is
`sum_x zeta^k(x)|x> tensor |r_x> tensor |0^m>`. Thus the auxiliary factors as
zero for every input and reference. Linearity and mixtures extend the result
to joint density operators. This is an all-input factorization, not evidence
from an auxiliary's lifetime or one sampled state.

The frontend's narrower `with_computed` form uses one auxiliary bit and an
expanded identity/Z/T body on that auxiliary. It is a special case of this
raw subset. If the source is `Q<Unit>`, `f` has one entry and `D_f` can be a
nontrivial scalar. Flattening must keep that scalar for later control.

## 5. F4: inverse and finite repetition

For a monomial, define

```text
p_inv(p(x)) = x,
k_inv(p(x)) = -k(x) mod 8.
```

**Claim F4a.** This table denotes `M(p,k)†`. H is its own adjoint. The inverse
of a controlled step has the same controls and the inverse action; reversing
the step list and inverting each action therefore gives the adjoint of F2's
complete operator.

**Proof.** The table sends `|p(x)>` to `zeta^(-k(x))|x>`, which undoes the
original action on an orthonormal basis. A controlled step has orthogonal
blocks consisting of its action and identities. The control projectors act
on disjoint axes and remain unchanged, so taking the adjoint inverts only the
action block. Finally `(U_m...U_1)†=U_1†...U_m†`, which is the operator of the
reversed, individually inverted list. For example, `p=[1,0], k=[0,1]` needs
inverse phases `[7,0]`; merely negating phases in place would give `[0,7]`
and is wrong.

**Claim F4b.** Concatenating the complete flat list `r` times gives `U^r`
for every nonnegative finite `r`, including `U^0=I` for the empty list.
This follows by induction on `r` and sequence composition. At source level,
the input expression is still evaluated once, and all target name, type,
effect, body, independent-verification, flattening, and capacity checks still
apply at `r=0`. The identity equation does not relax the acceptance contract.

## 6. F5: coherent control of a complete target

For a separately owned control bit `c`, let `Pi_b=|b><b|` and define

```text
C_b(U) = Pi_b tensor U + Pi_(1-b) tensor I.
```

The control may be entangled with the target or a reference; it need not be
newly initialized. It is the low-order bit in our encoding, disjoint from every
target action and every pre-existing target control. Before adding this
control, transport all target indices from `j` to `j+1` by F1.

**Claim F5.** Adding `(c=b)` to every step of a target sequence, including its
final output permutation, implements `C_b(U)`. Concatenating the zero-arm
controlled sequence for `U0` and the one-arm sequence for `U1` implements

```text
Q = Pi_0 tensor U0 + Pi_1 tensor U1.
```

**Proof.** A target step cannot change `c`, so projector orthogonality gives
`C_b(T) C_b(S) = C_b(TS)`. Induction proves the sequence claim, even when the
steps have their own internal controls. The two arm operators are identities
on opposite control blocks; multiplying them yields the displayed `Q`.
Join/split around the compiled circuit supply the stated input/output tuple
interfaces and add no physical operation. No control bit is measured and no
sum of classical alternatives is substituted for this operator.

For `Q<Unit>`, taking `U0=1` and `U1=zeta` yields
`Q=diag(1,zeta)` on the control. Dropping a scalar because its density map is
the identity would incorrectly erase this observable relative phase. The
distinct logical target ownership remains required despite its empty axes.

## 7. Source correspondence and external references

Under the static target typing premises, let `U` be the exact body operator
including its return layout. F2–F5 prove the mathematical transformations
`adjoint(U)=U†`, `repeat_static(r,U)=U^r`, and the displayed `qif` block
operator, subject to F3's restricted cleanup evidence. Evaluation of input
expressions precedes these operators and contributes its own effect; a
static operation cannot erase an `Iso` or `Observe` effect in an argument.
The argument-evaluation and pending-value interfaces use S1–S4.

Every equality above extends by `I_K` to an arbitrary external reference:
tensoring preserves equality and products, with layout permutations made
explicit. Consequently the induced maps agree on arbitrary correlated
states, not only on basis states or product inputs. This also covers caller
frames whose handles are inaccessible during static target compilation.

This closes a **local mathematical transformation obligation**, conditional
on verified inputs, correct source leaf semantics, and the recorded layouts.
It is not a proof that the Rust verifier enforces every premise, that Rust
lowering realizes every inference rule, or that all source constructs are
sound. Rejection on unsupported operations or resource limits is outside the
successful-transformation theorem.

## 8. Implementation correspondence and regression evidence

| Obligation | Implementation |
| --- | --- |
| Resolve the residual-environment target, check exact signature and declared effect, independently verify its body | `static_steps` in [lower.rs](../src/frontend/compile/lower.rs) |
| Track the ordered partition and emit the final `P_a` | `flatten` in [circuit.rs](../src/frontend/compile/circuit.rs) |
| Transport action indices and existing controls | `remap` in `circuit.rs` |
| Reindex inverse phases and reverse the whole sequence | `invert` in `circuit.rs` |
| Emit `D_f` from protected source/auxiliary bits | `flatten` computed case; `computed` in `lower.rs` establishes the narrower source form |
| Repeat checked steps; shift target axes and add arm controls | `expr_inner` static cases in `lower.rs` |
| Validate tables, disjoint indices, widths, effects, and complete ownership | `check_circuit`, computed checks, and `verify` in [verify.rs](../src/verify.rs) |

[tests/static_semantics.rs](../tests/static_semantics.rs) compares every matrix
column of selected compiled circuits with independent analytic formulas in
the exact ring `Z[zeta,1/2]`, using four integer coefficients with `zeta^4=-1`.
It checks phases as amplitudes; no probability comparison, floating-point
tolerance, compiler inverse routine, or round-trip identity is used as the
oracle. These are finite examples, not exhaustive compiler validation.
The existing [static-operation tests](../tests/static_operations.rs) retain
source rejection, malformed IR, capacity, algorithm, and numerical cases.

| Exact regression | Independent expected operator |
| --- | --- |
| `adjoint_and_nested_axis_remapping_match_all_exact_matrix_entries` | Analytic H/T/X/CNOT amplitudes, their conjugate transpose, and an embedding on nonadjacent axes followed by output order `[1,2,0]`. |
| `finite_repetition_preserves_the_phase_of_a_noncommuting_operator` | For `V=TX`, `V^(2r)=zeta^r I` and `V^(2r+1)=zeta^r V`; counts 0, 1, 2, 3, 8. |
| `nested_qif_preserves_zero_one_controls_and_branch_phases` | Four blocks selected by two controls: `TX`, `(TX)†`, Z, T. |
| `computed_scalar_phase_is_retained_on_unit_and_under_adjoint_and_control` | Scalar `zeta^7`, its adjoint `zeta`, and zero-controlled `diag(zeta^7,1)`. |

These four operator tests cover 12 compiled circuits, 38 input basis columns,
and 186 exact complex matrix entries on zero to three axes. A fifth test checks
the scalar helper's normalization, cancellation, all 64 eighth-root products,
and the Hadamard coefficient identity. Integer arithmetic checks overflow;
the test helper is not a new execution backend or an arbitrary-size verifier.

Local validation on 2026-09-26: all five new tests and all 124 Rust tests passed;
formatting and Clippy with warnings denied passed. Documentation validation
checked 319 local link targets, the static contract's six legacy anchors, and
the changed documents' tables. These checks do not machine-check F1–F5.

The [type/effect/name supplement](source-typing-rules.md) now presents all
syntax cases. Remaining work includes its source/Rust adequacy, correspondence
of all semantic leaves and Rust data structures, and assembly of the local
results into the full source-to-IR theorem. See the
[roadmap](../ROADMAP.md) and [conformance ledger](specification-status.md).
