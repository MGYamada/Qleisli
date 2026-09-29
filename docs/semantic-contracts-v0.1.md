# Finite semantic contracts for v0.1

Status: **bounded specification and compiler/checker path implemented**
(2026-09-27). This
English document specifies the first finite evidence boundary for the adopted
[v0.1 minimum](release-milestones.md#v01-minimum-semantic-contracts). The release
audit combines this kernel with the function boundary and regression evidence.
The Rust checker is not formally verified, and general source/compiler
correctness remains open. Implementation and regression results belong in
the [conformance ledger](specification-status.md).

The [proposal review](semantic-contract-proposal-review.md) gives the motivation
and counterexamples. The present document fixes a bounded exact fragment and
its rule obligations. Existing source v0 remains the baseline; the implemented
three-argument computed form below extends the two-argument form without
changing that form's structural acceptance rule.

## 1. Contract and interpretation

**SC-1 — Fixed meaning.** A contract fixes finite logical spaces `L_in,L_out`,
physical interface spaces `P_in,P_out`, and exact operators

```text
u     : L_in -> L_out,
E_in  : L_in -> P_in,       E_in† E_in = I_L_in,
E_out : L_out -> P_out,     E_out† E_out = I_L_out.
```

An implementation `U:P_in->P_out` satisfies the contract exactly when

```text
U E_in = E_out u.
```

The public logical operation `u` is an input to checking. It is not redefined
as `E_out† U E_in` after seeing the implementation. All matrix entries include
scalar phase; equality up to a global phase is insufficient. The initial
circuit evidence profile represents square unitary U on one fixed physical
basis type. Both encodings and u may be rectangular isometries, with
`u†u=I_L_in`; square u is unitary. Different logical input/output types are
allowed when their dimensions and the stated maps match. Adjoint evidence
separately requires square u. General pure isometric physical implementations,
observation instruments, approximate relations, and block-encoding contracts
require separate extensions.

**SC-2 — Interface identity.** Logical coordinates and physical axis order
are part of the contract. Exact dimensions alone do not identify interfaces:
`E` and `E v` may have the same image and different logical meanings. Tensor
order follows the source/IR convention: the left component occupies the low
bits, `index(a,b)=index(a)+2^bits(A) index(b)`. An explicit checked permutation
is required to change coordinates.

Operator-level evidence describes ordered axes. A source contract additionally
requires exact source type trees, ordered quantum holders, effect, and the
[source/IR boundary relation](source-ir-correspondence.md). A bit width is not
a source type or an ownership proof. In particular, `Q<Unit>` remains a linear
holder even though its Hilbert space has dimension one. All ordinary source
and raw-IR ownership checks remain mandatory.

**SC-3 — Entry evidence.** The equation constrains U on `image(E_in)`. Applying
the contract requires a checked preparation, a previous contract with exactly
that output encoding, or a scoped construction that establishes the encoding.
Owning the physical wires does not establish this premise. The first source
form establishes its entry encoding by construction; it does not expose a
public assertion that an arbitrary register is encoded.

For every external reference R, tensoring the equation gives

```text
(U tensor I_R) (E_in tensor I_R)
  = (E_out tensor I_R) (u tensor I_R).
```

Consequently the contract holds for arbitrary logical/reference pure states
and, by linearity of the induced density operator maps, mixed states. Neither
the contract nor disjoint ownership assumes a product input.

## 2. Exact finite checker and trust boundary

**SC-4 — Independent validation.** The evidence checker consumes untrusted
circuits, contracts, and evidence descriptions. It checks circuit well-formedness
through the ordinary independent IR verifier, validates every encoding and
logical operator, and derives a checked result only after all premises pass.
The implementation circuit and its ordered interface are fixed inputs. A
proof for a different circuit, a different predicate, or a changed contract
cannot be used merely because its name is unchanged.

The first exact arithmetic domain is the ring
`Z[zeta_8,1/2] = Z[1/2,sqrt(2),i]` inside the eighth cyclotomic field, where
`zeta_8=exp(i*pi/4)` and `zeta_8^4=-1`. H and the existing eighth-turn phases
are exactly representable. Scalars have canonical dyadic coefficients in the
basis `1,sqrt(2),i,i sqrt(2)`, with signed 128-bit numerators and nonzero
denominator exponents at most 126. Compare normalized coefficients exactly.
Arbitrary rational or algebraic entries outside this ring are unsupported.
No floating-point tolerance authorizes a certificate or auxiliary release.
Integer overflow, dimension exhaustion, and evidence budget exhaustion must
produce a diagnostic rather than a positive result. Intermediate arithmetic
may exhaust capacity even if an alternative evaluation order would fit.

The [coefficient-domain design note](coefficient-domains.md) records a future
type-parameterization recommendation and separates exact, approximation and
device contracts. It does not generalize this concrete R8 checker or its public
types, admit arbitrary angles or introduce an approximate acceptance tolerance.
The current ring, capacities and pure-cleanup requirements remain normative.

The initial dense-matrix profile is bounded at **six physical or logical bits** per
checked circuit, including controls and temporary computed auxiliaries, and
**1,024 steps** per flat circuit. This
is a checker capacity limit, not a bound on the mathematical rule or on the
existing language's other implementation profiles. Exact matrices have at
most 64 rows and 64 columns. Contract basis trees have at most 128 nodes and
depth 32, with the root at depth zero; these are distinct from the frontend's
source-type limits. Raw certified-compute checking uses a shared budget of
**10,000,000 charged exact scalar operations** across one raw program,
including both circuit interpretations, isometry checks, and each equation.
Each region is additionally capped at that default. Its
conservative charges can exhaust the work limit before another size limit is
reached. The public Rust API takes a caller-supplied `Budget` for exact work;
the raw-IR boundary always supplies the fixed default budget.

The Rust interface separates raw descriptions from checked evidence:

| Object or operation | Obligation |
| --- | --- |
| `BasisType` (`Unit`, `Bit`, `Pair`, `Tuple`) | Preserve the finite type tree in addition to its width. Since 0.2.0, `Tuple` has at least three immediate fields; two-field nodes remain `Pair`, with no reassociation. |
| `Circuit` | Bind a basis type and ordered finite circuit steps; validate the actual steps. |
| `Encoding` | Bind logical and physical basis types and an exact rectangular matrix; check isometry. |
| `Contract` | Fix input/output encodings and an exact logical operator independently of the implementation. |
| `CheckedContract` | Hold the bound circuit and contract behind private fields; only successful checking/rule constructors can create it. |
| `CheckedContract::check` | Establish SC-EQ for a supplied circuit and contract. |
| `CheckedContract::identity` | Establish the identity primitive on one checked encoding without dense circuit evaluation. |
| `then`, `tensor`, `adjoint`, `controlled` | Apply the corresponding rules to checked premises and construct the actual transformed circuit. |
| `check_binding` | Require exact structural equality to the supplied circuit and complete contract. |
| `check_entry` | Compare a supplied `Option<&Encoding>` against the contract's exact input encoding and return its output encoding only on equality. |

These are the roles of the initial [Rust API](../src/contract/mod.rs), not
`.qli` source types or a serialized proof format. A finite chain of opaque checked
constructors supplies compositional evidence; the first version does not
accept a user-authored proof graph or proof-language syntax. Construction
uses a caller-provided finite checking budget for exact work, and checked
results remain immutable. `check_binding` compares a complete structural
snapshot, including the identities of checked function dependencies; it does
not assert merely semantic equivalence of a replacement.
Certify a changed implementation separately before substitution.

The [0.2.0 type correction](tuple-shapes.md) retains n-ary shape in contracts
and external requests; equality compares that structure even when matrices and
widths coincide. Zero-, one- and two-field `Tuple` nodes reject as noncanonical.
Existing node/depth/bit bounds and exact equations apply unchanged. Binary
tensor/control constructors keep their specified output trees. This extension
has regression evidence, not a new Lean theorem about all source types.

`check_entry` checks compatibility between theorem interfaces only. A caller
can construct an `Encoding` describing a subspace without holding any state
in that subspace. This API is neither a state-indexed encoded handle nor proof
that an actual runtime state meets the entry premise. The initial source
extension establishes entry by allocating and computing a fresh auxiliary;
general encoded-state introduction/elimination rules remain future work.

Evidence search is outside the trusted checking boundary. A human, compiler,
AI, or simplifier may propose a derivation. Its source gives it no authority.
Checked handles must not offer an unchecked public constructor. They bind the
conclusion and the full circuit/interface they certify. Binding can use an
immutable structural snapshot; a human-readable name or an unchecked digest
is not sufficient. Raw serialized or public-field evidence remains untrusted
and is checked again at the final IR boundary.

The trusted implementation consists of the exact arithmetic and matrix
operations, the circuit interpreter used by leaves, the rule checker, the
IR verifier, and the connection from the source and actual IR interfaces.
Paper derivations below justify the mathematical rules. Finite Rust tests do
not prove that these implementations realize those rules on every input.

## 3. Evidence rules and paper soundness

Write `C(U;E_in,E_out;u)` for the exact equation with all SC-1–SC-4 premises.
Every successful rule also preserves the separately checked interface,
physical unitarity, logical isometry, capacity, and ownership requirements.
These are specifications of
rule behavior; concrete Rust constructor names are implementation details.

**SC-EQ — Exact leaf.** Independently interpret the actual validated circuit
as U, check `E_in†E_in=I`, `E_out†E_out=I`, and `u†u=I`,
then compute and compare `U E_in` and `E_out u` exactly. This proves the
equation for every input by equality of all matrix entries. Comparing only
measurement probabilities, a selected sample of columns, or the compressed
block `E_out† U E_in` without leakage checks is not this rule. The sealed
primitive circuit interpretations are leaves of the same exact semantics.
The separate identity constructor uses `I E=E I` directly on an already
checked isometric encoding, with an empty validated physical circuit.

**SC-SEQ — Sequential composition.** From

```text
C(U1;E0,E1;u1),     C(U2;E1,E2;u2)
```

derive `C(U2 U1;E0,E2;u2 u1)`. The intermediate encodings, including
coordinates, layout, and logical type/interface, must match exactly.
Associativity and substitution give
`U2 U1 E0 = U2 E1 u1 = E2 u2 u1`. Checked component evidence may be reused;
the rule need not re-enumerate the composite circuit's dense operator merely
to establish this algebraic step. The emitted composite circuit must still
be checked to be the specified composition of those components.

**SC-TENSOR — Parallel composition.** From
`C(U1;E1_in,E1_out;u1)` and `C(U2;E2_in,E2_out;u2)`, derive the tensor product
contract on disjoint owned interfaces, using explicit tensor order. The
mixed-product identity gives

```text
(U1 tensor U2) (E1_in tensor E2_in)
  = (E1_out tensor E2_out) (u1 tensor u2).
```

This is equality on the whole tensor space, including entangled inputs.
Disjoint axis placement is a separate construction/validation premise.

**SC-ADJOINT — Qualified inverse.** Require both U and u to be unitary.
From `U E_in=E_out u`, derive
`U† E_out=E_in u†` by multiplying on the left by `U†` and on the right by
`u†`. Swap the input/output encodings and interfaces. An arbitrary logical
isometry cannot use this rule, and the adjoint of a physical preparation is
not a generally valid pure operation. The circuit transformation must reverse
the actual steps and preserve exact inverse phase.

**SC-CONTROL — Same-encoding coherent control.** Require unitary U and u
with a single exact encoding `E_in=E_out=E`. Add one distinct control axis.
For `C(U)=|0><0| tensor I + |1><1| tensor U`, in the declared axis order,

```text
C(U) (I_Bit tensor E) = (I_Bit tensor E) C(u).
```

The zero branch follows from identity; the one branch follows from the
premise. If input and output encodings differ, the zero branch need not
match, so the first rule rejects that case. A contract about U does not
provide controlled access to an unknown external operation. This rule uses
the available finite circuit description and a checked controlled circuit
transformation.

**SC-REUSE — Checked dependency.** A checked result may be a premise of
another rule only with its bound circuit, contract and interface. If an
implementation changes, certify the replacement against the same fixed
logical contract before substituting it. Reusing a proof object is different
from trusting a function name or suppressing final IR validation.

**Paper theorem.** Induction over any finite acyclic evidence derivation
constructed by these rules establishes its conclusion equation. SC-EQ is
matrix equality; SC-SEQ and SC-TENSOR use the identities above; SC-ADJOINT
and SC-CONTROL use their additional premises; SC-REUSE supplies an already
established conclusion. Tensoring the theorem with an arbitrary identity
gives reference stability. This theorem is about the specified rules, not a
mechanized proof of the Rust checker or a completeness/efficiency theorem for
finding evidence.

## 4. Computed-relation source form

**SC-SOURCE — Classification and syntax.** The new three-argument
`with_computed` is a **language form**, not an ordinary `.qli` definition or
a newly imported standard-library function. The intended grammar is

```ebnf
WithComputedContract ::= "with_computed" "(" Expr "," Name "," Name ")"
                         "{" "|" Ident "," Ident "|" Stmt* Expr "}"
```

In `with_computed(q,f,u) { |d,a| body }`, q is evaluated once. The predicate
f and logical operation u are statically resolved declaration names, not
runtime operation values. Use the existing static-name hiding rule after
evaluating q. Both names participate in nonrecursive dependency checking.
The two binder names must be distinct.

For an exact finite basis type A, require:

| Item | Contract |
| --- | --- |
| q | One owned `Q<A>`, consumed once by the form. |
| f | A total basis function with packed domain exactly A and result `Bit`. Multiple parameters use the existing left-associated packing convention; zero parameters have domain `Unit`. |
| u | A declared `unitary fn` with exactly one parameter `Q<A>` and result `Q<A>`, with no classical parameters, or an appropriate sealed single-bit unitary name. Its compiled meaning is fixed before checking the body relation. |
| d | Private owned `Q<A>` replacing q inside the body. |
| a | Private owned `Q<Bit>` for the computed auxiliary. |
| body | Effect `Unitary`; final value exactly `(Q<A>,Q<Bit>)` in data/auxiliary order, with every private quantum resource accounted for. |
| Whole form | Returns `Q<A>`; effect `Unitary` joined with the effect of evaluating q. |

The body receives d and a as one controlled ownership boundary. All other
outer bindings are unavailable inside the isolated body. Outer quantum owners
remain in the surrounding frame. The body cannot use
q again, capture another quantum value, copy either private resource, hide
a live private resource, or discard an auxiliary implicitly. Unlike the
legacy computed scope, this initial extension captures no outer classical
values either. Closed classical expressions and branches are allowed when
the static extraction profile can evaluate them. Outer names remain
unavailable placeholders so that isolating the body does not silently make a
shadowed function callable. The binders may have the spelling of masked outer
owners without consuming those owners. Only operations supported by the
finite static circuit extraction profile can occur in the certified body.
A type-correct unitary body outside that profile receives an
unsupported/capacity diagnostic, not an invented proof.

At most five data bits plus one auxiliary fit the six-bit profile. Both the
body and the logical circuit obey the 1,024-step circuit limit. The body may
split and rejoin data and may change data and auxiliary values.
Its output type tree must match exactly, and its output axes are transported
into the specified data/auxiliary order before interpreting W. The checker
must not infer identity transport merely from equal dimensions or an equal
set of wires. `Q<Unit>` data must still be returned explicitly.

**SC-COMPUTED — Semantic premise.** Let

```text
E0 |x> = |x,0>,
Cf |x,a> = |x,a xor f(x)>,
Ef = Cf E0,                  Ef |x> = |x,f(x)>.
```

Since f is total and its input is retained, Cf is a permutation and Ef is
isometric even when f is noninjective. For the body's actual ordered circuit
W, require the exact certificate `W Ef=Ef u`. Then

```text
Cf† W Cf E0 = Cf† W Ef = Cf† Ef u = E0 u.
```

This proves the logical operation u and exact zero/separation of the
auxiliary together, for every input and external reference. The scoped
construction supplies entry evidence; no unrelated caller-supplied encoded
state is assumed. A failed equality rejects the form even if ownership,
effect, and circuit unitarity checks pass.

### Source examples

The following are acceptance/rejection examples for the new form;
their current validation results must be read from the conformance ledger.
Assume the usual imports of `x`, `z`, and `h` from `std::quantum`.

```qli
basis fn copy_label(b: Bit) -> Bit { b }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
unitary fn logical_x(q: Q<Bit>) -> Q<Bit> { x(q) }
unitary fn logical_z(q: Q<Bit>) -> Q<Bit> { z(q) }

unitary fn phase(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, copy_label, logical_z) { |d,a| (d,z(a)) }
}

unitary fn identity_with_work(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, copy_label, identity) { |d,a| (d,h(h(a))) }
}

unitary fn flip_together(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, copy_label, logical_x) { |d,a| (x(d),x(a)) }
}
```

These use one rule: respectively `Z_aux Ef=Ef Z`, `H_aux H_aux Ef=Ef I`,
and `(X_data tensor X_aux) Ef=Ef X`. The tensor notation names axes; the
implementation uses the declared low-bit ordering.

The complete [semantic-contract example](../examples/semantic_contracts/main.qli)
provides imports, independently written logical definitions, and a closed
entry point for these three cases. Its [usage note](../examples/semantic_contracts/README.md)
records how to check and run it; this finite example is not completion of
the release criteria.

| Fragment or alteration | Required rejection reason |
| --- | --- |
| `(d,x(a))` with logical `identity` | Leaves the auxiliary at one after uncomputation; fails the relation. |
| `(d,z(a))` with logical `identity` and `copy_label` | Correct cleanup but wrong public logical phase. |
| `(x(d),a)` with logical `logical_x` and `copy_label` | Does not preserve the computed relation. |
| `(d,a)` with logical `logical_z` | Valid physical identity, wrong logical operation. |
| Returning only d, or binding a to `_` | Missing linear ownership, regardless of matrix dimensions. |
| Returning `(a,d)` when shapes differ | Output type/interface mismatch. Equal shapes still require checking the actual returned axis order and relation. |
| Reading outer q or another outer quantum variable | The outer quantum frame is inaccessible. |
| Measurement, reset, or arbitrary discard in the body | Wrong effect and outside the unitary circuit profile. |
| A nonunitary declaration used as u, even with a unitary expanded body | The declared static-operation contract does not qualify. |
| A changed predicate or implementation paired with old evidence | Circuit/contract binding mismatch or failed exact checking. |

## 5. IR connection and static transformations

**SC-IR — Actual implementation binding.** The new raw instruction is
`RawOp::CertifiedCompute`. It records `source`, `source_out`, exactly one
fresh `ancilla_wires` entry, the total predicate `function` table, the actual
ordered body `use_steps`, and fixed `logical_steps`. The physical body axes
are the source axes in order followed by the auxiliary as the high bit.
Source checking validates exact type trees before lowering to width-based IR.
The final raw-IR verifier checks this complete
relation independently of the frontend. Merely attaching a Boolean saying
that the frontend accepted the body is insufficient. The ownership transition
consumes the source holder and returns its logical result exactly once; the
auxiliary is private to the checked region and cannot escape.

The raw verifier checks source ownership and a fresh output token, reserves
the private auxiliary wire globally, validates both finite circuits, constructs
Ef from the complete predicate table, and checks `W Ef=Ef u` exactly. These
public raw fields are a submitted claim, not a previously trusted proof.
Changing a raw field requires independent validation of the new claim.

The reference interpreter executes retained W inside compute/use/uncompute.
It removes the auxiliary only under the independently established exact
cleanup relation. Numerical reference simulation does not supply that proof
and does not define an approximate acceptance tolerance for it. Static
flattening may replace the whole checked scope by `logical_steps`; the
replacement is justified by SC-COMPUTED. Retaining the physical circuit in
the raw region makes its implementation correspondence inspectable.

The [function-contract form](function-contracts-v0.1.md)
`apply_contract(implementation,specification,input)` fixes a public logical
specification at the client boundary. Its immutable `FunctionEvidence` retains
both checked raw functions and their exact source snapshot. A final
`CircuitAction::Contract` refers to that evidence under ordered axis mapping,
control predicates, and an adjoint flag. It survives static transformations;
the independent checker interprets its already checked exact meaning, and
the simulator executes its checked circuit lowering. This permits private
computed regions to be replaced by their proved logical action while keeping
the original raw implementation available for inspection.

The exact logical circuit is a valid replacement for the entire clean scope
only after SC-COMPUTED succeeds. Its derivation is the equation in Section 4.
Inverse, coherent control, and repetition of the returned logical operation
must retain exact phase and satisfy their usual interface/capability premises.
Transformations either construct evidence using the rules above or recheck the
result; an old evidence object is not accepted for a different final circuit.

There is no standalone pure `release0`, no permission to release an arbitrary
owned auxiliary, and no observation hidden inside this form. The existing
two-argument `with_computed(q,f) { |a| body }` continues to use its Z/T-chain
certificate. General work registers, a user-written proof language, sized
interfaces, operation parameters, and arbitrary encoding assertions remain
outside this initial source extension.

## 6. Acceptance evidence and remaining obligations

Completion requires both positive and negative checks through the implemented
source-to-IR path. At minimum, cover the three Section 4 equations, phase
oracles on an asymmetric multibit predicate, and two implementations of the
same logical contract used by an unchanged client. Include coherent control,
an entangled external reference, output permutations, zero-width holders,
stale evidence, wrong encodings, and auxiliary-only X. Record which cases use
exact checking and which use numerical reference execution.

The finite kernel must also test sequential and tensor evidence, rejection of
mismatched middle encodings, qualified adjoints, control with unequal
encodings, malformed circuits, invalid isometries, and deterministic exhaustion
of dimensions, type trees, circuit size, and arithmetic/work budgets.
There is no untrusted proof-DAG reader in this initial API. Each returned
error must leave no
checked certificate behind.

The checker, source path, and [function boundary](function-contracts-v0.1.md)
are implemented and tested as recorded in the
[conformance ledger](specification-status.md). The release table records the
joint V01-C1–C6 audit; no single example establishes that entire milestone.
The source/Rust adequacy, compiler meaning preservation, arithmetic kernel
implementation correctness, and final IR checker correctness remain explicit
proof obligations. Exact cleanup must remain separate from any future
approximate logical contract: small nonzero auxiliary leakage never permits
pure release. Observation needs an instrument contract including outcome and
residual-system semantics, and general block compression is not exact
leakage-free intertwining.
