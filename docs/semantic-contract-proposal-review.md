# Review: compositional semantic contracts through isometric encodings

Status: **mathematical proposal reviewed; subsequently adopted as the v0.1
minimum on 2026-09-27; a first bounded integration is now implemented**.
This note evaluates `U E_in = E_out u`, its proof obligations, and its fit
with Qleisli. The adopted release requirements and work order are recorded
in [release milestones](release-milestones.md). Adoption does not by itself
extend the current v0 syntax, acceptance rules, or public standard library.
The implementation baseline and experiments below record the initial review;
the subsequent [SC specification and implementation](semantic-contracts-v0.1.md)
adds a three-argument source form and exact checker. Full public function
contract reuse and release acceptance remain incomplete.
Here “implementation” means an ideal circuit/IR operator, not a guarantee
about noisy physical hardware.

## 1. Assessment and exact contract

The equation is a sound and useful core for **exact pure implementation
contracts on encoded subspaces**. It connects logical meaning, implementation
substitution, and safe auxiliary cleanup without identifying ownership with
separability. Its algebraic form is familiar; the engineering contribution
would be a checked path from reusable contracts to the actual Qleisli IR.

Specify all four finite-dimensional spaces and all maps:

```text
E_in : L_in -> P_in,       E_out : L_out -> P_out,
E_in† E_in = I,            E_out† E_out = I,
u : L_in -> L_out,         U : P_in -> P_out,
U† U = I,                 U E_in = E_out u.
```

The equation implies `u†u=I`, since the Gram matrix of both sides equals
`I`. Equal logical input/output dimensions then imply that `u` is unitary.
The implementation's global validity and the encoded-subspace relation are
separate checks. Neither a declared `unitary` label nor a submitted proof
name should bypass independent checking of the actual implementation.

The logical operation and encoding must be fixed by the public specification.
Defining a new `u=E_out† U E_in` after seeing an implementation does not prove
that implementation meets the user's intended contract.

## 2. Computation, use, and uncomputation

Let `E_0|x>=|x,0>` and let a reversible XOR computation satisfy
`C_f|x,a>=|x,a xor f(x)>`. Then `E_f=C_f E_0` is an isometry for **any total
basis function** `f`; injectivity of `f` is unnecessary because `x` is retained.
If `W E_f=E_f u`, then

```text
C_f† W C_f E_0 = C_f† W E_f = C_f† E_f u = E_0 u.
```

This proves both the intended logical action and an exactly separated zero
auxiliary. Tensoring with an arbitrary reference identity preserves the
equation, so no product-state assumption about the data or reference is used.
Mixed inputs follow by linearity on density operators.

For `f(x)=x`, applying X to both data and auxiliary maps `|x,x>` to
`|not x,not x>`, hence `(X tensor X) E_f=E_f X`. Uncomputation returns
`|not x,0>`. Applying X only to the auxiliary instead returns `|x,1>` and
cannot receive the zero-cleanup certificate. H followed by H on the auxiliary
has the identity operator and therefore satisfies the contract, although
v0 deliberately rejects that body under its structural Z/T-only rule.

A broader useful family is explicit. For a permutation `g` and phases `d_x`,
if a valid unitary `W` satisfies

```text
W |x,f(x)> = d_x |g(x),f(g(x))>,      |d_x| = 1,
```

then its logical operation is `u|x>=d_x|g(x)>`. This preserves the computed
relation while allowing the data to change. The contract must still identify
the actual circuit implementing W, not just postulate its action.

## 3. Composition rules and their premises

| Rule | Valid statement and required boundary |
| --- | --- |
| Sequential | `U1 E0=E1 u1` and `U2 E1=E2 u2` imply `U2 U1 E0=E2 u2 u1`. The middle encoding, logical coordinates, physical layout, and owned resources must match. Equal dimensions or equal image subspaces alone are insufficient. |
| Tensor | Two equations imply the tensor equation on disjoint resources, with explicit tensor order/layout. This equality holds on entangled logical inputs too. |
| External reference | Tensor every map with `I_R`; arbitrary correlations with R are preserved. |
| Adjoint | If U and u are unitary, `U† E_out=E_in u†`. If U is only isometric and u unitary, the equation still follows algebraically, but U† is not necessarily a valid operation on all of P_out. A non-surjective logical isometry does not in general admit the reversed contract. |
| Coherent control | For fixed E and unitary U,u, `controlled(U) (I tensor E)=(I tensor E) controlled(u)`. If input/output encodings differ, the identity arm generally fails this equation. A separately certified encoding-conversion arm is needed. |
| Repetition | Repeat an endomorphism contract with the same encoding and interface. Zero repetitions still require a well-formed target/interface. |

These are algebraic derivations, not a claim that an unknown physical device
offers inverse or controlled access. Exact scalar phases must remain in the
contract: `I` and `-I` induce the same ordinary density map, but their
controlled versions differ by Z on the control. Equality of a preserved
subspace also does not identify its internal logical action.

## 4. Essential boundaries of the proposal

**Entry evidence.** A contract constrains U only on `image(E_in)`. The caller
must establish that its state, including any reference correlation, is
encoded there. For example U may act correctly when a work bit is zero and
incorrectly when it is one. Plain `Q<A>` ownership proves neither fact.
A checked preparation or an opaque aggregate carrying encoding evidence is
needed. The data and computed auxiliary must form one controlled ownership
interface; exposing an auxiliary handle must not create aliases to outer data.

**Encoding identity.** `E` and `E v` for a logical unitary v have the same
image, but use different logical coordinates. Replacing one silently changes
the represented logical operation. Encode the map, phase, bit order, exact
type tree, and interface in the contract identity, or check an explicit
conversion between them.

**Approximation.** Keep exact cleanup and approximate logical meaning as
separate obligations, for example

```text
U E_0 = E_0 v,             ||v-u||_op <= epsilon.
```

The first equation allows pure cleanup; the second states accuracy. A bound
`||U E_0-E_0 u|| <= epsilon` alone permits nonzero auxiliary leakage, however
small. Returning that auxiliary or discarding it with an explicit channel
contract are different operations. Operator-norm errors for unitary logical
steps compose additively by the usual telescoping bound; their norms and
phase conventions must be recorded explicitly.

**Block encoding.** General block encoding has the weaker condition
`E_out† U E_in=A/alpha`, possibly approximately, and can retain amplitude
outside the output code. It is not an instance of exact leakage-free
intertwining for a non-isometric `A/alpha`. H with `E=|0>` already has
`E† H E=1/sqrt(2)` and a nonzero `|1>` component. Under the additional
assumptions that U, the embeddings, and the compressed logical map are all
isometric, the exact compression equality does imply zero leakage: the
orthogonal leakage term has squared norm `I-u†u=0`. Do not apply that argument
to a general contraction. See the primary
[block-encoding definition, §4.1](https://arxiv.org/pdf/1806.01838).

**Observation.** A future measurement contract must compare complete
instruments, including classical outcome decoding and the conditional
residual system. Matching outcome probabilities alone is insufficient.
The pure equation is a good first fragment, not a single formula already
covering observation, postselection, or general block encodings.

## 5. Fit with the current implementation

The [source-to-IR correspondence](source-ir-correspondence.md#1-boundary-relation-and-the-preservation-statement)
already uses `V_IR J_in=J_out V_source`. Its J maps are coordinate
isomorphisms over the complete live interface; the proposed E maps generalize
this shape to proper encoded subspaces. Existing BC ownership, exact types,
SSA decoding, layouts, and issued-ID obligations remain necessary.

The [public contract ledger](stdlib-contracts.md) currently records meanings
in documentation and finite regressions. It explicitly does not provide a
machine-readable general certificate schema. The
[raw verifier](../src/verify.rs) checks IR validity, not equality to an
independently specified arbitrary logical operator.

In [`computed`](../src/frontend/compile/lower/mod.rs), the frontend verifies
an entire linked auxiliary Z/T chain and replaces it with
`ComputeUseUncompute`. Raw [`verify_compute`](../src/verify.rs) enforces its
own protected-operation restrictions. Static
[`flatten`](../src/frontend/compile/circuit.rs) also relies on that restricted
meaning. A checked rewrite such as H;H to identity can still emit the existing
IR, provided independent evidence connects the complete original body to the
rewrite. Retaining general W as an actual compute/use/uncompute implementation
requires an evidence boundary covering that circuit, ownership/output
interfaces, cleanup and static transforms, for example a new certified IR
region. Merely loosening the frontend's gate whitelist is unsound. A new raw
instruction is a design choice, not a mathematical requirement if a separate
checked translation can already produce supported IR.

Current ideal-operator soundness has paper proofs under stated verification
premises. General correctness of the Rust checker/compiler remains open.
The proposal should say it **uses the existing validation boundary**, not
that the implementation's global soundness is already machine proved.

## 6. A small proof checker and a useful first milestone

A suitable initial certificate is a finite acyclic derivation with typed
endpoints, primitive equalities, sequential/tensor composition, qualified
inverse/control rules, and bounded exact matrix comparison. Its theorem is:
successful checking against the specified circuit and contract implies the
operator equation. Proof search can fail without weakening this theorem.

The verifier must independently validate encodings, interfaces and premises,
bind each certificate to the actual circuit/IR and contract version, reject
cycles or stale/mismatched dependencies, and retain ordinary resource/effect
checks. Reuse of a checked proof can avoid repeated dense simulation; it
does not guarantee that all equivalences have small proofs. Bound the proof
size, matrix dimensions, and arithmetic cost and report exhausted capacity
without issuing a certificate.

In particular, matrix dimensions cannot detect a lost `Q<Unit>` ownership
token. The existing linear interface checks remain necessary even for an
exact operator equality. An encoding certificate is not permission to bypass
the ownership discipline or infer separability of other owned registers.

For the current H/T gate family, exact arithmetic in a cyclotomic domain is
appropriate. [Existing static tests](../tests/static_semantics.rs) already
use `Z[zeta_8,1/2]`, but their test helper is not a production proof kernel.
Floating-point agreement is not an equality certificate, especially when
it authorizes pure cleanup or coherent control.

The strongest small acceptance milestone is one fixed phase-oracle contract
`O_f|x>=(-1)^f(x)|x>` and two different implementations: a certified
compute/Z/uncompute circuit and a direct phase implementation. An unchanged
client should accept either, including under coherent control and with an
entangled reference. Check the final IR and all output axes, not just an
intermediate source name. Reject a phase-shifted replacement, changed
predicate, wrong encoding/layout, mismatched proof, and nonzero auxiliary
leakage. Then add identity via H;H and simultaneous data/auxiliary X as
separate demonstrations of the same rules.

A useful concrete predicate is `f(a,b)=a and not b`. With the first component
in the low bit, its logical matrix is `diag(1,-1,1,1)`. Its asymmetry exposes
swapped-axis mistakes. For a zero auxiliary in the third bit, compare all
four input columns and eight physical output entries exactly, including the
zero rows outside the clean output subspace. A second implementation may
have a different physical width; each uses its own checked encoding/wrapper
to expose the same logical client interface.

This milestone can define a limited experimental fragment while the source
adequacy work continues. General-size signatures, operation parameters,
error budgets, and access capabilities should follow that concrete result.

## 7. Relation to primary research

- [Singhal and Reppy, QHTT (2021)](https://arxiv.org/pdf/2109.02198), and
  [Singhal's expanded report (2020)](https://arxiv.org/pdf/2012.02154), put
  pre/postconditions into quantum computation types. The expanded report
  uses ghost variables to reason about external correlations. The proposal
  makes an explicit encoding/operator equality central; this is a choice of
  contract, not evidence that QHTT cannot express related properties.
- [Chareton et al., Qbricks (2020 preprint; ESOP 2021)](https://arxiv.org/pdf/2003.05841)
  separates circuit-building code from deductive specifications and uses
  symbolic path sums. Its §5.5 ancilla constructor requires zero return,
  and §6.2 includes equations for circuit application. Contract-based
  verification and evidence for auxiliary cleanup therefore have direct
  precedents. This review does not claim a new general principle or a
  stronger expressiveness result.
- [Hietala et al., SQIR/VOQC (2021)](https://arxiv.org/pdf/1912.02250), §4.1,
  distinguishes exact equality from equality up to global phase, and §4.6
  verifies layout transformations through qubit mappings. Qleisli's intended
  contribution would be maintaining exact phase and representation evidence
  through its particular source, ownership, and IR interfaces.
- [Araújo et al. (2014)](https://arxiv.org/pdf/1309.7976) prove an obstruction
  to universally adding control to a single use of an unknown unitary in
  the ordinary circuit model. They also discuss extra physical access, such
  as a known bypass giving `I direct-sum U`, which changes that model. The
  proposal's separate controlled-access capability is therefore appropriate;
  a semantic equality certificate alone does not supply that capability.

The defensible research target is an implemented and validated combination
of these ideas: exchangeable logical contracts, phase-sensitive encodings,
linear ownership, exact auxiliary cleanup, and evidence checked against
final IR. This is a contribution to demonstrate, not an established novelty
claim from the present literature check.

## 8. Evidence collected for this review

The standalone [exact examples](../scripts/check_semantic_contract_examples.py)
use Python's standard `Fraction` and explicit arithmetic in `Q(sqrt(2))`.
All **39 checks passed**, with no floating-point tolerance. They cover the
phase oracle, H;H, simultaneous X, reference/tensor and control identities,
and counterexamples for auxiliary-only X, unqualified adjoints, mismatched
encodings, missing entry evidence, phase erasure, block compression, and
approximate cleanup. These are fixed finite matrices, not a production
certificate checker or a machine-checked proof of the general rules above.

One counterexample gives every basis input leakage `1/n` while a coherent
superposition leaks with probability one (checked at n=4 and n=16). Another
has uniformly small nonzero leakage and produces a mixed logical state after
auxiliary discard. Exact operator comparison is essential: checking each
basis output's probabilities approximately does not certify coherent cleanup.

Reproduce from the repository root:

```sh
python3 scripts/check_semantic_contract_examples.py
cargo test --test compile --test static_semantics --quiet
python3 scripts/check_docs.py
```

The existing CLI was run on four temporary projects with `f(x)=x` and the
same `with_computed(q,f) { |a| body }` shape:

| Body | Observed current result |
| --- | --- |
| `z(a)` | Accepted; source checking and IR verification succeed. |
| `h(h(a))` | `Unsupported`: the whole body is not a Z/T chain. |
| `x(a)` | `Unsupported` under the same structural restriction. |
| `let q=z(q); a` | `Ownership`: the original q is already consumed/inaccessible. |

These establish the current acceptance boundary, not support for the proposed
extension. The existing `compile` and `static_semantics` suites were rerun:
**37 Rust tests passed**. No Rust source or Lean proof was changed by this
review; no new full compiler soundness theorem is claimed.

The documentation reference check and `git diff --check` also passed.
