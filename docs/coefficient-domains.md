# Coefficient domains and approximation boundaries

Status: **design risk and architectural recommendation recorded on 2026-09-28**.
This follows the user's comment about anticipating the wrong early-FTQC gate
architecture. It is a preparation direction for future MINOR specifications,
not an implemented generic scalar API, arbitrary-angle checker, approximate
certificate or STAR backend. The current [finite contract](semantic-contracts-v0.1.md)
and the selected [M2 exact-angle profile](hierarchical-ir-spec.md#first-qpe-profile-and-exact-angles)
remain unchanged.

## Review inventory and v0.3 decision

**v0.2.1 review follow-up, 2026-09-30; public changes still undecided.**
The production finite domain is sufficient for its declared H/X/Z/T fragment,
but not for exact general-width Fourier transforms. With
`R_k = diag(1, exp(2*pi*i/2^k))`, width four already needs R4 outside R8.
The existing `CircuitAction::Monomial` uses eighth-turn phase labels; increasing
its width bound does not add those missing phases.

| Path | Current exact interpretation | Integration limit |
| --- | --- | --- |
| Production flat IR and finite evidence | `Z[ζ8,1/2]`; bounded i128 arithmetic | Exact R4 and higher dyadic rotations cannot be encoded; long product matrices can exhaust coefficients. |
| Experimental hierarchical dyadic phase nodes | The declared bounded dyadic-angle profile and its typed derivations | Finite-leaf bridges must explicitly establish the requested domain and meaning; this is not production CLI acceptance. |
| PhaseWord / PathSum / QFT components | Cyclic phase modulo 256, with a separate complex bridge | The current QFT template profile is widths 1–8; this does not prove all-width QFT or unify the finite scalar implementation. |

The v0.3 specification work must decide the public scalar/domain and IR contract
alongside types, sizes and capabilities. A candidate common interpretation is
`Z[ζ_(2^k),1/2]` for explicitly bounded `k >= 3`, with embedding
`ζ8 -> ζ_(2^k)^(2^(k-3))`. A width-n QFT needs phase precision at least n;
including H in the same coefficient ring needs `k >= max(3,n)`. These are
mathematical requirements and a design candidate, not a selected representation
or permission to change existing public Rust fields in PATCH.

Before implementation, decide canonical arithmetic/equality, embeddings between
precisions, complex interpretation, intermediate/aggregate limits, serialization,
request/evidence binding and migration of existing R8 clients. For all-width
symbolic QFT, prove the size-dependent phase laws and actual compiler acceptance;
eight bounded template reductions cannot replace that proof. Keep ideal exact
meaning separate from synthesis into Clifford+T and certified approximation.
Tests at small widths must distinguish phase sign, reversal and controlled scalar
phase. The [verification plan](verification-migration-v0.2.md#target-ir-and-reference-semantics-fixed-before-migration)
reuses finite-leaf soundness under hierarchy rather than creating competing
unconnected definitions of correctness. Current domains and schemas stay fixed.

## Avoid fixing the language to one hardware forecast

Starting early risks designing around the wrong future logical gate set. For
the current phase-fixed H/X/Z/T/CNOT/Toffoli fragment and its compositions, the
existing ring `R8 = Z[ζ8,1/2]`, with `ζ8 = exp(iπ/4)`, is sufficient for exact
matrix entries. A Clifford+T target can continue to use it for those circuits;
this does not make every desired ideal rotation exactly expressible in R8.

[Akahoshi et al., PRX Quantum 5, 010337 (2024)](https://arxiv.org/abs/2303.13181)
propose STAR (space-time efficient analog rotation), combining error-corrected
Clifford operations with direct analog rotations whose residual errors remain.
[Toshio et al., Phys. Rev. X 15, 021057 (2025)](https://journals.aps.org/prx/abstract/10.1103/PhysRevX.15.021057)
develop a related small-angle resource-state protocol for early FTQC. These are
alternative architectural proposals, not evidence that STAR will dominate or
that arbitrary rotations become noiseless or fully fault-tolerant.

The following arithmetic implication is our design reasoning, not a result
about Qleisli proved by those papers. General angle support exceeds R8. For
example, the phase gate `P(π/8) = diag(1,ζ16)` is outside it: `Q(ζ16)` has degree
8 over Q, while `Q(ζ8)` has degree 4 and contains R8. Thus `ζ16` cannot be in R8.
Distinguish `P(θ) = diag(1,exp(iθ))` from
`Rz(θ) = diag(exp(-iθ/2),exp(iθ/2))`: `P(θ) = exp(iθ/2) Rz(θ)`, whose scalar
factor matters under coherent control. Choosing a hardware instruction by an equality
only up to global phase is insufficient for the current contracts.

The recommendation is to parameterize future exact algebra by its coefficient
domain and separate exact, approximation and device contracts. This keeps an
extension path for both Clifford+T synthesis and native-rotation targets; it
does not guarantee support for every future architecture.

## Coefficient-domain parameter: design obligations

`Scalar<D>`, `Matrix<D>` and `ExactEvidence<D>` are **design notation**,
not proposed final Rust names, public signatures or implemented generic types.
The current Rust [`Exact`](../src/contract/exact.rs) and matrices are concrete
R8 implementations. Do not change their API or accepted capacities in 0.1.6.

1. **Specify the domain before enabling it.** D must identify a versioned
   representation, admitted constants, canonicalization/equality procedure,
   addition, multiplication, negation, conjugation and a specified embedding
   into C. State algebraic laws and evidence for the implementation's
   correspondence, overflow/work limits and rejection behavior. The required
   gate constants must exist in that domain; “ring” alone does not supply
   Hadamard or arbitrary phase constants. Exhaustion never becomes equality
   within a tolerance.
2. **Keep exact fragment checks decidable and bounded.** General real numbers
   cannot be made exactly comparable merely by adding a type parameter.
   Selected cyclotomic extensions or restricted symbolic phases are candidates
   with their own equality/proof rules. Unknown symbolic identities reject or
   require a separately checked derivation. Do not replace the selected M2
   symbolic dyadic-phase path with dense generalized matrices.
3. **Bind evidence to the domain.** Definitions, meanings, encodings and proof
   identities must retain D and its version. Cross-domain reuse requires a
   checked embedding preserving constants, operations, conjugation and the
   claimed equality; preserve phase, interfaces and dependencies too. Foreign
   metadata cannot choose a new arithmetic implementation or silently coerce
   exact values into floats.
4. **A type parameter is not a plugin trust grant.** Only explicitly reviewed,
   versioned domain implementations may participate in trusted acceptance.
   Arithmetic and equality are part of the evidence kernel's trusted base.
   A user-supplied Rust trait implementation, Python callback or certificate
   that says “equal” cannot issue exact evidence. Measure the added checking
   obligations and retain independent regressions/proof accounts for each
   admitted domain.

## Exact, approximate and device contracts

These are separate future contract families, not interchangeable modes of one
equality test. Existing exact release conditions remain authoritative.

| Contract | Required statement and binding | What it does not establish |
| --- | --- | --- |
| Exact ideal meaning | Phase-exact `U E_in = E_out u` in the specified domain/meaning system, bound to the actual IR, encodings, interfaces and dependencies. Pure scratch release retains exact zero return and separation for every admitted input/reference. | Physical fault tolerance, noisy execution accuracy or an approximation claim. |
| Approximate implementation | Bind ideal target, actual implementation and an explicitly bounded error ε to a metric, domain of inputs and composition rule. For controllable unitary components, use a phase-sensitive bound such as `op_norm(U_actual - U_ideal) ≤ ε`; for observation use the complete output/reference instrument and a declared diamond-norm bound. | Exact equality, phase access inferred from an uncontrolled channel, or pure cleanup from small leakage. |
| Device/noise realization | Bind target profile, physical/noise assumptions, calibration scope where relevant, success/retry/failure instrument and residual error claims to the realized operations. | A hardware guarantee derived solely from an exact symbolic angle or ideal circuit proof. |

For a compatible sequence of unitary implementations with valid operator-norm
bounds ε_i, telescoping gives the conservative total bound `sum_i ε_i`, counting
each actual invocation; the corresponding channel diamond-norm bound is at
most `min(2, 2*sum_i ε_i)`. Specify any different metric convention explicitly.
Repeat nodes do not avoid accumulating invocation error. Algorithmic resolution,
sampling uncertainty, synthesis error and hardware noise have distinct budgets.
For probabilistic rotation protocols, include failure/retry outcomes rather
than assuming that postselected success is a deterministic unitary.

Approximate logical accuracy never authorizes exact pure scratch release.
Use a construction whose ideal scratch cleanup is still exact under the chosen
contract; otherwise retain the scratch or explicitly observe/discard it under
a separately specified instrument contract. Actual hardware noise stays in the
device claim; it is not hidden by an exact ideal cleanup theorem.

## External rotation search and checked realization

Under the [2026-09-29 LeafRealizer policy](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker),
rotation-synthesis norm-equation search may remain an untrusted external
producer. A proved Lean checker must connect its actual circuit and witnesses
to the requested operation, coefficient/gate profile and exact equality or
certified approximation bound. This separates search from checking at each
pass; it does not trust the search algorithm, expand the current coefficient
domain or relax exact auxiliary cleanup. `LeafRealizer` is a future checking
role whose concrete interface and profile still need specification.

## Desugaring and adoption gates

The [desugaring layer](terminology.md#desugaring-layer) translates convenience
forms into already specified core operations without adding primitive meanings
or checker rules. It can normalize a supported phase spelling in the selected
exact domain. It cannot manufacture a new domain or convert a noisy/approximate
rotation into an exact certificate. Synthesis and native-gate selection belong
outside the checker and must submit the evidence required by the chosen contract.

Before implementing a generalized domain or approximation family, specify its
public/serialized identity, laws, supported fragments, bounds, diagnostics and
migration; identify which checker obligations are essential. Retain R8 results
and all existing cleanup rejections. Require cross-domain mismatch and stale
evidence rejection, controlled-phase tests and independent arithmetic/error
composition checks. The current M1 formats and M2 profile acquire no new tags
or capabilities from this note. New public APIs/formats need a MINOR/versioned
extension. No particular Rust trait, dependency, larger ring or native-rotation
backend is selected for implementation by this documentation change.
