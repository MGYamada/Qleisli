# Coefficient domains and approximation boundaries

Future design direction, not a generic scalar API, new angle profile, approximate evidence or hardware backend. Current R8 and bounded M2 contracts stay fixed.

## Review inventory and v0.3 decision

Production R8=Z[zeta8, 1/2] cannot express general-width dyadic Fourier angles: width four needs R4. A candidate common Z[zeta_(2^k), 1/2] interpretation uses k>=max(3, n) for width n and embedding zeta8 -> zeta_(2^k)^(2^(k-3)). v0.3 must decide arithmetic/equality, complex interpretation, precision embeddings, bounds, serialization/request binding and migration. Small bounded templates do not prove all-width laws.

| Path | Current exact interpretation | Integration limit |
| --- | --- | --- |
| Production flat IR and finite evidence | `Z[ζ8,1/2]`; bounded i128 arithmetic | Exact R4 and higher dyadic rotations cannot be encoded; long product matrices can exhaust coefficients. |
| Experimental hierarchical dyadic phase nodes | The declared bounded dyadic-angle profile and its typed derivations | Finite-leaf bridges must explicitly establish the requested domain and meaning; this is not production CLI acceptance. |
| PhaseWord / PathSum / QFT components | Cyclic phase modulo 256, with a separate complex bridge | The current QFT template profile is widths 1–8; this does not prove all-width QFT or unify the finite scalar implementation. |

## Avoid fixing the language to one hardware forecast

Hardware forecasts do not define semantics. P(theta)=diag(1, e^(i theta))=e^(i theta/2) Rz(theta); the scalar matters under control. zeta16 is outside Q(zeta8), so arbitrary angles exceed R8. Native rotations, exact synthesis and noisy physical realization carry distinct obligations; no STAR dominance or backend is adopted.

## Coefficient-domain parameter: design obligations

Specify reviewed versioned constants/arithmetic/conjugation/canonical equality/complex embedding and intermediate/aggregate limits before enabling a domain. Exact comparison must be decidable in the chosen bounded fragment. Bind domain/version and any checked embedding to meanings/encodings/evidence and dependencies. A Rust trait, callback, success flag or arbitrary certificate cannot implement an equality oracle. Unknown identities or exhaustion fail, never become tolerance-based equality.

## Exact, approximate and device contracts

Exact, approximate and device contracts are separate. Approximate controllable pure operations need phase-sensitive operator bounds; observing maps need the complete instrument/reference metric. For valid unitary sequence bounds epsilon_i, telescoping gives sum epsilon_i, counting each invocation; channel diamond distance <=min(2, 2 sum epsilon_i) under the stated convention. Keep resolution, statistics, synthesis error and noise separate. Approximate leakage never permits pure release: retain scratch or explicitly observe/discard it under another contract. Probabilistic protocols retain failure/retry outcomes.

| Contract | Required statement and binding | What it does not establish |
| --- | --- | --- |
| Exact ideal meaning | Phase-exact `U E_in = E_out u` in the specified domain/meaning system, bound to the actual IR, encodings, interfaces and dependencies. Pure scratch release retains exact zero return and separation for every admitted input/reference. | Physical fault tolerance, noisy execution accuracy or an approximation claim. |
| Approximate implementation | Bind ideal target, actual implementation and an explicitly bounded error ε to a metric, domain of inputs and composition rule. For controllable unitary components, use a phase-sensitive bound such as `op_norm(U_actual - U_ideal) ≤ ε`; for observation use the complete output/reference instrument and a declared diamond-norm bound. | Exact equality, phase access inferred from an uncontrolled channel, or pure cleanup from small leakage. |
| Device/noise realization | Bind target profile, physical/noise assumptions, calibration scope where relevant, success/retry/failure instrument and residual error claims to the realized operations. | A hardware guarantee derived solely from an exact symbolic angle or ideal circuit proof. |

## External rotation search and checked realization

External norm-equation search may propose circuits/witnesses. The future proved Lean [LeafRealizer](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker) must bind them to the independent operation/profile/interface and exact or certified approximate request; an auxiliary equation alone is insufficient.

## Desugaring and adoption gates

Desugaring changes no primitive meaning or domain. A new domain/approximation family needs specified identity/laws/fragments/limits/diagnostics/migration plus cross-domain/stale-evidence faults and phase/error-composition checks. Retain R8 compatibility and cleanup rejections; no arbitrary trait, dependency or native-rotation backend is selected.
