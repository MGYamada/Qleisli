# Coefficient domains and approximation

Future design, no generic scalar/angle/device/evidence API. Current bounded R8 and M2 stay fixed.

## Review inventory and v0.3 decision

R8=Z[ζ8,1/2] with bounded i128 cannot represent QFT4's R4. Hierarchical dyadic/phase256/QFT bridges are separate, widths1..8, not all-width/domain-unification proofs. Candidate Z[ζ_(2^k),1/2], k≥max(3,n), embeds ζ8 as ζ_(2^k)^(2^(k−3)). Before v0.3 adoption specify canonical arithmetic/equality/conjugation/complex interpretation, checked embeddings, intermediate/aggregate bounds, serialization/request/dependency binding and migration. Traits/flags/callbacks prove no equality; exhaustion/overflow/unknown rejects, never tolerance fallback. Long exact products may overflow.

## Exact, approximate and device contracts

Exact U Ein=Eout u binds actual IR/interfaces/encodings/phase/dependencies and all-reference zero separation. Approximation separately binds ideal/actual realization/domain/metric/composition. Controlled unitaries require phase-sensitive operator norm; observing maps need complete reference-sensitive instrument/diamond bounds. Unitary sequence errors sum per invocation; channel distance ≤min(2,2Σε) in that convention. P(θ)=exp(iθ/2)Rz(θ); scalar matters under control, ζ16 lies outside Q(ζ8). Native rotations, exact synthesis, resolution, statistics and device noise differ; no STAR/backend preference adopted.

Leakage never licenses pure release: retain scratch or explicit Observe/discard with different contract. Probabilistic realization retains failure/retry/residual outcomes and calibration/device assumptions. Ideal proof grants no hardware guarantee.

## External search and adoption

Untrusted norm-equation search needs future LeafRealizer binding actual circuit/witness to independent gate/domain/interface/error requests; auxiliary equations alone fail. Desugaring adds no domain. Every extension needs laws/fragment/limits/diagnostics/migration and cross-domain/stale/phase/composition faults, preserving R8/cleanup compatibility.
