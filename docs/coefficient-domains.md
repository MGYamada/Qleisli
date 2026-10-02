# Coefficient domains and approximation boundaries

Future design, not generic scalar/angle/approximate-evidence/device APIs. Current
bounded R8 and M2 profiles remain fixed.

## Review inventory and v0.3 decision

Production R8=Z[zeta8,1/2], i128 bounded, cannot represent width-four QFT's R4.
Hierarchical dyadic and phase256/path/QFT components have separate symbolic/complex
bridges, currently widths1..8, not all-width proofs/domain unification. Candidate
Z[zeta_(2^k),1/2] with k>=max(3,n) embeds zeta8 as zeta_(2^k)^(2^(k-3)); v0.3 must
specify arithmetic/equality/interpretation/embedding, limits, serialization/request
binding and migration before adoption. Long exact products may exhaust coefficients.

## Coefficient-domain obligations

Specify versioned constants/arithmetic/conjugation/canonical decidable equality and
complex interpretation, intermediate/aggregate bounds. Bind domains/checked embeddings
to meanings/encodings/dependencies. Traits/callbacks/flags/certificates grant no equality
oracle. Unknown/overflow/exhaustion reject, never become tolerance equality.
Hardware forecasts do not define semantics: P(theta)=exp(i theta/2)Rz(theta), scalar
observable under control; zeta16 is outside Q(zeta8). Native rotations/exact synthesis/
noisy realization are distinct, with no selected STAR/backend dominance.

## Exact, approximate and device contracts

Exact U E_in=E_out u binds actual IR/interfaces/encodings/phase/dependencies and exact
zero separation for every admitted input/reference. Approximation separately binds
ideal target/actual realization, input domain, error metric and composition. Controlled
unitaries need phase-sensitive operator norm, not uncontrolled channel equivalence;
observing operations need full output/reference instrument diamond bounds. For valid
unitary errors epsilon_i, sequence operator bound sum epsilon_i, counting invocations,
channel distance<=min(2,2sum epsilon_i) under that convention. Keep synthesis, resolution,
statistics and device noise separate. Approximate leakage cannot release scratch:
retain it or explicitly Observe/discard under a different contract. Probabilistic
realization retains failure/retry/residual outcomes and explicit physical/calibration
assumptions; ideal exact proof gives no hardware guarantee.

## External search and adoption

Norm-equation search may be untrusted. Future Lean [LeafRealizer](lean-kernel-migration.md#external-search-and-the-leafrealizer-checker)
binds actual circuit/witness to independent gate/domain/interface/error request;
auxiliary equation alone is insufficient. Desugaring adds no meaning/domain.
Every extension needs laws/fragment/limits/diagnostics/migration, cross-domain/stale
faults, phase and composition checks. Preserve R8 compatibility and cleanup rejections.
