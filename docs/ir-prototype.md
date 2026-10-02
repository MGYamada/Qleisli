# Rust finite IR verifier and reference execution

Production Rust profile; [frontend](frontend-v0.md) emits untrusted IR.
General correspondence to [formal models](formal-core.md) remains unproved.

## Inputs and trust boundary

Public RawProgram annotations/effects are untrusted. verify checks ownership,
constructors, finite tables and effects, issuing private VerifiedProgram only
on success. Executors accept that wrapper; rewrites require fresh verification.
BasisShape retains ordered width, not source names/product trees. Width-zero
registers still have owner tokens. QuantumPhi maps each input wire position i
to output position i; it asserts no preparation, copying or separability.
Every live output is covered once; quantum_outputs fixes final order.
Effect is Unitary <= Iso <= Observe; pure means the first two. Expanded IR effects
do not replace source callee declared-effect checking. Classical phi inputs all
precede output introduction, forbidding reads of another output in the same merge.

## Implemented checks

| Operation | Independent obligation |
| --- | --- |
| Resources | Globally fresh input/generated wires and SSA IDs; distinct inputs, single consumption, all live owners returned, no reuse after measurement. |
| Gate/CNOT/Toffoli, split/join, LiftBasis | Sealed meanings, ordered axes, total injective lift. Growth Iso; equal dimensions required for Unitary. |
| ApplyUnitary | Exact finite Hadamards, phase-labelled permutations and basis controls; complete axes, disjoint control/targets, total injective tables, phases 0–7. |
| QuantumIf | Distinct control/target, sealed unitary arms, full scalar phase; no measurement. Legacy raw compatibility variant, not current source producer. |
| MeasureZ/Reset/Discard | Consume, replace with fresh wire, or explicitly trace out ownership respectively; reject Observe operations in pure programs. |
| Classical operations/branch | Visible operand/guard IDs, fresh outputs, both arms from same context, complete fresh phis for live resources; no leaks/hidden effects. Booleans preserve quantum ownership and derive Unitary. |
| ComputeUseUncompute | Total predicate and structural inverse; protected phases/controlled gates preserve source/auxiliary basis labels. No standalone Release0. |
| CertifiedCompute | Check retained W and u against W E_f=E_f u; reserve fresh auxiliary and consume/reissue data owner, including width zero. |
| Contract actions | Reconstruct immutable evidence, ordered local axes/adjoint, complete width and disjoint controls at every attachment. |

[SC/FC](finite-contracts.md) fixes exact capacities, body extraction, source/dependency
binding and cleanup. Raw protected uses are broader than the source identity/Z/T
form; they do not implement borrowing. CertifiedCompute executes retained physical W
between compute/uncompute. Function actions execute independently checked extracted
physical lowering; certified regions may use their proved logical substitution,
while raw witnesses remain retained and differentially tested. Arbitrary matrices,
textual proofs and numerical smallness issue no evidence. Safe API privacy does not
protect against arbitrary external unsafe code.

Table-related registers/auxiliary widths <=12, classical nesting <=64 including
empty arms. No global verifier wire/instruction cap; logarithmic live-wire indexing,
shared freshness/classical scopes and context/interface-proportional branch work
still require separate execution limits.

## Reference execution

run_closed requires no classical/quantum inputs or quantum outputs. Return
probabilities in classical_outputs order; local/global first axis is least
significant. Phis preserve position. Observation/reset/discard retain unnormalized
pure-component ensembles, adding probabilities of hidden histories, not amplitudes;
partial Bell disposal therefore retains a mixed state. f64 is approximate, without
a positive-weight cutoff or renormalization. Tiny outcomes do not prove ideal support.

CertifiedCompute reports InconsistentVerifiedIr if one-valued auxiliary weight/total
exceeds 1e-12 or total is nonfinite. Scale coordinates by maximum absolute value
for this ratio to avoid underflow; the original finite-total check still rejects
overflow. Zero components have no leakage. This alarm follows exact certification
and never authorizes cleanup.

Defaults: 16 axes, 65,536 ensemble components, 1,048,576 aggregate amplitude cells,
1,000,000 steps per run; hard axis cap 20. Charge operation visits, expanded circuits,
legacy protected/unitary steps across components/selected branches. Cached contracts
precharge transitive execution cost; calls/branches never reset allowance. Exhaustion
returns ExecutionLimit without partial result. Limits do not bound FLOPs/wall time;
no silent truncation. [Sampling](machine-interface-spec.md#sampling-and-typed-trials)
is a separately specified trajectory API.

Legacy QuantumIf uses a private post-verification adapter preserving precharged
cost, polarity, axes and Unit scalar phase. Sharing numerical code does not reduce
acceptance. [Producer/debt inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
keeps public variants and independent checking until versioned migration. Desugaring
must preserve input meaning before acceptance; valid output alone is insufficient.

## Evidence and open obligations

[Verifier](../tests/verify.rs)/[simulator](../tests/sim.rs) tests cover ownership,
interfaces/effects, tables, auxiliary misuse, phase, histories/reset/discard and
residuals. Source and static suites cover separate layers. General operation
parameters/classical-port heterogeneous static operations, source borrowing and
open-program production simulation remain unsupported. ComputeUseUncompute runs
its factored effective operator, not independent physical zero-return inspection.
The finite paper argument is conditional, not proof of the Rust checker or hardware.
