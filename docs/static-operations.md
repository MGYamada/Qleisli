# Finite static operation transformations

Normative finite profile; [M1](next-minor-spec.md) adds explicit access. Closed named targets width12, M1/contract operands width6. General Rust/source preservation open.

## Surface contracts

Unary declared unitary Q<A>->Q<A>, no classical ports/captures/iso identity; eligible sealed h/x/z/t/s/sdg/tdg on Bit and id/phase_eighth on exact A. Fresh whole-body/effect/owner/cycle/unary-IR checks, including unused/zero/both bodies/empty owners.

adjoint(u,q)=U†; repeat_static(n,u,q)=U^n,canonical n0..4096; qif(c,q){0=>u0,1=>u1}=diag(U0,U1). Evaluate once left-right, keep control pending during target; resolve after inputs, live/spent locals hide callees. Fresh same wires, distinct retained control/target, effect joins inputs. qif Join/ApplyUnitary/Split uses control0/target j+1. Complete output/frame/phases/classical simultaneous phis validate before closed Boolean extraction.

## Phase-preserving finite IR

CircuitSteps use ordered disjoint controls and H/monomial/retained contract. M|x>=zeta8^phase[x]|p(x)>: bijective p,phase0..7,empty-axis scalar allowed. Inverse reverses steps,H unchanged,p_inv[p[x]]=x,phase_inv[p[x]]=-phase[x]mod8. Normalize output permutation before inverse/control, never phase/axis erasure. Equal-width lift is permutation; legacy Z/T compute structural, certified substitution retains checked physical witness; FunctionEvidence retained/adjoint toggled. Raw QuantumIf compatible. Control+target<=12; copies/tables/controls charged.

Original-function independent extractor<=6 bits checks exact adjoint/qif; wider transformations only structural/no larger matrix. Repeat checks actual body against meaning and n complete ordered candidate copies, incl axes/phases/polarities/receipt identity; zero empty candidate still checks body. Source repeat expands/charges, not dense U^n. [SC/FC capacities](finite-contracts.md) apply; specialization freshly checks receipts, no floating/widened fallback.

## Initial applications

[Ledger](stdlib-contracts.md): qft2 F4/Bit pair, qft3 F8/nested triple, positive Fourier/low-first/reversal. Phase2 returns ((CBit,CBit),Q<Bit>),phase3 nested classical triple/target. K_y=M^-1 sum_r exp(-2*pi*i*r*y/M)U^r for every target/reference; no eigenpromise required, general APIs separate. T-eigenstate1001 denotes phase1/8+target1.

[Tests](../tests/static_operations.rs)/[exact](../tests/static_semantics.rs)/[copies](../tests/review_v021.rs) cover phase/control/Unit/zero/axes/off-grid/reference/limits, not general source proof.
