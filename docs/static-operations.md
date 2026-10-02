<a id="a2-有限の静的操作変換"></a>
<a id="表層の契約"></a>
<a id="位相を保持する有限ir"></a>
<a id="最初の利用対象"></a>
<a id="通常定義と公開契約"></a>
<a id="確認した結果"></a>

# Finite static operation transformations

Normative compatible finite profile; general Rust/source preservation remains
open. [Language](language-spec.md) fixes ownership/effects; [M1](next-minor-spec.md)
adds static parameters with explicit access. Named closed targets use the
12-bit profile; M1 uses six bits. Contracts/computed forms keep closed operands.

## Surface contracts

Targets: declared unary unitary Q<A>→Q<A>, no classical ports; sealed
h/x/z/t/s/sdg/tdg on Bit, id/phase_eighth on exact finite A. Same complete trees,
normal body/ownership/effect/cycle checking and independent unary IR verification
precede extraction. No caller capture; an iso identity is ineligible.

| Form | Ownership and exact action |
| --- | --- |
| adjoint(u,q) | Consume/return Q<A>; U† |
| repeat_static(n,u,q) | Consume/return Q<A>; U^n, even zero checks target/body |
| qif(c,q){0=>u0,1=>u1} | Distinct Q<Bit>/Q<A> owners in/out; \|0><0\|⊗U0+\|1><1\|⊗U1 |

Own effect Unitary joins input effects. Quantum arguments evaluate left-to-right;
resolve targets after inputs in residual environment. Live/spent locals hide
callables; static references participate in acyclic dependency checking.
Q<Unit> remains linear/disjoint despite empty wires. Counts canonical decimal
0..4,096; nested expansion/depth/work limits still apply.

### Static target judgment

A signature alone supplies no body evidence. Fresh symbolic input must return
exact Q<A> with no leftovers; check unused bodies, both qif targets and zero
repetitions. Closed deterministic CBit work/branches may flatten only after
both arms validate; retain simultaneous complete phi and final output axes.

### Expression rules and evaluation order

adjoint/repeat evaluate input once, check residual target, emit ApplyUnitary
with fresh token on same ordered wires/type. qif holds evaluated control in
pending frame while evaluating target; target branches may rename that complete
frame. Resolve both branches in same residual environment; emit Join,
ApplyUnitary, Split. Target j maps to j+1, control axis 0, false/true polarity.
Return control then target. Reject aliases, missing zero targets, spent target
names, classical-port targets or stronger declared effects.

## Phase-preserving finite IR

ApplyUnitary contains CircuitSteps: distinct basis controls and Hadamard,
finite monomial or retained contract action. Monomial M|x>=ζ8^phase[x]|p(x)>;
p is total bijective, exponents 0..7, ordered axes distinct/in range and disjoint
from controls. Empty-axis table [0] may carry scalar phase; no arbitrary matrix
primitive. Inverse reverses steps, H unchanged, p_inv[p[x]]=x and
phase_inv[p[x]]=-phase[x] mod 8. Control adds exact predicates. Normalize output
coordinate permutations before inverse/control; never erase phase/order.

Equal-width injective lifts are permutations. Legacy compute must pass its
Z/T structural rule; certified compute contributes independently checked logical
u only after actual W Ef=Ef u, retaining physical evidence. Contract actions
retain the same FunctionEvidence under remap/control/repetition; inverse toggles
adjoint. No unconditional auxiliary release. Raw QuantumIf remains compatible;
source static forms emit ApplyUnitary. Register transformation cap 12 bits
(control+target together), distinct from live-wire cap; copied tables/controls
spend work, all enclosing raw IR is independently checked.

For interfaces ≤6 bits, independent function extraction (separate from frontend
flattening) yields the original exact matrix: adjoint/qif compare their emitted
operator/full controlled block. Above six, existing structural checks remain,
with no larger matrix. Static parameters use issued checked receipts; generic
checking defers concrete comparison to specialization, never assumes names.

repeat_static compares one emitted body to independent original meaning, then
checks actual candidate equals n ordered complete copies: axes, phases,
polarities and receipt identities. Zero candidate is empty but body still checks.
This avoids forming U^n for this source form, while flat IR still expands and
spends work. Base extractor stays six bits/1,024 steps and its dependency limits,
i128/exponent126 exact arithmetic. Long bases/explicit matrix contracts,
repeat_op matrix meanings or long adjoint/qif can still exhaust. No widened
capacity, approximation fallback or proved general Rust transform follows.

## Initial applications

### Ordinary definitions and public contracts

[Bundled ledger](stdlib-contracts.md) fixes qft2:F4 on Q<(Bit,Bit)> and qft3:F8
on Q<((Bit,Bit),Bit)>, positive Fourier including reversal, low-weight-first
bits. Example phase2 returns ((CBit,CBit),Q<Bit>), phase3 returns
(((CBit,CBit),CBit),Q<Bit>), Observe, consuming phase and retaining target.
Controlled U^(2^j) then inverse QFT yields complete
K_y=M^-1 Σr exp(-2πiry/M)U^r on general target/reference inputs; eigenstate
probabilities follow the Dirichlet kernel. No eigenpromise is needed for valid
instrument acceptance. Arbitrary angles/general QPE APIs remain separate.

### Verification record

[Static regressions](../tests/static_operations.rs), [exact translation checks](../tests/static_semantics.rs)
and [serial-copy repairs](../tests/review_v021.rs) cover inverse axes, controlled
signs/empty scalars, zero/body/count limits, QPE phases/off-grid/reference
coherence, malformed tables/control overlaps and altered copies. Their recorded
finite numerical/exact results do not prove arbitrary-source adequacy.

```sh
cargo run --bin qleisli -- run examples/phase_estimation
cargo test --test static_operations
```

The T-eigenstate example returns 1001 (phase bits 100 mean integer 1/8;
last bit measures retained target). Historical test censuses use Git history;
current evidence is beside fixtures and in the generated inventory.
