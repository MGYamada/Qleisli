# L0: bundled definition contract ledger

Format v1 covers twelve shipped experimental ordinary public definitions, not sealed
APIs or product v1. [STDLIB.md](../STDLIB.md), [module contract](standard-library.md)
and [library goal](stdlib-roadmap.md) govern adoption. English source docs/lint establish
form only; finite operator evidence, actual-IR proof and intent review are separate.
Automatic complete ledger conformance (especially observing/iso), general source
preservation and generalized adoption remain open. Add algorithms to corpus until v0.5.

## Common contract fields

All entries are contract v1, shipped experimental. Name/type/effect/ownership/phase/order
changes require contract review. Every declaration receives source and independent IR
checks. Retain arbitrary-reference correlations; disjoint owners need not be separable.
Finite width <=12 and shared static budgets apply. f64 regressions at 1e-12 are not exact
proofs; logical costs below exclude physical/device routing and synthesis. QLT is a
[future design](../tests/fixtures/qlt_design/README.md), implemented only after v0.3 types,
at v0.4 or later.

## Registered definitions

B2=(Bit,Bit), B3=(B2,Bit), B4=(B2,B2), first field low, weights 1,2,4,8.
These abbreviations are not source aliases. Unless noted, operations consume/return
one same-type owner group, with no state promise, measurement or scratch.
All operators below act identically on arbitrary references.

| ID; API | Signature/effect | Full meaning and logical cost |
| --- | --- | --- |
| B001; basis::xor2 | Two Bit arguments -> Bit; basis | Total XOR on four inputs; noninjective product-domain map. Enumerate four labels; emits no quantum operation by itself. |
| B002; basis::and2 | Two Bit arguments -> Bit; basis | Total AND, noninjective; valid XOR-compute predicate, not measurement. Same table cost. |
| R001; routines::hadamard2 | Q<B2> -> Q<B2>; Unitary | H⊗H; split, two H, join; zero scratch. |
| R002; routines::reflect_uniform2 | Q<B2> -> Q<B2>; Unitary | 2\|s><s\|-I, s=(H⊗H)\|00>; four H, nonzero2 compute/Z/uncompute, one private auxiliary with exact label-preserving cleanup. Factored reference execution. |
| R003; routines::measure_x | Q<Bit> -> CBit; Observe | X eigenvalue (-1)^b, consumes target; H then MeasureZ. |
| R004; routines::measure_z2 | Q<B2> -> (CBit,CBit); Observe | Consume both; left then right results, weights 1/2; split and two MeasureZ. |
| R005; routines::parity_zz | Two Q<Bit> arguments -> ((Q<Bit>,Q<Bit>),CBit); Observe | P_s=(I+(-1)^s Z⊗Z)/2; preserve sector coherence/return data, consume meter; Init0, two CNOT, MeasureZ; at most three local live wires. |
| F001; transforms::qft2 | Q<B2> -> Q<B2>; Unitary | Positive F4[y,x]=exp(2πixy/4)/2; two H, two controlled T, explicit output reversal; no scratch. |
| F002; transforms::qft3 | Q<B3> -> Q<B3>; Unitary | Positive F8[y,x]=exp(2πixy/8)/sqrt(8), x=a+2b+4c; three H, five controlled T and reversal; no generalized/approximate QFT. |
| A001; arithmetic::increment2 | Q<B2> -> Q<B2>; Unitary | y -> (y+1) mod4, every label, phase +1; split/CNOT/X/join, zero scratch. |
| A002; arithmetic::add2 | Q<(B2,B2)> -> same; Unitary | (x,y) -> (x,(y+x) mod4), all 16 labels, phase +1. Three split, Toffoli, two CNOT, three join; carry uses original low bits, zero scratch. |
| A003; arithmetic::mul2_mod15 | Q<B4> -> same; Unitary | y<15 -> 2y mod15, fixes15, phase +1. Input (a,b,c,d) returns (d,a,b,c); three split/join, no ordinary primitive gates. Static transforms materialize 16-entry zero-phase permutation; routing is not physically free. No modulus/multiplier parameters. |

Bodies: [basis](../stdlib/src/basis.qli), [routines](../stdlib/src/routines.qli),
[transforms](../stdlib/src/transforms.qli), [arithmetic](../stdlib/src/arithmetic.qli).
Exact phase/encoding, all-input and resource semantics are public contracts.

## Acceptance, rejection, cost, IR, and evidence

Accept exactly the full types/ordered distinct owners above; reject reuse, wrong
arity/tree, aliasing, implicit disposal and declared-effect violations. xor2(p) is
an arity error; do(a,b)<-q;pure xor2(a,b) instead reaches full-map injectivity and
rejects. Basis calls/predicates need no injectivity alone. Static inverses/control/
repetition retain full phase and charge permutation expansion under their budgets.

[Algorithm tests](../tests/algorithms.rs) cover Grover/BV, observing effects, sector
coherence and entangled QEC. [Static tests](../tests/static_operations.rs) distinguish
reflection signs under control and test QFT/QPE phases, off-grid distributions and
references. [Arithmetic tests](../tests/order_finding.rs) cover all basis labels,
wraparound, full-space powers/inverse, entangled round trips and misuse; N=15 is not
general Shor. [Boundary tests](../tests/specification_boundaries.rs) distinguish
basis arity from injectivity. Numerical/inverse agreement alone proves no general
compiler phase-preservation theorem.

## Sized corpus candidates before standard adoption

Case-local candidates live with source/equations/costs in
[sized corpus](../corpus/sized/README.md), [QFT](../corpus/sized/qualtran_qft/README.md),
[QPE](../corpus/sized/qualtran_qpe/README.md), [arithmetic](../corpus/sized/qualtran_arithmetic/README.md)
and [clients](../tests/fixtures/sized_clients/README.md). They are not bundled APIs:
XOR/GHZ, all-ones control, increment/AddK/complement/equality, order/amplitude clients.
Retain full unitary action beyond preparation/residue promises, exact phase, restored
inputs/private scratch and arbitrary references. AddK via repeated increment is not
efficient general synthesis. Historical large results remain frozen; no new maximum
case is required. Adoption requires production source/runtime and independent named
contract binding, preservation/compatibility, reviewed access/resources, stable public
module/API and separate proof/intent review. Preserve the twelve existing contracts.
