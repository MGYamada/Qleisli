# L0: bundled definition contract ledger

Contract-v1 twelve shipped experimental ordinary definitions, not sealed API/product v1. [STDLIB](../STDLIB.md)/[library goal](stdlib-roadmap.md) govern adoption. Every source/IR independently checks; phase/order/owners/effects changes need review. Full automatic conformance/general source and intent proof open. Until0.5 algorithms corpus.

## Common contract fields

Exact trees, ordered owners, references incl entangled states, finite width12/static work budgets. Costs logical/exclude routing/device/synthesis; numerical tolerance1e-12 not proof. QLT>=0.4 future. B2=(Bit,Bit),B3=(B2,Bit),B4=(B2,B2),first low weights1/2/4/8, metanotation only. Unitary entries consume/return same owner unless noted.

## Registered definitions

| ID / API | Signature/effect | Meaning and logical cost |
| --- | --- | --- |
| B001 xor2 / B002 and2 | Bit,Bit->Bit; basis | Total XOR/AND, four-label table/no quantum operation, noninjective; valid compute predicates, not pure lifts. |
| R001 hadamard2 | Q<B2>->same; Unitary | H tensor H, split/two H/join, zero scratch. |
| R002 reflect_uniform2 | Q<B2>->same; Unitary | 2 projector(s)-I,s=H tensor H applied to zero; four H/nonzero2 compute/Z/uncompute/one exact-zero aux. -R differs under control. |
| R003 measure_x | Q<Bit>->CBit; Observe | H/MeasureZ, consumes target, eigenvalue(-1)^b. |
| R004 measure_z2 | Q<B2>->(CBit,CBit); Observe | split/two Z measurements, consume both, left/right order. |
| R005 parity_zz | Q<Bit>,Q<Bit>->((Q<Bit>,Q<Bit>),CBit); Observe | P_s=(I+(-1)^s ZtensorZ)/2; retain sector coherence/reference/data, consume meter: init/two CNOT/measure, max3 live. Individual Z then XOR differs. |
| F001 qft2 / F002 qft3 | Q<B2>/Q<B3>->same; Unitary | Positive F_M[y,x]=exp(2*pi*i*x*y/M)/sqrt(M),explicit reversal,2H+2controlledT / 3H+5controlledT,no scratch. |
| A001 increment2 | Q<B2>->same; Unitary | x->(x+1)mod4,phase+1,CNOT/X/split/join,no scratch. |
| A002 add2 | Q<(B2,B2)>->same; Unitary | (x,y)->(x,(x+y)mod4),16labels/+1,Toffoli/twoCNOT/three split+join, original-low carry. |
| A003 mul2_mod15 | Q<B4>->same; Unitary | x<15->2x mod15,fixed15/+1,(a,b,c,d)->(d,a,b,c),three split+join/no ordinary gate; static16-entry permutation,routing not physically free. |

Source [basis](../stdlib/src/basis.qli), [routines](../stdlib/src/routines.qli), [transforms](../stdlib/src/transforms.qli), [arithmetic](../stdlib/src/arithmetic.qli); exact phase/all-input/reference/cost contracts.

## Acceptance, rejection, cost, IR, and evidence

Exact arity/tree/disjoint owners/effects mandatory; reuse/alias/drop rejects. xor2(tuple) arity error, pure two-bit XOR injectivity error. Static transforms preserve phase/evidence/zero bodies/charged expansion. [Algorithms](../tests/algorithms.rs) Grover/BV/QEC/parity; [static](../tests/static_operations.rs) QFT/QPE phases/off-grid/reference; [order](../tests/order_finding.rs) full-space arithmetic/inverse/powers; [boundaries](../tests/specification_boundaries.rs). Grover one of4 theta=pi/6,success sin²((2k+1)theta),can overshoot; BV needs linear-promise. Bit-flip code assumes code space/<=one X,syndromes I/Xa/Xb/Xc=00/10/11/01; coherent b->((b,b),b) not cloning, decode restored zeros still explicitly discard. Z/two-X faults outside promise. Algorithm success not typing/hardware theorem.

## Sized corpus candidates before standard adoption

[Sized source](../corpus/sized/README.md)/[clients](../tests/fixtures/sized_clients/README.md) XOR/GHZ/QFT/QPE/arithmetic/order/amplitude not bundled. Full unitary beyond promises, exact phase/input restoration/cleanup/reference; repeated-increment AddK not efficient general synthesis. New maximum cases waived; production/named binding/preservation/compatibility/access/resources/stable API/proof+intent review before adoption. Existing twelve contracts remain.
