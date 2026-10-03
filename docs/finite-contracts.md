# Finite exact semantic and function contracts

Normative Rust SC/FC. [Formal scope](formal-core.md) separates component proofs/tests/specification review from source adequacy.

## Semantic equation and entry

SC-1: independent logical u/encodings Ei,Eo, physical square unitary U; check UEi=Eou exactly, u†u=Ei†Ei=Eo†Eo=I (square u unitary). SC-2: exact trees/effects/holders/axes, first field low/index(a,b)=a+2^bits(A)b, Unit owner retained. SC-3: actual image(Ei) entry from checked prep/prior output/scope, never shape/ownership/image equality alone. All equations extend by identity on arbitrary correlated references.

## Exact checking and immutable binding

SC-4 independently verifies raws/encodings/equations/full interfaces/issued dependencies; names/hashes/cache not evidence, replacement recertifies. Ring Z[1/2,sqrt2,i], canonical signed-i128 dyadics/exponent<=126, no tolerance fallback. Limits including control/scratch: width6/dim64,flat1024steps,tree128/depth32(root0),shared10M exact scalar operations/program (regions capped). Caller Budget spans all stages, no reset.

Unit/Bit/Pair/Tuple>=3 preserve shape/order; actual Circuit/Encoding/Contract retained. Private CheckedContract; check_binding full equality, check_entry encoding not runtime state. [API](../src/contract/mod.rs).

## SC evidence rules

SC-EQ actual all-entry equation+isometries, never selected columns/projected equality; SC-SEQ exact middle encoding/U2U1; SC-TENSOR disjoint ordered owners/entangled frames; SC-ADJOINT unitary U,u/reversed steps/swapped encodings; SC-CONTROL also Ei=Eo/distinct control/full phase, access separate; SC-REUSE full circuit/interface/dependency binding. Acyclic derivations conditional, no Rust/search completeness.

## Certified computed source and raw region

with_computed(q,f,u){|d,a|body}: [language isolation/evaluation rules](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/language-spec.md#9-restricted-auxiliary-computation), f total packed A->Bit; Unit/one/left-associated multiargument domain. u unary declared same-tree unitary/no classical ports or eligible sealed Bit. Body Unitary returns exactly(data,aux); form fresh Q<A>/joins input effect. Caller/pending frame incl Unit retained, split/rejoin axes checked; only extractable closed classical work. Five data bits+aux/1024 body and logical steps.

E0|x>=|x,0>; Cf|x,a>=|x,a xor f(x)>; Ef=CfE0. WEf=Efu implies Cf†WCfE0=E0u: zero/separation for every reference even noninjective f. Raw CertifiedCompute retains predicate/use/logical/body/interface and physical witness; substitution only after checking. No Release0; legacy empty/Z/T rule unchanged. [Examples](../examples/semantic_contracts/README.md).

## Function application and extraction

FC-1 apply_contract(implementation,specification,input): evaluate once before name resolution; both ordinary dependencies checked even unused/zero. Same exact unary unitary Q<A>->Q<A>/no classical ports/full U=u; private scratch only certified cleanup, fresh same ordered output. Iso ineligible; supplied spec equality proves no intended meaning.

FC-CHECK [extractor](../src/contract/function.rs) revalidates both raws/nested evidence/IDs/effects/ports, extracts ordered physical circuits incl phase/output permutation, compares all entries, binds raws/circuits/signature/names/frozen sources. Gates/split/join/equal-width lift/ApplyUnitary/QuantumIf/closed Booleans+branches/protected+certified compute supported. Both arms/premerge phis validate; reject init/observation/classical ports/growing lift/unsupported nodes.

FC limits: SC width/tree/exact bounds; raw1024 incl both arms,retained/extracted1024 each,branch/dependency32,expanded1M steps/implementation and specification (empty body costs1),128 sources/name4096bytes/aggregate names+sources1 MiB. Preflight metadata/raw/extraction/equality before deep copies under one budget.

## FC evidence, caching, transforms and execution

FC-OPAQUE immutable Arc FunctionEvidence retains raw/operator/circuit/signature/names/sources; clone same issued identity, fresh equivalent checks different identity. Binding includes nested identities, construction acyclic; [QIRF](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/machine-interface-spec.md) reconstructs.

FC-CACHE frozen compiler instance/full declarations/signature/dependencies only, no cross-compilation reuse. Full project incl unrelated/comments/std snapshots shared/copy charged once; per-receipt metadata/raw/pair work remains. Public owned identity compatible; disk changes uncertified.

FC-IR action {indices,evidence,adjoint}, ordered distinct in-range targets/matching width/disjoint controls. Empty-axis scalar still moves Unit owner; remap/tensor/sequence/repeat retain order/evidence, inverse reverses/toggles, control both phases, zero checks access. Backend replacement needs correspondence.

FC-EXECUTE uses extracted implementation on actual axes/controls/adjoint, never specification. Exact interpretation may use checked logical matrix with separately justified cleanup substitution. Runtime1M executed steps/shared/precharged expansion; name cost representation. FC-THEOREM/STATIC conditional on raw/extraction/primitive meaning, not Rust/cache/compiler/simulator/device adequacy. [Regression clients](../tests/function_contracts.rs).
