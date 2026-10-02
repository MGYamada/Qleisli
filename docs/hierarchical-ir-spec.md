<a id="dependency-scheduling-implementation"></a>
<a id="experimental-named-qpe-instrument"></a>
<a id="external-field-encoding-and-reconstruction-host"></a>
<a id="independently-requested-roots"></a>

# Selected bounded hierarchy and evidence profile

Normative M2 contract,not full production integration. Rust authoritative/schemas disabled; new acceptance [Mathlib-free Lean](lean-kernel-migration.md). Reader/native/source/execution/R14/H1-H5 remain separate.

## Scope and representation

Envelope {format:"qleisli.hierarchical-ir",version:1,profile:"qpe-dyadic8-v1",definitions,meanings,encodings,proofs,entry}. Strict JSON/u32 DAG tables/no unknown/cyclic/unreachable nodes. Concrete statics before emission. Full ordered owner/type/axis/classical interfaces incl immediate tuple trees/Unit/Bits(0),Bit k weight2^k. Destination->source maps complete typed bijections; one fresh injective rename across both call sides,IDs only labels/no regrouping.

Wire-field inventory/QLH1 encoding fixed explicitly in [bridge](../src/interchange/hierarchical/bridge.rs) and [host packet](../tests/fixtures/hierarchical_ir/host-packet.md),not Rust-name inference. Definition {interface,effect,body},meaning {interface,body},encoding {logical,physical,body};proof {kind,rule,premises,implementation,meaning,input_encoding,output_encoding,witness};witness {template_version,parameters,references};entry {implementation,proof}. Embedded finite JSON unchanged/no seals.

### Definition nodes

leaf(raw);sequence(nonempty/exact adjoining endpoints);tensor(disjoint/effect join);call(full fresh maps);repeat(closed same-endpoint unitary/body checked at0);inverse(whole-space unitary);control(distinct leading Bit/polarity/full phase);rewire(full typed permutation incl empty);structural;dyadic_phase(frame preserved);computed(actual C/W/C†/encoding);observe_z(consumed Bit/fresh classical);init0(fresh zero). Branch/reset/discard only finite leaves,no standalone release.

### Explicit structural conversions

take_bit(n,k):Bits(n)->(Bit,Bits(n-1)),n1..8/k<n/original remainder order;put inverse. split/join_tuple arity2..64/immediate nested fields. Explicit Bit<->Bits(1),no owners<->Unit or Bits(0) distinct. Consume all/fresh outputs/every axis preserved,zero scalar+1/no nonempty release. [Structural checker](../lean-kernel/QleisliKernel/Hierarchical/Structural.lean) not source/binding theorem.

## Meanings, encodings and derivations

Pure identity/finite/sequence/tensor/inverse/control/power/rewire/structural/phase/qft meanings exact quantum-only interfaces/[SC ring](finite-contracts.md). phase one Bit/qft one Bits(m),F_M[y,x]=exp(2*pi*i*x*y/M)/sqrt(M),M=2^m/positive/low-first. Power endpoints identical/inverse reversed; instruments never pure children even at0; names grant no access.

Encodings identity/tensor/rewire/zero_scratch: E|x>=C(|x> tensor |0_s>),closed whole-space C/unchanged logical prefix/fresh scratch+empty owners. Entry actual prep/prior transition,never shape/lifetime. Proof UEi=Eou includes phase/full interfaces/reference identity.

Rules: finite fresh raw/all-entry exact<=6bits;sequence ordered children/middle encoding;tensor disjoint;inverse whole-space unitary or separate range rule;control Ei=Eo/both sectors/distinct control;repeat actual body/count incl0;associativity exact endpoints/tensor explicit rewire;rewire composed permutations;phase Bit/identity encoding/bounded angle;computed WE=Eu/actual uncompute;conjugation matched V†/controlled W/V/range;schema fixed registry. No conclusion/hash authority; only checked reassociation/identity elimination/permutations/modular phases. Full-content sharing/no phase erasure/coercion/search/dense>6bits. Instrument rule QPE/identity external encodings only.

## Fixed schema import boundary

qft-dyadic8/1,controlled-power/1,qpe-instrument/1;predicate/adder reserved. Manifest binds domains/premises/conclusion/module/declaration/revision/template/actual checker; actual type/axiom/runtime/dependency audits before enablement. Artifact integers/premises/witness never theorem replacement.

QFT j=m-1..0:H(j),phases k=j-1..0 angle2*pi/2^(j-k+1),explicit reversal/O(m²) inspection,no dense F. Actual Fourier root one qft(width1..8)/same Bits endpoints/outer3..16 route-body-reversal; actual phase-fixed H (reject X/-H). Other circuit shapes need derivation; TP-005 retained.

Power true-control repeat2^k/U versus requested power/phase-fixed provider or exact-power proof;leading control0/full owner endpoints/identity encoding,witnessv1[k,providerImplementation]/no refs. [Bridge](../lean-kernel/QleisliKernel/Hierarchical/Power.lean) needs provider equation/isometry; access/cleanup not efficiency names.

## Independent host checks

[Kernel API](../src/interchange/hierarchical.rs) fresh Conditional.checkAll then finite reconstruction from same immutable artifact/shared budget. Pending finite requests bind indices/bytes/proof/four identity endpoints/empty premises+witness; unary legacy<=6axes/explicit Bits adapters,aggregate16 MiB. Standalone derivation rejects finite; inverse/reference needs common-leaf unitarity. Retained result no root/production guarantee.

Independent hierarchy-request version1 has profile/kind/effect/interface/meanings/entry,never artifact-filled. Pair DAG reachable pair0/covers request; every constructor/interface/nonref operand/ordered child equal,no algebraic normalization. Finite pairs fresh exact matrices incl phase. Root.checkAll/QLR1 reconstruct all obligations/retain both documents; [Root theorem](../lean/Qleisli/HierarchicalRoot.lean) reader premises,no graph-environment substitute.

The [VM-27 slice](../tests/fixtures/verification_v027/README.md) checks original
QIRF1/2 leaves, finite request pairs and phase-fixed H natively. All five private
hierarchy/Fourier/instrument/QPE replies use version3 and report the shared native
10,000,000 exact-work count; old replies reject. Additive native-only reports
create no production handles. Existing executable reports independently rebuild
Rust sealed leaves under a separate equal ceiling; `exact_work` retains legacy
work and `native_exact_work` reports native work. External JSON versions remain
unchanged. [Actual native semantic discharge](../lean/Qleisli/NativeHierarchy.lean)
covers fresh leaf/H body meanings and independent pairs; all decoder fields and
small full complex/reference executions have independent tests. General
reader-to-Operator/analytic hierarchy and universal decoder/native compiler
proof premises remain open.

check_instrument/QLI1 binds actual prep/pure equation/readout/output to [initialize-unitary-readout-v1](../tests/fixtures/authoring_sessions/measured-qpe-v021/preparation-packet.md#host-connection-contract). Named QPE request/candidate version1/QLQ1 independently binds provider/full stages/ordered readout,retains original/providerQLR1/shared deadline; finite+provider+phase-fixed-H union reconstructed once,no omitted/duplicate/nonleaf obligations. [Actual QPE theorem](../lean/Qleisli/HierarchicalQpeInstrument.lean) Kraus/reference/packing/completeness conditional actual provider/readers,no source/schema guarantee.

### Experimental checked reference execution

[Execution API](../src/interchange/hierarchical/execution.rs) uses retained actual definitions/finite implementation matrices,not acceptance authority. Input finite possibly unnormalized complex/reference dimension positive,index=reference*2^bits+basis/low-first. Supported pure constructors incl inactive/zero validation,no classical inputs. Instruments all unnormalized residual/reference branches incl0,ascending low-first readout. Shared actual work/state/branch budgets/preflight,overflow/nonfinite/limit abort/no partial/renormalization/expanded repeats/global matrix.

sample_normalized_shots positive finite norm/reported original norm/fresh execution+one high53-bit mass draw per positive shot,conditional normalized residual; aggregate work/output. Drift min(2^-20,2^-40+16*EPSILON*steps),not certified error; any failure aborts batch.

## First QPE profile and exact angles

n,m1..8/n+m<=16;j0..2^k-1/k0..8. Canonical modulus/even-factor reduction/zero(0,0)/inverse same modulus; checked addition before shifts,H separate/finer symbolic/no approximate cleanup.

Limits16 MiB/JSON128/100,000nodes/1Mrefs/graph256/repeat0..4096/2Mstructural/10Mexact. Schedule permutations/decreasing edge ranks/reachability/depth incl0,charge10*nodes+5*refs+3*roots/prepaid preparation/refs preflight/roots<=nodes+1; quadratic typed-port work precharged incl empty. Node/ContractTyping all bodies/effects/fresh maps/meanings/encodings; Observe not equation,typing computed not cleanup. Native framing64 MiB/1Mreads/60s,QLH1 response1,100,000bytes/QLR1 2,200,000bytes,shared nested limits. Failure limit/invalid_ir/contract/unsupported with bounded indices/premise chain; sharing retains2^m-1 QPE executions.

Fresh0/H/bit-k powers/inverse positive QFT/ascending Z/retained target. K_y=M^-1 sum_j exp(-2*pi*i*j*y/M)U^j; instrument sum_y |y><y| tensor (K_y tensor I_R)rho(K_y† tensor I_R),y=sum_k bit[k]2^k. Every outcome/reference/residual/explicit disposal. Approximation future diamond bound min(2,2sum invocation eps); sampling/resolution/noise separate/exact scratch unchanged.

## Synthesis without complete truth tables

M3 Boolean DAG inputs/constants/NOT/XOR/AND/shared nodes: compute/XOR outputs/reverse scratch gives |x,y,0>->|x,y xor f(x),0>,reference-stable O(nodes+edges+outputs); noninjective XOR valid,not in-place lift without inverse/full extension.

M4 add/carry/compare/subtract/reduce/reverse; modular multiply0<a<N<2^n/coprime/inverse constant/identity x>=N,compute-swap-inverse-uncompute;powers a^(2^k)modN. Actual arithmetic/out-of-range/inverse/scratch proofs before Shor/API/math/V1-C5 open.

## Migration and implementation gates

Versioned successor/no RawOp reinterpretation; finite adapters full signature/contracts/fresh leaves,reverse rejects finer/unsupported/limits. [H1-H5](next-minor-spec.md) full binding/audited native+readers/shared source+metrics/small phase+entangled instruments/adversarial limits remain open,V1 separate. [Small-system waiver](v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30) forbids new maxima,old failures retained. [Packets](../tests/fixtures/hierarchical_ir/README.md) keep actual component premises.
