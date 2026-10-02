# Selected bounded hierarchy and evidence profile

Adopted bounded M2 profile; component checkers/proofs exist, complete production integration remains open. Rust is production-authoritative and all external schemas are disabled. New acceptance belongs in the [Mathlib-free kernel](lean-kernel-migration.md); [rule inventory](rule-inventory.md), proof modules and retained packets record coverage. Untrusted desugaring targets specified shared operations without inventing acceptance rules. Source preservation, native/transport correspondence and R14/H1–H5 remain separate.

## Scope and representation

`qleisli.hierarchical-ir`, version 1, profile `qpe-dyadic8-v1`, has exactly `format,version,profile,definitions,meanings,encodings,proofs,entry`. Use strict bounded [machine-interface JSON](machine-interface-spec.md), u32 table indices and DAGs; reject unknown nodes, cycles, invalid references and unreachable entries. QIRF requires its separate decoder.

Interfaces contain ordered quantum `(owner,type,axes)` and classical slots. Preserve complete structural types, immediate tuple arity, nesting, Unit and little-endian Bits(n); Bits(0) remains an owner. Bit k has weight 2^k. Each owner occurs exactly once unless the node explicitly creates/consumes it. Port maps are destination-to-source bijections of complete owner, flattened-axis and classical positions, including empty owners. Mapped slots have identical trees and ordered axes; IDs are labels, not positions. Both call maps together require one consistent fresh injective rename. Regrouping requires an explicit structural conversion.

Definitions are `{interface,effect,body}`, effects unitary/iso/observe. Children reference shared definitions. Concrete bounded static parameters are substituted before emission; host expressions and unbounded arithmetic are absent.

### External field encoding and reconstruction host

Interface `{inputs,outputs}` sides are `{quantum,classical}`; quantum ports `{owner,basis,axes}`, classical `{value,basis}`. Basis prefix arrays use tags unit, bit, bits(width), tuple(arity). Nodes/rules have `tag` plus their exact operands. Meanings are `{interface,body}`, encodings `{logical,physical,body}`, maps `{owners,axes,classical}`, witnesses `{template_version,parameters,references}`, references `{table,index}`, schema rules additionally `id`, entry `{implementation,proof}`. All numeric wire fields are u32. Structural take/put carry width/position; other conversions have no operands. Embedded finite program/description are complete UTF-8 JSON strings, preserving whitespace. Reject missing/duplicate/extra fields and submitted evidence/cache/theorem replacements.

The [Rust host](../src/interchange/hierarchical.rs) proposes a schedule; fresh audited native `Conditional.checkAll` returns pending indices. Rust projects those from the same immutable artifact and reconstructs complete finite program/meaning/boundary equations under one exact budget. `Kernel::new(executable)` selects the dependency; `inspect(payload)` accepts no caller response and retains artifact bytes/leaves/work, with no production conversion or independent root guarantee. No partial report escapes failure.

Private QLH1 uses little-endian length-prefixed u32/bytes, 64 MiB framing and one million bounded reads; host deadline 60 seconds, response ≤1, 100, 000 bytes. Bridge/native/finite-reader correspondence remains explicit; [host packet](../tests/fixtures/hierarchical_ir/host-packet.md) preserves the experiment.

### Independently requested roots

Independent requests have exactly `{format:"qleisli.hierarchy-request",version:1,profile:"qpe-dyadic8-v1",kind,effect,interface,meanings,entry}`. Never fill missing request fields from the artifact. Match full root interface/effect/proof kind, IDs, axes, trees and empty owners.

The proposed actual/request pair DAG is acyclic, entirely reachable from pair zero, covers the request table and names both entries at pair zero. Compare every full interface, constructor, non-reference operand and ordered child; table numbering/sharing may differ. No algebraic normalization, implicit conversion or reordering. Finite pairs retain both descriptions and require independently decoded exact matrix equality, including scalar phase. Artifact/requests share two-million structural and ten-million exact budgets.

`Kernel::check_against` uses fresh `Root.checkAll`; QLR1 embeds unchanged QLH1 plus request/pairs/schedule. Rust rejects omitted/duplicate indices and reconstructs every ordinary/pair obligation before privately retaining both inputs in CheckedRequest. Response ceiling 2, 200, 000 bytes; 60-second/64 MiB limits unchanged, finite payload ≤16 MiB. [Root theorem](../lean/Qleisli/HierarchicalRoot.lean) constructs common denotation/unitarity/reference inverse laws conditional on these readers, without a supplied whole-graph environment. [Request packet](../tests/fixtures/hierarchical_ir/root-request-packet.md) records binding mutations.

`check_instrument` additionally binds actual preparation, requested pure equation, ordered readout/output under [initialize-unitary-readout-v1](../tests/fixtures/authoring_sessions/measured-qpe-v021/preparation-packet.md#host-connection-contract). Nested QLI1/QLR1/QLH1 share one-million decoded words and the same framing/work budgets. Sealed CheckedInstrument retains both documents. [Instrument bridge](../lean/Qleisli/HierarchicalInstrument.lean) proves branch/residual/reference density and CBit packing; completeness additionally needs actual finite-leaf unitarity/independent meaning. Neither API grants production authority or named QPE from artifact-only inspection.

### Experimental named QPE instrument

`check_qpe_instrument(payload,request,candidate)` uses separate version-one `qleisli.qpe-instrument-request` and `qleisli.qpe-instrument-candidate`, profile qpe-dyadic8-v1. Request supplies full preparation/circuit/readout/output and independent provider request; candidate proposes actual H/power/inverse-Fourier/provider indices and schedules. QLQ1 embeds the original entry/preparation/readout and provider QLR1. All nested frames share the preceding word/framing/structural limits, 60-second deadline and 2, 200, 000-byte response ceiling.

Reconstruct all finite/provider-pair obligations and the deduplicated phase/Fourier H union exactly once under one exact budget, including phase-fixed mathematical H. Private CheckedQpeInstrument retains candidate bytes and exposes CheckedInstrument. [Actual theorems](../lean/Qleisli/HierarchicalQpeInstrument.lean) bind full arbitrary-reference Kraus maps, completeness and classical packing, conditional on exact finite/H readers and independently interpreted provider. Candidate claims, native/transport correspondence and general source preservation are distinct; no production conversion/schema is enabled.

### Experimental checked reference execution

`CheckedRequest::execute`/`CheckedInstrument::execute` interpret retained actual definitions and checked finite implementation matrices. Input coefficients are finite possibly unnormalized `[real,imaginary]`, positive reference dimension; index = reference*2^quantum_bits+basis, first declared axis least significant, reference unchanged. Support finite/sequence/tensor/inverse/control/repeat/rewire/structural/dyadic phase, checking children even under zero repeat/inactive control. Classical circuit inputs/other constructors reject unsupported. Instruments apply actual fresh-zero preparation and ordered measurements, returning every unnormalized residual/reference branch, including zero branches, packed low bit first.

ExecutionLimits charges aggregate state/work or state/returned-branch amplitude cells (caller input excluded), preparation/readout cells, definition visits, permutation/phase cells and finite multiply-adds. Reserve task metadata only if guaranteed future visits fit work; parsed metadata has its separate framing cap. Overflow, bad dimensions/nonfinite coefficients/exhaustion reject without partial output or silent normalization. Traverse sharing without expanding repeats or global dense matrices. f64 execution is diagnostic, outside acceptance.

`sample_normalized_shots` explicitly normalizes positive finite norm, reports original norm, freshly executes each shot and samples full branch mass using one high-53-bit RandomSource draw; independent uniform words are a caller premise. Return packed outcome and normalized conditional residual/reference. SamplingLimits checks positive shot count before allocation and shares total work/output allowance. Drift guard is min(2^-20, 2^-40+16*f64:: EPSILON*actual_steps), a runtime tolerance, not certified error. Norm/drift/overflow/limit/RNG failure returns no partial batch.

### Definition nodes

The closed constructors and operands follow. Only leaves may contain existing classical branch/reset/discard; exact interface/effect and finite reconstruction still apply. No standalone release0 exists. Computed scopes require matched C/W/C† and the checked encoding equation.

Sequence joins all effects and exact intermediate interfaces; tensor concatenates disjoint owner/wire/classical frames at both endpoints. Call maps share consistent injective fresh renaming, preventing preserved-ID changes/new-ID capture. Control places a fresh distinct Bit first at both ends, with the child quantum-only and identical ordered target trees; equal-width Bit/Bits(1) coercion is forbidden. Phase preserves its named target/frame; measurement consumes its named Bit and emits fresh classical ID; init creates fresh Bit owner/wire with the exact surviving frame. Body checks include zero repeat. These structural conditions do not establish provider/cleanup equations.

| Node | Fields and meaning |
| --- | --- |
| `leaf` | `program`: complete bounded finite raw program; checked by the existing independent verifier and, when used as a semantic leaf, the exact checker |
| `sequence` | `children`: ordered nonempty definition refs; adjacent exact interfaces match; execution order is array order |
| `tensor` | `left,right`: disjoint interfaces; effect join; ownership includes both frames |
| `call` | `definition,input_map,output_map`: complete ordered bijective port maps, no capture; substitute local IDs freshly |
| `repeat` | `count,definition`: identical unitary quantum-only input/output; body checked even for count zero |
| `inverse` | `definition`: checked whole-space unitary, inverse effect remains unitary |
| `control` | `definition,polarity`: checked whole-space unitary and one additional distinct control owner, with boolean polarity; full phase retained |
| `rewire` | `permutation`: complete bijection of typed slots/axes, preserving each slot's type; zero-wire owners participate |
| `structural` | `operation`: one explicit ownership conversion from the closed set below; exact types and axis routing are checked without a dense leaf |
| `dyadic_phase` | `target,j,k`: Bit target, diag(1,exp(2πij/2^k)), exact integers in the angle profile |
| `computed` | `compute,use,logical,encoding`: complete checked compute/use/uncompute region; local scratch does not escape |
| `observe_z` | `input,output`: consume a Bit owner and emit a classical bit |
| `init0` | `output`: create fresh zero Bit ownership |

### Explicit structural conversions

Conversions below are closed internal node/meaning operations, not implicitly adopted source notation. They cover only converted quantum ports; frame via tensor/call. Consume every input owner, produce fresh outputs, preserve every physical axis; n=1 take retains fresh Bits(0). Denotation is the actual phase-free routing bijection, identity on references; empty conversions have scalar +1 and cannot release nonempty scratch. Inverse swaps operations/endpoints and checks both routing laws. [Actual checker](../lean-kernel/QleisliKernel/Hierarchical/Structural.lean) is shared by definition/meaning typing, with remaining-budget and reference round-trip theorems. Semantic binding, source preservation and external integration remain distinct; [packet](../tests/fixtures/hierarchical_ir/structural-packet.md) retains evidence.

| Operation | Complete quantum input and output |
| --- | --- |
| `take_bit(n,k)` | One Bits(n) owner becomes a Bit owner for axis k and a Bits(n−1) owner for all remaining axes in original order. Require 1≤n≤8 and k<n. |
| `put_bit(n,k)` | Exact inverse: Bit then Bits(n−1) become one Bits(n), inserting the selected axis at k. |
| `split_tuple` / `join_tuple` | One tuple owner becomes its immediate ordered field owners, or the inverse. Preserve each complete nested field tree and immediate arity, between 2 and 64. |
| `bit_to_bits` / `bits_to_bit` | Explicit Bit ↔ Bits(1), preserving its physical wire. |
| `pack_unit` / `unpack_unit` | No owners ↔ one Unit owner, explicitly creating or consuming the one-dimensional owner. |
| `pack_empty_bits` / `unpack_empty_bits` | No owners ↔ one Bits(0) owner, under the same explicit rule. Unit and Bits(0) remain different types. |

## Meanings, encodings and derivations

Meaning constructors are identity, finite, sequence, tensor, inverse, control, power, rewire, structural, phase and qft, with exact ordered interfaces. Finite coefficients are a+b√2+i(c+d√2) with signed dyadic coefficients; only bounded leaves materialize matrices. QFT is positive F_M[y, x]=exp(2πixy/M)/√M, M=2^m, low-bit-first. All pure meanings are quantum-only; phase has one Bit, qft one Bits(m) with identical endpoints, power identical child endpoints, inverse reversed endpoints. Instruments are not pure children even at zero count. Finite headers ≤six input/output bits still require reconstruction/equality. A named unitary supplies no implementation access.

QPE instrument takes/retains provider Bits(n), adds CBits(m) and requires its closed phase-fixed unitary provider plus full n/m/interface/axis binding. Encodings: identity, tensor, rewire and zero_scratch. Identity preserves classical slots; tensor frames disjoint; rewire maps physical side. Zero scratch is E|x>=C(|x>⊗|0_s>) with closed whole-space unitary C, unchanged leading logical ports and fresh declared scratch, retaining zero-width owners. Range entry needs fresh compute or a checked transition; shape/name/lifetime/claimed matrix alone cannot grant entry or cleanup.

Proof fields are `kind,rule,premises,implementation,meaning,input_encoding,output_encoding,witness`. Equation means actual U E_in=E_out u with exact phase/interface. Derive from checked premises; never trust displayed conclusions. Instrument kind is limited to the QPE schema, identity external encodings, all branch/residual/reference CP maps; observe cannot use equation. No general instrument-equivalence checker. Normalization permits only checked same-interface sequence reassociation/identity elimination, full permutation composition and modular dyadic reduction. No commutation guessing, phase deletion, type conversion, host execution/search or >six-bit global multiplication. Memoize complete content/premises/interfaces, not submitted hashes; well-typed wrong binding must reject.

| Rule | Checker obligation/witness |
| --- | --- |
| finite leaf | Independently check the raw implementation, encoding and exact equation within six bits and existing arithmetic/work bounds |
| sequence / tensor | Match the actual IR children in execution order; intermediate encodings equal, or an explicit checked rewire premise connects them; tensor ports/owners disjoint |
| inverse | Whole-space unitary implementation and matching unitary logical/encoding boundary; rectangular encoding requires its separate admitted-range derivation, not this rule |
| control | Same complete encoding on both sectors, fresh distinct control, exact phase and controlled implementation binding; a restricted encoding needs both sectors' entry/exit premises |
| repeat / powers | Actual body/count equals the proof operand/count; identity interfaces and all premises checked for zero; natural arithmetic overflow rejects |
| associativity | Flatten only adjacent sequence nodes of the same exact interfaces/encodings; tensor reassociation needs an explicit owner/type rewire, not dimension equality |
| rewire composition | Compose full permutations including zero-wire owner slots; actual IR order must equal the derived permutation |
| dyadic phase | Match the actual target `Bit`, complete identity-encoded quantum interface and exact bounded `j,k` in both implementation and meaning; preserve phase rather than compare probabilities |
| compute/uncompute | Actual `computed` contains C, W, C† and fresh-zero scope; premise W E=E u with E=C(-⊗0); conclusion returns every private scratch axis exactly zero and factors it from arbitrary references |
| conjugation | Actual sequence V†; controlled W; V, with V/V† matched and disjoint control; whole-space v w v† rule or explicit admitted-encoding premises |
| schema | Only the fixed registry entry, static arguments, premise proofs and exact IR structural witness described below |

### Constructed component coverage

[Rule ledger](rule-inventory.md) and [kernel](../lean-kernel/README.md)/[math bridges](../lean/README.md)
index actual finite/conditional/gradient/Fourier/wiring/call/rule/constructed-denotation
proofs. Detailed retained [packets](../tests/fixtures/hierarchical_ir/README.md) state
component premises/limits and counterexamples. The closed external contracts above
remain separate from these bounded proofs. Check actual complete contents from empty
state under one remaining structural budget; no submitted hash/cache/flag/environment
or Rust success is evidence. Unsupported leaves fail even at zero powers.

Finite requests bind actual indices/bytes/proof/four identity-encoded endpoints,
empty premises/witness, unary legacy trees <=six axes with explicit Bits adapters,
aggregate payload<=16MiB. [Finite inspector](../lean-kernel/QleisliKernel/Hierarchical/Finite.lean)
issues pending equations, not opaque-byte semantics; standalone Derivation rejects
finite rules. Fresh [Rust reconstruction](machine-interface-spec.md#reconstructed-finite-unitary-leaves)
remains a correspondence premise until VM closure. Full common-leaf unitarity is
required for inverse/reference laws, not merely equality.

Named Fourier request is existing envelope equation/unitary/entry0 with exactly one
qft(width) meaning and identical closed Bits(width) endpoints. [FourierRoot](../lean-kernel/QleisliKernel/Hierarchical/FourierRoot.lean)
checks width1..8/outer sequence3..16: identity route, actual recursive body, actual
reversal; complete types/maps/empty owners/phase remain. Recursive H requests bind
actual bytes/ports and independently phase-fixed H, rejecting X/-H. QLF1 runs complete
Conditional/namedBoundary and returns every ordinary finite proof/H index. Reconstruct
union once under shared exact work; omissions/duplicates/bad counts/nonleaf indices
reject. CheckedRequest retains both originals, never serialized producer success.
[Root theorem](../lean/Qleisli/HierarchicalFourierRoot.lean) derives full positive Fourier
conditionally on exact readers/native/decoder; TP-005 remains audited. Encoded/computed/
full-schema/provider/source/production and complete Soundness gates remain pending.

<a id="finite-reconstruction-requests"></a>
<a id="conditional-finite-derivations"></a>
<a id="shared-phase-gradient-laws"></a>
<a id="actual-shared-gradient-inspection"></a>
<a id="actual-fourier-stage-coefficients"></a>
<a id="complete-recursive-fourier-body"></a>
<a id="actual-shared-wiring"></a>
<a id="actual-outer-fourier-request"></a>
<a id="fourier-request-host"></a>
<a id="whole-space-derivation-implementation"></a>

## Fixed schema import boundary

Closed shipped registry, never arbitrary Lean proof import. Requested IDs: qft-dyadic8/1, controlled-power/1, qpe-instrument/1; predicate/adder IDs reserved, unknown/unproved reject. Manifest records version, full premise/conclusion, bounded domains, module/declaration/source revision/template/executable checker. Build/type/axiom/executable/dependency audits must bind the acceptance theorem to actual checking; native/transport/Rust-leaf correctness remains separate. Artifacts supply ID/integers/premises/IR witness, never replacement theorem/hash.

QFT template visits ordered j=m−1..0, H(j), controlled phases k=j−1..0 with angle2π/2^(j−k+1), then actual reversing swaps (rewire or three-CNOT). Preserve stages/roles/maps/exact positive F. O(m²) inspection, no dense F; another correct shape needs another derivation. Controlled power needs actual control(repeat(2^k, U)) and checked phase-fixed provider or a separately proved exact-power implementation; repeated squaring requires equations. An efficient label/mathematical unitary grants no efficient access. Local computed/conjugation retain their own range/cleanup premises.

### Direct controlled-power artifact binding

Direct controlled-power/1 matches actual control(repeat(2^k, provider), true) to control(power(providerMeaning, 2^k), true), distinct index domains, leading control axis0, one exact provider premise/identity encodings and full closed types/owners/axes. Version1 parameters [k, providerImplementation], no witness refs; caller independently supplies both. [Power.inspectEntry](../lean-kernel/QleisliKernel/Hierarchical/Power.lean) checks full artifact/dependencies before remaining-budget local inspection. [Bridge](../lean/Qleisli/HierarchicalPower.lean) needs that provider equation and explicit isometry for unitarity/reference maps.

QPE witness: fresh m-bit zero, H each bit, controlled U^(2^k) by bit k, inverse positive QFT, ascending Z readout, retained target. Bind every actual power/stage/dimension, prove full instrument. [Dispatcher](../lean-kernel/QleisliKernel/Schema.lean) only checks closed IDs/versions/parameters; theorem/importer/tests/native/transport/finite-leaf gates still precede enablement. Alternative efficient power providers are separate.

### Typed preparation and dependency scheduling

[Graph](../lean-kernel/QleisliKernel/Hierarchical/Graph.lean) checks a complete schedule
permutation, decreasing rank on every actual edge, reachability/depth, including
zero bodies. Bound nodes100,000, refs1,000,000, depth256, visits2,000,000;
charge10*nodes+5*refs+3*roots, with preparation prepaid. Stop references before excess
and roots after nodes+1. Acyclicity establishes no semantics.

[Artifact](../lean-kernel/QleisliKernel/Hierarchical/Artifact.lean) retains four tables,
entry and full witness/endpoints, bounds references by their own domains, precharges
size/quadratic-port work and finite payload <=16 MiB. Equation cannot observe;
instrument requires QPE meaning/identity boundaries. [Ports](../lean-kernel/QleisliKernel/Hierarchical/Ports.lean)
checks complete typed owner/axis/classical bijections/inverse laws, preserving empty
owners and IDs as labels; charge before coordinate allocation and debit in caller.
Side-map success proves no cross-call freshness/body equation.

[NodeTyping](../lean-kernel/QleisliKernel/Hierarchical/NodeTyping.lean) checks every
actual node/header/effect/frame and consistent fresh two-sided call maps, including
zero bodies. [ContractTyping](../lean-kernel/QleisliKernel/Hierarchical/ContractTyping.lean)
then checks meanings/encodings under the same remaining work, no implicit type
coercion/expansion. Computed shape matches C/W/u/E and fresh scratch but still needs
unitarity, finite reconstruction and actual cleanup/request equations. Type/graph
success does not enable external schemas or issue semantic evidence.

<a id="dependency-scheduling-implementation"></a>
<a id="typed-artifact-preparation"></a>
<a id="complete-side-map-checker"></a>
<a id="definition-node-typing"></a>
<a id="meaning-and-encoding-typing"></a>

## First QPE profile and exact angles

Bounds: 1≤n, m≤8, n+m≤16, phases0≤j<2^k, 0≤k≤8. Normalize modulo denominator then divide even numerator/denominator, zero=(0, 0); negative inverse same modulus. Checked integer addition uses larger denominator, rejects out-of-profile before shift; no float/rounding. H separate; R8 leaves unchanged, finer angles use symbolic nodes. Other coefficient domains/native rotation need separately bound reviewed arithmetic/meaning/approximation; no backend approximation enters this exact profile.

QPE instrument below includes every outcome and retained target/reference correlation; measured y=sum bit[k]*2^k. Eigenphase promises concern resolution only, target disposal is explicit.

Limits: 16 MiB artifact, nesting128, 100, 000 combined nodes, 1, 000, 000 refs, depth 256, repeat 0–4096, 2, 000, 000 charged structural visits, 10, 000, 000 shared exact leaf work. Charge every visited edge/element; memoize checked sharing. Categories: limit, invalid_ir for interface/ownership/effect, contract for equation/schema/binding, unsupported for profile; retain failing index/premise chain within budget. Checking is polynomial in shared artifact plus bounded leaves; explicit QPE executes2^m−1 provider applications, regardless of Repeat storage. Record generation/IR/proof/checker/dense/execution metrics separately.

Future approximate adapters need diamond-distance instrument bounds; unitary errors may use min(2, 2*sum ε_i) counting actual invocations. Sampling/resolution/device error is separate. Exact scratch cleanup cannot weaken; use exact uncompute or reject.

```text
K_y = (1/M) sum_(j=0)^(M-1) exp(-2π i j y/M) U^j.
rho -> sum_y |y><y| tensor (K_y tensor I_R) rho (K_y† tensor I_R).
```

## Synthesis without complete truth tables

M3 selected Boolean DAG: input/constants/NOT/XOR/AND/shared nodes. Compute each into fresh zero with X/CNOT/Toffoli, XOR requested outputs, reverse scratch: |x, y, 0_s>→|x, y xor f(x), 0_s> for all references. Local identities plus complete reverse trace give O(nodes+edges+outputs) evidence/circuit, no exponential truth table. Noninjective f is valid XOR oracle, never in-place lift; in-place synthesis needs inverse/full extension.

M4 selected add/carry/compare/conditional subtract/reduce then reverse cleanup. For multiplication require0<a<N<2^n, gcd(a, N)=1, inverse constant, identity x≥N. Double-buffer compute/swap/inverse-uncompute restores old buffer; bind powers to a^(2^k)modN. Local arithmetic/out-of-residue/inverse/full scratch proofs precede Shor. Decomposition is adopted, complete source/API/math proof and V1-C5 remain open.

## Migration and implementation gates

Use versioned successor, never reinterpret existing RawOp. Old finite adapter preserves full signature/contracts and independently checks leaves. Reverse expansion rejects finer angles/unsupported nodes/budget excess; migrate public exhaustive matches separately. H1–H5 below are pending full integration gates; component checks do not complete them. The [small-system continuation](v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30) removes newly generated maximum-size cases from remaining prerequisites while retaining earlier results/failures. V1-C1–C5 remains separate.

| Gate | Required implementation evidence |
| --- | --- |
| H1 independent binding | Fresh-process checking of every node/rule; mutation of body, static count, interface, phase, dependency, port map and encoding rejected even when cached names match. |
| H2 schemas | Pinned Lean statements about the actual checking definitions, axiom and executable audits; matched templates and negative premise/layout/angle cases; record remaining native, transport and Rust finite-leaf correspondence assumptions. |
| H3 scaling | One shared QPE/QFT definition instantiated at (n,m)=(1,3),(2,4),(8,8); report all size/work metrics, forbid any dense matrix above six bits and any expansion of shared repeated bodies during checking. |
| H4 semantics | Small exact admissible-angle comparison; π/8/finer schema cases; independently computed QPE instrument on superpositions/entangled references at small widths, not only exact eigenphases; preserve target ownership. |
| H5 failure/migration | Cycles, deep inputs, zero-repeat invalid bodies, limits, wrong theorem registry/version and forged entry evidence; old adapter round-trip and explicit reverse-adapter rejection. |
