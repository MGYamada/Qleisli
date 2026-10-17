# Primitive boundary and admission

This chapter specifies the edition-2026 `0.3.0-beta` source primitive boundary
and records the audit and migration of the 27 earlier qualified source entries.
It is subordinate to the [authority hierarchy](authority.md),
`TRUSTBOUNDARY.md` and `STDLIB.md`. The cutover in
[#369](https://github.com/MGYamada/Qleisli/issues/369) and
[#167](https://github.com/MGYamada/Qleisli/issues/167) changes source access and
ordinary definitions, not the meaning of the existing Raw constructors or the
native acceptance authority. This inventory is a technical classification;
it is neither a human adoption of a minimal generating set nor a new
constitutional interpretation or guarantee.

## Meaning, spelling and implementation

| Category | Authority and obligation |
| --- | --- |
| Semantic primitive or irreducible semantic rule | An existing operation, instrument, ownership transition or effect rule at the independent semantic/checking boundary. Intended meaning, premises and actual acceptance require review. Moving a rule into a backend or package does not remove these duties. |
| Language primitive | One typed `PrimitiveId`, available by its bare spelling only when lexical and ordinary declaration/import resolution leave that spelling unbound. The identity fixes typing and effect rules; it grants no native acceptance or general inverse/control capability. |
| Derived library definition | Inspectable ordinary `.qli` checked like user source, with a separately reviewed contract. Its `std::` home grants no privilege. |
| Backend implementation intrinsic | An implementation of an existing meaning. Actual target output, phase, axes, workspace and resources retain their separate preservation and realization obligations. Internal operation tags are not additional source primitives. |

Native Lean checking alone issues new production accepted handles. Parsing,
Rust catalogs, lowering, simulation and exporter output do not. Intended
mathematical specifications remain independent of acceptance and require
specification review. A technical inventory, refreshed source hash or successful
test is not primitive admission, proof of irreducibility or source preservation.

## Bare lookup and ordinary shadowing

Unqualified callable resolution has this order:

1. A lexical runtime or static binding, including a moved binding or a binding
   of the wrong callable category, determines the use. Its ownership/category
   error is final; lookup never retries a same-named declaration or primitive.
2. A same-module ordinary declaration or explicitly imported ordinary public
   declaration determines the use under the usual visibility and collision
   rules. Its signature, public effect, access requirements and body obligations
   apply even when its spelling matches a primitive.
3. Only a genuinely unbound spelling may resolve to the corresponding typed
   language primitive. An unknown name remains a name error.

This is a lexical rule, not overload selection by argument type. A failed type,
arity, effect, capability, concrete-profile or native check never selects another
callee or authority. Parameters, lets, fold binders, static providers and
restricted classical/basis expressions preserve their existing category and
scope rules. An ordinary function named `h` receives ordinary source checking;
its name cannot grant Hadamard meaning. A moved local `h` still shadows both.

Primitives are not imports, prelude declarations, reserved identifiers or hidden
aliases. Call `h(q)` or `global_phase_eighth(q)` without a `use`. Ordinary gates
and state/structure definitions require ordinary declarations or explicit
imports. The four former compiler foundation namespaces `std::quantum`,
`std::observe`, `std::registers` and `std::classical` have no callable entries or
compatibility aliases. Importing a retired path rejects with migration guidance;
that guidance is never a lookup path. The bare name `phase_eighth` is not an
alias for `global_phase_eighth`.

## Typed source inventory and exact contracts

`src/frontend/primitive.rs::PrimitiveId` and its `ALL` list contain the 13
retained source identities below. Common typing consumes these identities in
`src/frontend/check/primitive.rs`; finite and selected adapters consume the same
identity rather than classifying names by string. A concrete adapter may refuse
an unsupported identity. Its refusal does not restore qualified lookup or
replace the source judgment. Historical internal tags such as X, Cnot, Init0
and Empty remain transport/emitter vocabulary with no language identity.

Let `ζ = exp(i*pi/4)`. `A` and `B` stand for complete supported Basis trees,
not merely bit counts. Runtime argument-list arity and tuple result shape are
separate. Every quantum argument evaluates once, in source order, and its owner
is consumed and explicitly returned or eliminated. All quantum equations extend
with identity on an arbitrary retained reference. Distinct owners may be
entangled; zero-axis owners remain linear. The following table gives intended
contracts, not a claim of completed general preservation proofs.

| Typed identity; bare spelling | Static/runtime interface; principal effect | Exact action and retained boundary duty |
| --- | --- | --- |
| `H`; `h` | No static arguments; one `Q<Bit> -> Q<Bit>`; Unitary | `H|b>=(|0>+(-1)^b|1>)/sqrt(2)`, same axis. Retains the existing amplitude-mixing action; a deterministic basis map alone cannot express that superposition. |
| `Phase`; `phase` | `[j,k]`; one `Q<Bit> -> Q<Bit>`; Unitary | `diag(1,exp(2*pi*i*j/2^k))`, with exact dyadic arguments and coefficient/profile checks. This is a relative Bit phase, distinct from a scalar. |
| `GlobalPhaseEighth`; `global_phase_eighth` | No static arguments; one `Q<A> -> Q<A>`; Unitary | `ζ I_A`, including Unit/Bits<0> and full packaged trees. Retains explicit scalar phase with no physical wire. This audit does not prove that no alternative algebraic derivation exists. |
| `Unit`; `unit` | No static arguments; one ordinary `Unit -> Q<Unit>`; Unitary | Fresh zero-axis owner, coefficient +1. `unit(())` is unary. Explicit owner introduction is a semantic transition, not classical `()` or implicit preparation. |
| `Finish`; `finish` | No static arguments; one `Q<Unit> -> Unit`; Unitary | Consumes exactly that zero-axis owner with coefficient +1, retaining all preceding scalar work. No observation or clean-state inference for another basis. |
| `Split`; `split` | No static arguments; one `Q<(A,B)> -> (Q<A>,Q<B>)`; Unitary | Explicit binary owner partition, complete child trees and left/right axes retained, coefficient +1. No implicit flattening or separability promise. |
| `Join`; `join` | No static arguments; two `(Q<A>,Q<B>) -> Q<(A,B)>`; Unitary | Consumes two distinct owners, returns one ordered product owner, coefficient +1. This is not a one-tuple-argument call or physical SWAP. |
| `MeasureZ`; `measure_z` | No static arguments; one `Q<Bit> -> Bit`; Observe | Complete destructive Z instrument `K_b=<b|`, including every unnormalized reference branch. Consumes the logical owner. Observation cannot be represented by a pure label. |
| `Discard`; `discard` | No static arguments; one `Q<A> -> Unit`; Observe | Explicit partial trace of the complete subsystem, retaining reference marginal and every erasure history. Not clean release, a zero-state proof or implicit scope destruction. |
| `TakeBit`; `take_bit` | `[n,k]`; one `Q<Bits<n>> -> (Q<Bit>,Q<Bits<n-1>>)`; Unitary | Requires `k<n`; extracts coordinate k and preserves remaining order, phase +1. The zero-width remainder remains owned. Explicit atomic-register routing/type rule. |
| `PutBit`; `put_bit` | `[n,k]`; two `(Q<Bit>,Q<Bits<n-1>>) -> Q<Bits<n>>`; Unitary | Requires `k<n` and distinct owners; inserts the first coordinate at k, retaining the rest and phase +1. No physical SWAP or width-only coercion. |
| `EmptyBits`; `empty_bits` | No static arguments; nullary `() -> Bits<0>`; Unitary | Exact ordinary empty label, copyable and owner-free. In restricted basis/classical expressions only this resolved typed identity receives the existing constructor rule; a same-named ordinary function does not gain it. |
| `PrependBit`; `prepend_bit` | `[n]`; two `(Bit,Bits<n>) -> Bits<n+1>`; Unitary | Ordinary head-before-tail label construction with no quantum action. Retains the existing sized-label/type rule, not preparation or a measurement. |

Retaining a rule records the existing semantic interface needed by this
implementation; it is not a mathematical proof of global minimality. Any
further derivation or removal must first express the whole recorded interface
in ordinary checked source and provide the applicable independent phase, type,
reference, owner/effect, cleanup and resource correspondence. Apparent gate
identities up to phase or matching widths are insufficient. The admission
process below applies to genuinely new authority.

`Unitary` classifies quantum action at fixed ordinary inputs; it does not make
ordinary copying or dropping reversible classical computation. `Bit`, `Bits<1>`,
`Unit`, `Bits<0>`, nested/flat tuple trees and products of separate owners remain
distinct. Effect inference checks bodies independently of public annotations;
external callers, specialization and provider selection use public effects.
Observe/reset/discard cannot be concealed behind Unitary or Isometry labels.
Unitarity alone does not grant inverse or control access.

## Audit and migration of all 27 former entries

Every old source entry is accounted for below. These rows preserve migration
history, not callable aliases. Derived code has its ordinary public interface
and declared static actuals; replacing an import is not a same-name fallback.

| Former qualified entry | Current source access | Derivation or retained semantic rule |
| --- | --- | --- |
| `std::quantum::h` | bare `h` | Existing Hadamard action and exact amplitude rule. |
| `std::quantum::phase` | bare `phase` | Existing exact dyadic relative-phase rule. |
| `std::quantum::phase_eighth` | bare `global_phase_eighth` | Existing full scalar `ζ I`, explicitly named to distinguish T. |
| `std::quantum::unit` | bare `unit` | Explicit zero-axis Unit owner introduction. |
| `std::quantum::finish` | bare `finish` | Explicit Unit owner elimination with phase retained. |
| `std::quantum::split` | bare `split` | Explicit ordered binary owner partition. |
| `std::quantum::join` | bare `join` | Explicit ordered owner combination. |
| `std::quantum::init0` | ordinary `std::state::init0` | `basis unit(()) as _ { 0 }`: the existing injective singleton-to-Bit rule, table `[0]`, coefficient +1. Isometry; one fresh physical wire. |
| `std::quantum::x` | ordinary `std::gate::x` | `h(z(h(q)))`, exact X including coefficient +1. |
| `std::quantum::z` | ordinary `std::gate::z` | `phase[1,1]`, exact `diag(1,-1)`. |
| `std::quantum::t` | ordinary `std::gate::t` | Coherent control of `global_phase_eighth` on an explicit Unit owner, then `finish`; exact `diag(1,ζ)`, no auxiliary physical wire. |
| `std::quantum::s` | ordinary `std::gate::s` | `phase[1,2]`, exact `diag(1,i)`. Readability does not require a power of T. |
| `std::quantum::sdg` | ordinary `std::gate::sdg` | `adjoint(s)`, exact `diag(1,-i)`. |
| `std::quantum::tdg` | ordinary `std::gate::tdg` | `adjoint(t)`, exact `diag(1,ζ^-1)`. |
| `std::quantum::id` | ordinary `std::gate::id[type(A)]` | Return the same owner, coefficient +1; explicit Basis actual preserves the complete tree. |
| `std::quantum::cnot` | ordinary `std::gate::cnot` | Ordinary coherent control of X, control first, target second; both owners returned in order. |
| `std::quantum::toffoli` | ordinary `std::gate::toffoli` | Ordinary control of packed CNOT; three distinct owners and the original nested result tree. |
| `std::quantum::controlled_phase` | ordinary `std::gate::controlled_phase[j,k]` | Ordinary control of the phase provider, exact control/target order; same coefficient/profile premises. |
| `std::observe::measure_z` | bare `measure_z` | Existing complete destructive measurement rule. |
| `std::observe::discard` | bare `discard` | Existing explicit subsystem erasure rule. |
| `std::observe::reset` | ordinary `std::state::reset` | `discard(q); init0()`, Observe. Returns a fresh zero owner; the erased input is not cleanly uncomputed. |
| `std::registers::take_bit` | bare `take_bit` | Existing typed atomic-register extraction rule. |
| `std::registers::put_bit` | bare `put_bit` | Existing typed atomic-register insertion rule. |
| `std::registers::empty` | ordinary `std::structure::empty` | `basis unit(()) as _ { empty_bits() }`: explicit Unit-to-Bits<0> singleton representation, phase +1, one zero-axis owner. |
| `std::registers::consume_empty` | ordinary `std::structure::consume_empty` | `finish(basis q as _ { () })`: exact Bits<0>-to-Unit singleton representation followed by explicit owner elimination. |
| `std::classical::empty_bits` | bare `empty_bits` | Existing ordinary empty-label constructor. |
| `std::classical::prepend_bit` | bare `prepend_bit` | Existing ordinary sized head/tail constructor. |

Reset has channel `rho_AR -> |0><0|_A tensor Tr_A(rho_AR)` with a fresh
output owner; this formula includes arbitrary reference correlations. The Unit
and Bits<0> conversions above are explicit source maps, never definitional type
equality or inserted coercions. Scalar phase accumulated before their use remains
in the composition. Pure structural elimination does not invoke discard.

## Concrete profiles, source retention and resources

All 13 identities have common source typing. Existing finite and selected
profiles still have independent capacities. Finite Raw R8 phase lowering
requires an integral eighth-root exponent, with `k<=8` and `j<2^k`; unsupported
coefficients reject rather than round. Selected dyadic hierarchy preparation
retains its `k<=8`, `j<2^k` and symbolic-word profile; those sufficient checks
are not a complete semantic normal form. Finite register routing remains
`k<n<=12`; selected routing remains `k<n<=8`, and ordinary prepend uses its
existing `n<12` / `n<8` concrete bounds. Aggregate type, width, depth, work and
native limits apply as well. The selected Discard adapter remains unavailable;
ordinary reset therefore does not acquire selected support merely by moving
into std. Instrument initialization after observation retains its existing
profile refusal. No old-route retry is supplied.

Ordinary calls retain original definition, caller instance, static actuals,
public effect and full source/dependency identity. Checked Meaning overrides
retain the exact original Raw witness and actual checked leaf, matrix, both
ports and reference receipts; a same-width endpoint or digest alone is not
source correspondence. Original zero-repeat children retain their checking
obligations. A dormant repeat-zero witness is not an equation between an
arbitrary hierarchy and finite implementation. These bounded engineering
source checks do not claim a general source-preservation theorem.

The ordinary preparation uses the existing Raw `LiftBasis` 0-to-1 table `[0]`;
finite target export must inspect that actual table and fresh wire/owner mapping.
It cannot replace arbitrary rectangular maps by initialization. Structural
singleton maps retain their full Unit/Bits<0> trees and original roots under
composition, repeat, control and adjoint wherever the concrete profile supports
them. Explicit cleanup and rejected observation/phase/width cases remain part
of that profile. Source recognition alone enables none of these emitters.

Semantic ownership, clean/dirty scratch and target workspace are separate.
The T definition's Unit owner has zero physical wires, but does not promise
zero target T cost. SWAP's three ordinary CNOT calls differ from structural
`permute_axes` output routing even when a fixed-coordinate matrix agrees.
A representation sharing count, logical instruction count or checker-work
budget is not quantitative Resource Safety. Every target/resource claim needs
its own actual artifact, model, units and evidence. Exact cleanup must hold
for every permitted input and reference; approximation never excuses dirty
scratch. General QS, PR, quantitative RS and EXACT duties remain pending;
the two admitted ordinary QLV1 ownership/classical-scope scopes remain protected.

## Core forms and independent meaning

The public Rust `RawOp` in `src/ir.rs` contains **21 constructors**. They are
untrusted data, not accepted handles or 21 new library functions:

| Family | Constructors |
| --- | --- |
| Preparation and fixed gates | `Init0`, `Gate`, `Cnot`, `Toffoli` |
| Explicit ownership packaging | `PackUnit`, `UnpackUnit`, `Split`, `Join` |
| Finite action and basis isometry | `ApplyUnitary`, `LiftBasis` |
| Coherent selection | `QuantumIf` |
| Checked computed/cleanup scopes | `CertifiedCompute`, `ComputeUseUncompute` |
| Observation | `MeasureZ`, `Reset`, `Discard` |
| Classical values and branching | `ClassicalConst`, `ClassicalNot`, `ClassicalXor`, `ClassicalAnd`, `ClassicalBranch` |

This list is not the entire semantic vocabulary: `SingleGate`, `CircuitAction`,
protected operations and hierarchy constructors also have their explicit
inventories and obligations. A new raw constructor cannot bypass admission by
being called an implementation detail. Conversely, the presence of a source
alias does not imply a new raw constructor. No free-standing `Release0` exists
in this RawOp set; clean removal is part of the explicitly checked scope.

The relevant provenance is:

| Layer | Actual source and scope |
| --- | --- |
| Data and interfaces | `src/ir.rs`; `lean-kernel/QleisliKernel/Semantics/{Raw,Observation,Finite}.lean`. These expose original operations, ports, finite actions and effects; data construction is untrusted. |
| Pure reference meaning | `lean/Qleisli/Semantics/Finite.lean` supplies literal gate amplitudes, controlled/monomial actions and encoded equations. `Semantics/Raw.lean` retains original events, ordered axes, full complex composition and clean-scope meanings. These references do not define meaning as successful checking. |
| Instrument reference meaning | `lean/Qleisli/Semantics/RawInstrument.lean` retains all erasure outcomes, classical values, hidden histories and unnormalized operators. Reset is erasure followed by fresh-zero preparation. It does not select only a successful sampled branch. |
| Hierarchy operator specification | `lean/Qleisli/HierarchicalOperators.lean` specifies positive dyadic phase, ordered wiring, control and composition. This specification is separate from establishing a complete production hierarchy acceptance-to-operator theorem. |
| Executable acceptance | `lean-kernel/QleisliKernel/Raw/{Structure,Pure,Observation}.lean`, finite/QIRF checks and the dedicated hierarchy checks validate actual IR fields, owners/effects and enabled evidence. The source catalog is not their authority. |
| Production composition and proof limits | `Protocol.Validity`, `Protocol.NativeContract` and their `Qleisli.NativeValidity` / `Qleisli.NativeContract` bridges retain their precise artifact/request scopes. Dedicated hierarchy components have separate bridges. Their exact coverage is recorded in the production-boundary chapter. |

Reference definitions require human specification review. Lean proves stated
relationships to those definitions; it does not decide that a chosen formula
is the intended gate, instrument or resource model. Ordinary accepted roots
have the recorded scoped ownership/classical-scope guarantees. Optional finite
requests and leaf contracts establish additional results only within their
premises. This chapter asserts no general source/runtime, CPTP, clean-release,
target-realization or quantitative resource theorem.

## Ordinary library and module resolution

`src/frontend/source.rs::BundledRegistry` embeds **seven ordinary source
modules with twenty-five public definitions** and five private helpers for
reflection, scalar phase, parameterized phase, packed CNOT and fixed Bit identity.
Both loaders retain all seven complete original sources
and their fixed manifest. They receive normal common declaration, type, owner,
access, dependency and effect checking rather than a compiler-import exception.
Concrete materialization and native checking occur under the actual consumer's
scope; selected source checking alone does not natively certify every bundled
specialization:

| Module and source | Public definitions | Contract provenance |
| --- | --- | --- |
| `std::basis`, `stdlib/src/basis.qli` | `xor2`, `and2` | Total finite ordinary basis-label maps. Neither is injective over its two-input domain; a coherent enclosing construction must meet its own obligations. |
| `std::transform`, `stdlib/src/transform.qli` | `hadamard2`, `qft2`, `qft3` | Ordered H tensor H; positive finite Fourier phase, first leaf least significant, output reversal included, no auxiliary or input-state promise. Fourier interfaces remain fixed-width. |
| `std::reflection`, `stdlib/src/reflection.qli` | `reflect_uniform2` | Phase-fixed reflection `2|s><s| - I` with exact computed-auxiliary cleanup. Private `nonzero2` is a normal basis helper; Hadamard is imported from ordinary transform source. |
| `std::gate`, `stdlib/src/gate.qli` | `id`, `t`, `s`, `sdg`, `tdg`, `z`, `x`, `controlled_phase`, `cnot`, `toffoli`, `swap` | Ordinary phase-fixed gates. T controls a scalar phase on a zero-width Unit owner; phase/Pauli and controlled gates derive through ordinary providers. SWAP uses three CNOTs. No library definition grants primitive authority or a target-cost guarantee. |
| `std::state`, `stdlib/src/state.qli` | `init0`, `reset` | Ordinary explicit singleton-to-Bit preparation and observing discard/preparation; original owner, phase and complete reference instrument retained. |
| `std::structure`, `stdlib/src/structure.qli` | `permute_axes`, `empty`, `consume_empty` | Structural two-axis map `[1,0]`, exact phase +1, with reversed output axes and no physical gate instruction. Explicit zero-width Bits owner introduction/elimination use singleton basis maps. Generic register/permutation interfaces remain unsupported. |
| `std::measurement`, `stdlib/src/measurement.qli` | `measure_x`, `measure_z2`, `parity_zz` | Complete destructive X/Z instruments and nondestructive data-parity measurement with their original owner/result trees and reference behavior. |

The [semantic namespace Reference](stdlib.md) gives every mathematical module's
admission rule, exact public interfaces and migration mapping. `std::routines`
and `std::transforms` are retired without aliases. The three A001–A003 fixed
arithmetic definitions remain ordinary local source in
`examples/order_finding/arithmetic.qli`, preserving amplitude +1, modular
overflow, the addend and the full-space value-15 extension. They have no canonical
std export; `std::arithmetic` is reserved for parameterized arithmetic/number
theory. Reserved family names do not promise callable APIs. Generic QFT
completion and fixed/generic correspondence remain outside all v0.3.0 and the
current goal.

The English source contracts and `STDLIB.md` state intended meanings and
conventions; their presence alone does not prove implementation conformance.
Until 0.5.0, algorithm additions ordinarily belong in the approved corpus rather
than expanding stdlib. This chapter adopts no new library algorithm.

The shared resolver registers complete interfaces and resolves explicit imports
with ordinary visibility and collision rules. Import-only cycles are allowed;
every self-import rejects as a collision. Genuine body/provider/Basis/Meaning
mutual dependencies reject, with only checked decreasing runtime self-calls
permitted. Same-module private lookup remains available; cross-module imports
and host entries require public declarations. Import spelling supplies no
runtime initialization or evidence.

Both loaders reserve `std` and `std::` for the ordinary bundled registry.
The retired foundation catalogs expose no importable entries. Unknown or retired
paths reject; bare primitive lookup occurs only after lexical and ordinary
resolution leave the name unbound. Ordinary bundles retain their provenance and original ASTs,
with bundled bytes checked under each loader's byte policy before
parsing/copying. The selected loader additionally reserves all seven bundled
module slots and counts their bytes toward its aggregate limit. The finite
loader retains its separate bounded and explicit legacy byte policies and
local filesystem discovery limits. No ambient source replacement or checking
exemption follows from
`ModuleOrigin::Bundled`. Resolution, original source identity, concrete
materialization and independent acceptance remain separate duties; new
alias/re-export syntax in #65 is not admitted here.

## Generic acceptance and library-owned algorithms

The 0.3.0 architectural contract in
[#131](https://github.com/MGYamada/Qleisli/issues/131) assigns five distinct
roles to each path below. A role is a responsibility, not a claim that every
required proof already exists. The
[production boundary](production-boundary.md#entrypoints-and-actual-checked-representations)
records the actual predicates, native modes and current theorem limits.

| Path and source | Producer | Independent acceptance | Specification and proof | Execution or emission | Compatibility responsibility |
| --- | --- | --- | --- | --- | --- |
| Project/qrate source: `frontend::project`, `frontend::check`, `frontend::compile` | Load original sources and produce typed/lowered proposals. | Fresh ordinary native checking of every materialized concrete ordinary function root and its retained obligations. | Reviewed source rules and library meanings; source preservation remains separate. | Simulate or export the privately retained accepted artifact. | Preserve source selection, diagnostics, unused declarations and complete interfaces through explicit versioned changes. |
| Explicit module-map source: `frontend::compile::ParsedProgram`, internal `frontend::specialize` | Close explicit bindings, retain original source identities and select a concrete profile before checking. Fourier/QPE recognizers discover candidates only. | Ordinary Raw or the required dedicated hierarchy/request gate; failed checking cannot select another route. | Source-step comparisons and finite contract lemmas retain their bounded scopes. | Run the checked selected root; `emit-proposal` still emits untrusted data. | Retain module/entry/binding identity and the supported finite/hierarchical contracts. The retired public sized namespace is not restored. |
| Flat Raw IR and QIRF: `ir::RawProgram`, `interchange::{native,codec}` | Construct original operations, evidence DAGs and versioned bytes. | `Kernel` checks actual root/dependencies and, for execution, the complete retained QLV2/QDV1 view. | Independent Raw/Observation meanings and ordinary native bridge theorems. | Consume the exact checked graph; output validity alone is not translation preservation. | Retain published flat IR and QIRF `finite-v0` / `finite-meaning-v1` profiles, or publish an explicit versioned mapping before changing them. |
| Finite contracts and leaves: `contract`, `finite_leaf`, `pure_leaf` | Construct independent requested equations and untrusted implementation candidates. | Native contract gate binds original bodies, complete interfaces, encodings and exact equations. | Library/operator equations and arbitrary-reference lemmas under their actual premises. | A private checked contract is usable only for its retained artifacts and capabilities. | Preserve square leaf, rectangular pure leaf and encoded/control contract distinctions; no same-width or effect substitution. |
| Hierarchy inspection: `interchange::hierarchical::Kernel::inspect_native` | Produce the hierarchy and finite obligations. | `--hierarchy-pending` checks conditional structure and required finite leaves. | Structural/finite bridges; complete analytic operator composition remains open. | Inspection alone grants no execution; require a fresh execution-scope view comparison before running. | Preserve this distinct request-free scope and its original root/dependency identity. |
| Hierarchy composition request: `check_against_native` | Propose an actual graph and a separately supplied composition request. | `--hierarchy-request-pending` checks root, leaves and requested pairs. | Generic composition equations under stated premises; producer consistency is not source preservation. | Retain and execute the same graph/request pair. | Preserve request grammar, ordered ports and finite obligations. |
| Hierarchy Fourier request: `check_against_native` Fourier branch | Rust/Python factoring proposes the original trace and Fourier request. | `--hierarchy-fourier-pending` checks root, leaves and Hadamard obligations. | Fourier mathematics belongs to the library/proof role; current specialized bridges remain built. | Use the retained checked graph, without granting a new QFT primitive. | Preserve exact phase, axes and current profile limits until a reviewed generic replacement exists. |
| Hierarchy instrument: `check_instrument_native` | Propose preparation, evolution, readout and the request. | `--instrument-pending` checks all stages, leaves and pairs. | Complete instrument/reference specifications and the stated component results. | Retain all permitted branches and ordered public results. | Preserve observation, initialization, zero-width owners and boundary identity. |
| Named-QPE instrument: `check_qpe_instrument_native` | Discover actual provider/routing/power components and a candidate binding. | `--qpe-instrument-pending` checks the original request, candidate, all stages and finite/Hadamard obligations. | Provider, Fourier and QPE semantic theorems remain separate from recognition. | Execute the same checked instrument, not a name-selected replacement. | Preserve all original provider, root, dependency, phase and readout bindings. |
| Component protocols: readout, preparation, phase/layout and their DAGs | Propose bounded component descriptions. | Their existing dedicated independent component checks. | Component lemmas do not automatically certify an enclosing program. | No component success alone constructs a complete program handle. | Retain each component's version, scope, capacities and caller obligations. |
| Python client and foreign adapters: `python/qleisli`, `interop` | Translate host/foreign inputs and propose IR or target text. | Production imports reach the same native gate; no Python/foreign receipt confers acceptance. | Translation and runtime preservation remain distinct proof duties. | Export consumes an accepted input; target correctness requires its own correspondence. | Preserve public host contracts, supported foreign subsets and explicit unsupported-format refusals. |
| Python sized producers/oracles: `scripts/compile_sized_corpus.py`, `compile_sized_instrument.py` | Independently construct proposals and small-system comparison results. | No producer or numerical oracle issues production acceptance. | Differential results are tests, not generic checker soundness. | Use proposals only after the applicable production gate. | Retain historical inputs and the comparison role; do not revive their grammar as a production frontend. |
| Research: `research/semantic-kernel` | Explore symbolic contracts and proof candidates. | Its research DAG result has no production authority; Raw input still requires native checking. | Research rules and bounded comparison evidence remain explicitly experimental. | No research receipt grants execution, cleanup or device authority. | Keep the independent comparison and its notices/tests; production migration requires separate review. |
| Executable package: `lean-kernel/` | Decode untrusted bytes and compute the enabled checks. | Mathlib-free total executable definitions implement production acceptance. | Actual-definition soundness is proved separately; the implementation language is not a proof of the pipeline. | Native IO/compilation/runtime assumptions remain explicit. | Retain dispatch/profile compatibility, source policy, compiled audit and fixed capacities. |
| Specification/proof package: `lean/` | Formalize independent meanings and construct checked proofs. | Does not replace the native executable or issue a host accepted handle. | Mathlib-backed specifications, bridge theorems, semantic transport and proof audits. | No theorem name alone authorizes execution or a target artifact. | Keep applicable VM-22–VM-29 proofs and protected guarantee bindings current during migration. |
| Engineering comparisons: `engineering_{pure,instrument,pure_tensor,openqasm}` | Propose actual/ideal artifacts, closed budgets and target bytes where supported. | Separate fresh native inequality checks bind the complete actual request and retained view. | Engineering bounds retain their exact metric/domain/reference premises. | Private reports confer only their stated engineering claim. | Preserve distinct claim kinds; epsilon zero cannot grant exact Meaning, control, cleanup, PR or quantitative RS. |

### Required generic-contract bindings

A later generic rule must bind all the following data independently of a QFT,
QPE or other algorithm name. The list is a contract for the migration in #273,
not a newly enabled serialized schema or a claim of generic completeness:

1. **Original implementation.** Retain the original artifact bytes, complete
   operation bodies, selected root and checked dependency graph/order. Bind
   called providers, shared nodes and zero-count or otherwise unused obligations
   required by the profile. A stale index, equal name, matching digest without
   correspondence, or native-valid replacement is insufficient.
2. **Complete interfaces.** Retain separate domain/codomain type trees, classical
   result trees, ordered quantum ports, owner identities, wire coordinates and
   explicit input/output encodings. Unit, Bit, atomic Bits and product trees
   remain distinct even at equal width. State and check encoding dimensions,
   isometry premises and entry/exit compatibility; composition matches the
   complete intermediate contract, not just its bit count.
3. **Actual semantic action.** Check the actual gates, exact coefficients and
   phase, axis order, controls, ownership/effect transitions and permitted
   branches. For instruments retain every unnormalized hidden history and the
   ordered public projection. State the arbitrary-input/reference premises;
   distinct owners are not evidence of separability.
4. **Independent expected meaning.** Fix the requested library/operator or
   instrument meaning before candidate search. Retain its original definition,
   request bytes, source/specification identity and dependencies. A recognizer's
   match or an implementation-derived probability table cannot define it.
   Review intended mathematical meaning separately from proving conformance.
5. **Capabilities and workspace.** Bind forward, adjoint and control access
   separately from semantic unitarity, together with owners, effects, clean/dirty
   workspace and exact restoration premises. Observing/reset/discard bodies
   cannot obtain a pure label by hiding those operations. A resource claim must
   additionally bind its actual target, cost model, workspace and artifact.
6. **Actual checking execution.** Identify the protocol, schema, profile and
   checker compatibility separately from edition and product version. Retain
   original byte decoding, requested root, derived obligations and continuous
   checking states. Independently compare the complete retained host execution
   representation where it crosses the Lean boundary. A serialized success
   flag or old receipt cannot replace a fresh decision.
7. **Consumed or emitted artifact.** Bind a checked conclusion to the actual
   immutable object consumed by execution or emission. Claims about source,
   runtime or targets require their own preservation links; independently
   accepting both endpoints does not prove correspondence between them.
8. **Declared domain and failure.** State every finite/coefficient/phase,
   depth/work and interface limit. The current symbolic phase-word model has
   modulus 256; its exact sufficient checks are not a complete semantic normal
   form or a general phase-domain theorem. Generalization requires its own
   specification/proof and profile migration. Reject unsupported forms,
   changed contracts and exhausted budgets without an authority fallback.

The generic checker may establish a reusable composition or contract rule.
The Fourier sum, QPE distribution and other algorithm-specific mathematical
results belong to library/specification/proof modules that instantiate those
rules. Adding an algorithm must not require granting its name a new trusted
semantic rule. Intended definitions must remain independent of acceptance.
`PathSum.compile_sound` proves correspondence of individual path states; alone
it proves neither the complete complex sum nor a Fourier/QPE specification,
source preservation, completeness, control or observation integration.

Current `QleisliKernel.Qft`, `Qpe` and the hierarchy Fourier/QPE checks and their
`lean/Qleisli` bridge proofs remain implemented, specialized components. This
architectural rule does not move or delete them, claim a completed independent
library decomposition, or add generic QFT to the 0.3.0 scope. Keep supported
checks, exact finite contracts, VM-22–VM-29 authority gates and existing proof
coverage until reviewed replacements cover them. Consolidation, a generic
prototype and later compatibility-path migration remain in
[#273](https://github.com/MGYamada/Qleisli/issues/273). The 0.3.0 common frontend
and its already specified namespace migration remain separate.

## Admission and replacement process

The adopted interpretations require an explicit review before adding semantic
authority. Record the decision in an Issue; do not maintain a second backlog
in this chapter. The required account is:

1. **Identify the addition.** Specify whether it changes semantic rules,
   exposes an existing rule under a source name, derives checked source, or
   implements an existing meaning as an intrinsic. List affected source/Core
   forms, checker predicates, reference definitions and production paths.
2. **Justify irreducibility.** Explain why ordinary checked source, bounded
   elaboration, a verified transformation, a capability/evidence object, a qrate
   definition or target lowering is insufficient. Performance, popularity,
   backend availability and implementation difficulty alone do not qualify.
3. **State the independent contract.** Give the exact whole-input map or
   complete instrument, type/tuple tree, encodings, finite domain, phase,
   ordered axes, owners, effects, capabilities and failure behavior. Include
   arbitrary permitted inputs/references; a gate name or probability table is
   not the contract. State premises rather than assuming separability.
4. **State workspace and realization obligations.** Distinguish semantic data,
   clean/dirty scratch and backend workspace. Require exact permitted cleanup
   and reference restoration; state target/gate assumptions and the actual
   realization correspondence needed under PR. No unspecified target schema,
   projective quotient or approximate cleanup is implied.
5. **Analyze QS, PR and RS.** Identify existing binding interpretations and
   ledger scopes, changed dependencies/assumptions and actual acceptance/artifact
   bindings. State quantitative measures and preservation obligations under RS;
   ownership checks and checker work budgets do not substitute for them.
6. **Provide production evidence.** Check the actual executable definitions,
   transport/decoding and interface/request binding. Add bounded independent
   positive and negative cases for phase, axis order, references, wrong effects,
   duplicate/dropped owners, workspace and stale identities as applicable.
   Build/audit changed proofs and retain explicit source/runtime/target gaps.
7. **Record the decision and migration.** Follow the authority hierarchy for
   specification review, any genuinely new constitutional interpretation and
   guarantee admission. Ordinary aliases and implementation choices covered by
   existing interpretations do not require a new Guardian ruling for each edit.
   Update reviewed inventories, compatibility mapping and applicable proofs
   before enabling the changed boundary; a manifest edit does not grant approval.

Project axioms, unsafe/partial executable definitions and runtime overrides
remain forbidden. A reviewed physical or semantic assumption must be explicit
in the contract; it is not permission to declare a Lean project axiom or to
accept a producer's unchecked assertion.

For example, a proposal to seal `qft2` solely because a backend can execute it
faster fails the irreducibility justification: the ordinary checked
`std::transform::qft2` already expresses its phase-fixed finite contract.
An optimization or target intrinsic can instead propose a realization of that
same meaning and supply the required independent checks. This is an admission
assessment of that stated rationale, not a claim that a historical proposal was
formally rejected or that the optimization is already verified.

Replacing an implementation or exposing an equivalent derived definition must
retain the old intended meaning and applicable guarantees through explicit
correspondence. A semantic change cannot hide under an unchanged name. Record
release compatibility and migration separately from constitutional edition;
not every primitive edit changes the constitutional regime. If a constitutional
amendment is needed, follow its actual edition procedure. Retain historical
artifacts and records rather than rewriting them to match the replacement.

### Edition-aware deprecation and replacement

A proposal must distinguish retiring a spelling or implementation from
changing the primitive's meaning. Record the exact old and new source/Core
forms, semantic contracts, profile/API mapping, release compatibility and
proof/guarantee dependencies. An equivalent derived replacement needs checked
correspondence for the full recorded domain, including phase, references,
owners/effects and workspace; a few matching examples are insufficient.

Keep each historical primitive set recoverable from its exact Git revision and
reviewed inventories, with its original edition/profile and applicable meaning.
Do not rewrite old manifests or adoption records to describe a replacement.
A later edition may deprecate source access under its explicit migration policy,
but cannot erase or weaken an accumulated guarantee for its historical scope.
Within edition 2026, implementation evolution preserves the old intended
meaning; an incompatible source removal requires the ordinary breaking-release
process even when it preserves the safety implication. A genuinely changed
constitutional regime follows the Constitution's actual amendment procedure.
Neither an edition increment nor a new primitive name waives non-weakening.

## Existing guardrails and their limits

`scripts/check_verification_inventory.py` freezes source identities including
the common and concrete catalogs, public constructor families and their fields. It discovers
unlisted production checking sources. `scripts/check_production_coverage.py`
checks classified public routes and native dispatch. These checks detect drift;
refreshing their metadata is not primitive admission or proof. The inventory
pins the typed source identity and concrete adapter sources, discovers new checking
files, and separately records public Raw/finite/hierarchy constructor families
and fields. Its mutation suite rejects a new Raw constructor even if its
source digest is refreshed. Production coverage independently binds public
routes and native dispatch. Review the source, catalog/constructor inventory
and affected acceptance/proof contracts together; updated hashes cannot supply
human specification review or a constitutional judgment.

The typed inventory guard additionally fixes the `PrimitiveId` members, their
`ALL` order, canonical bare spellings and unbound-only lookup body. Adding a
source identity cannot pass by refreshing a file digest or inserting an
internal selected-emitter row. Its mutation calibration separately exercises
typed source growth and an unhandled selected adapter; these are drift/coverage
checks, not judgments of irreducibility or admission.

The existing regression sources include:

- `tests/review_v021.rs` source-signature checks;
- `tests/sized_source.rs::primitive_signatures_agree_through_symbolic_and_concrete_preparation`
  and `concrete_phase_and_repeat_limits_check_zero_and_unused_providers`;
- `tests/project.rs::std_prefix_and_invalid_module_names_cannot_shadow_bundled_modules`,
  the retired-foundation-path refusal checks,
  `semantic_stdlib_modules_are_bundled_source_with_private_helpers` and
  `import_only_cycles_load_but_call_cycles_and_name_collisions_reject`;
- `tests/semantic_contracts.rs::primitive_evidence_preserves_exact_phase`,
  `unit_has_scalar_phase_and_a_distinct_owned_type` and
  `tensor_proofs_keep_low_order_axes_and_allow_a_correlated_reference`.

Lean source/dependency policy and `lean-kernel/Audit.lean` reject unauthorized
project axioms, unsafe executable declarations and forbidden runtime
replacement paths; `lean/Audit.lean` checks the proof package's axiom closure.
The reference-module import policy keeps mathematical semantics separate from
acceptance and transport. These checks and the guarantee-continuity machinery
retain their actual scopes; they do not mechanically judge specification intent
or irreducibility, authenticate a human ruling, or complete every #154 gate.
Listing a regression here does not report a new test run.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
