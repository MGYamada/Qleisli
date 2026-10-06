# Primitive boundary and admission

This chapter records the current production catalogs and the admission process
required by the adopted QS, PR and RS interpretations. It is subordinate to the
[authority hierarchy](authority.md), repository `TRUSTBOUNDARY.md` and
`STDLIB.md`. It adds no primitive, source grammar, target schema, trusted axiom
or discharged guarantee. The remaining decisions in
[#154](https://github.com/MGYamada/Qleisli/issues/154),
[#65](https://github.com/MGYamada/Qleisli/issues/65) and
[#131](https://github.com/MGYamada/Qleisli/issues/131) remain in those Issues;
this inventory does not adopt every proposal in them.

The current implementation is `0.3.0-alpha`, in constitutional edition 2026.
The common original-source judgment uses canonical ordinary `Unit`, `Bit` and
`Bits<n>` types and one typed sealed catalog. The tables below distinguish the
existing concrete finite and selected lowering subsets, whose emitter support
remains distinct. Source recognition and typing do not supply concrete
capability, native acceptance or semantic evidence. Source paths identify files
in the [Qleisli repository](https://github.com/MGYamada/Qleisli).

## Meaning, spelling and implementation

The [discovery and inspectability contract](discovery.md) explains recovery
through signatures and checked derived source, and when sealed/external meaning
requires specification and evidence.

| Category | Authority and obligation |
| --- | --- |
| Semantic primitive or irreducible semantic rule | Defines an operation, instrument, ownership transition or effect rule at the semantic/checking boundary. Its independent intended meaning, premises and actual acceptance rule require review. Writing it in Lean, another package or a backend does not remove that obligation. |
| Sealed source entry | A compiler-owned name/signature that user source cannot replace. Some entries expose existing primitive rules; others are aliases or compositions. Catalog membership alone supplies neither semantic evidence nor a new admitted meaning. |
| Alias or elaborated construction | Lowers to already specified operations with the exact interface, phase and effect. It introduces no independent acceptance authority; its source correspondence still requires evidence. |
| Derived library definition | Ordinary checked `.qli` source. Its mathematical contract is reviewed independently, and its implementation goes through the normal checking path. Placement under `std::` does not exempt it. |
| Backend implementation intrinsic | Implements an existing meaning through a target instruction, decomposition or optimization. Its actual output needs the applicable realization/preservation checks; backend availability cannot grant a new source meaning. |

`std`'s reviewed mathematical specifications are intended meanings under the
trust-boundary policy. This assumption is about specification intent, not the
correctness of every library implementation or name containing `std`. The
native Lean checker alone issues production acceptance. Rust catalogs,
recognizers, lowering, simulation and target emission supply no such authority.

`src/frontend/check/primitive.rs::Primitive::ALL` is the typed common-source
catalog of **27 distinct names**, preserving their exact static/runtime arity,
type trees, principal effects and owner transitions. It introduces no new
native primitive or semantic axiom. Existing concrete catalogs retain
**17 finite entries and 18 selected entries**, with eight names overlapping:
`std::quantum::{h,x,cnot,init0,phase_eighth,split,join}` and
`std::observe::measure_z`. These subsets are recorded in
`src/frontend/core.rs::PRIMITIVES` and `src/frontend/sized/primitive.rs`.
A known common name unavailable to a requested emitter yields a located
unsupported concrete-profile error, not another source grammar or fallback.

## Finite lowering subset of sealed names

All entries in this table are compiler-owned imports. `A` and `B` are
specification metavariables for the currently supported finite basis trees.
Explicit opaque Basis formals are checked by the common source judgment but
remain outside finite concrete eligibility. Argument-list arity and
tuple result shape are distinct. Every supplied quantum owner is consumed by
the source call and explicitly represented in its returned or eliminated
interface. Separate owners may be entangled.

Let `ζ = exp(iπ/4)`. Each equation below specifies exact amplitude, including
phase. Gate actions on a larger system act with the identity on the retained
reference; this is an intended semantic contract, not a claim that all source
and runtime preservation links are already proved.

| Entry | Current signature; effect | Meaning, owners and lowering provenance |
| --- | --- | --- |
| `std::quantum::init0` | `() -> Q<Bit>`; Iso | Introduces a fresh owner/wire in zero. Emits `RawOp::Init0`; no input-state promise about other owners. |
| `std::quantum::h` | `Q<Bit> -> Q<Bit>`; Unitary | Exact Hadamard, `H|b> = (|0> + (-1)^b|1>)/√2`; emits `Gate(H)` and a fresh output token on the same wire. |
| `std::quantum::x` | `Q<Bit> -> Q<Bit>`; Unitary | `|b> ↦ |b xor 1>` with amplitude +1; emits `Gate(X)`. |
| `std::quantum::z` | `Q<Bit> -> Q<Bit>`; Unitary | `|b> ↦ (-1)^b|b>`; emits `Gate(Z)`. |
| `std::quantum::t` | `Q<Bit> -> Q<Bit>`; Unitary | `|b> ↦ ζ^b|b>`; emits `Gate(T)`. |
| `std::quantum::s` | `Q<Bit> -> Q<Bit>`; Unitary | Alias for two successive T actions, `diag(1,i)`; no new gate constructor or acceptance rule. |
| `std::quantum::sdg` | `Q<Bit> -> Q<Bit>`; Unitary | Alias for six T actions, `diag(1,-i)`; exact phase is retained. |
| `std::quantum::tdg` | `Q<Bit> -> Q<Bit>`; Unitary | Alias for seven T actions, `diag(1,ζ⁻¹)`; exact phase is retained. |
| `std::quantum::id` | `Q<A> -> Q<A>`; Unitary | Returns the owned value with no emitted gate. This is linear passage of the owner, not duplication. |
| `std::quantum::phase_eighth` | `Q<A> -> Q<A>`; Unitary | Exact scalar `ζ I`, including on `Q<Unit>`. Emits `ApplyUnitary` with an existing zero-axis monomial, permutation `[0]` and phase exponent `[1]`; adds no physical wire. |
| `std::quantum::cnot` | `(Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)`; Unitary | `|c,t> ↦ |c,t xor c>`; emits `Cnot`, preserves control/target order and returns both owners. Aliased operands reject. |
| `std::quantum::toffoli` | `(Q<Bit>, Q<Bit>, Q<Bit>) -> ((Q<Bit>, Q<Bit>), Q<Bit>)`; Unitary | `|a,b,t> ↦ |a,b,t xor (a and b)>`; emits `Toffoli` and preserves this nested result tree. All three owners must be distinct. |
| `std::quantum::split` | `Q<(A,B)> -> (Q<A>, Q<B>)`; Unitary | Explicitly replaces one binary-product owner with two ordered owners over the same wire list. Emits `Split`; no measurement or separability claim. An arbitrary tuple tree is not flattened. |
| `std::quantum::join` | `(Q<A>, Q<B>) -> Q<(A,B)>`; Unitary | Explicitly combines distinct owners into the ordered binary-product owner, concatenating left then right wires. Emits `Join`; no assertion that the inputs form a product state. |
| `std::observe::measure_z` | `Q<Bit> -> Bit`; Observe | Destructive Z measurement. Consumes the quantum owner and creates an ordinary result; emits `MeasureZ`. The complete unnormalized outcome family is relevant with references. |
| `std::observe::reset` | `Q<Bit> -> Q<Bit>`; Observe | Ends the input logical wire and returns a fresh logical owner/wire in zero. Emits `Reset`; it is an observing reset channel, not pure inverse computation or clean-release evidence. |
| `std::observe::discard` | `Q<A> -> Unit`; Observe | Explicitly consumes the owner with discard semantics. Emits `Discard`; it is not implicit scope cleanup or proof of a zero state. |

Declarations and source-side effect/owner transitions are in
`src/frontend/core.rs` and `src/frontend/compile/lower/primitives.rs`.
`src/frontend/compile/lower/transforms.rs` also constructs static gate/provider
descriptions; those descriptions require their independent evidence. A compiler
declaration, comment or successful lowering is not itself a proof of the table's
mathematical meaning.

## Selected lowering subset of sealed names

`src/frontend/sized/primitive.rs` records the selected concrete subset used by
its projection/concrete elaborator after common source checking. Its internal `TypeShape::Bit` and
`Bits` labels still denote quantum source values, while internal `CBit` and
`CBits` labels denote ordinary values. These private catalog labels are not
source spellings. The table spells the actual source types explicitly. Square-bracketed
parameters below are static natural arguments.

| Entry | Current signature; effect | Meaning, owners and lowering provenance |
| --- | --- | --- |
| `std::quantum::h` | `Q<Bit> -> Q<Bit>`; Unitary | The same exact Hadamard meaning; a finite leaf is bound to actual source ports. |
| `std::quantum::x` | `Q<Bit> -> Q<Bit>`; Unitary | The same exact bit flip; a finite leaf is bound to actual source ports. |
| `std::quantum::cnot` | `(Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)`; Unitary | Controlled X over the ordered control/target owners, followed by explicit owner routing. |
| `std::quantum::phase` | Static `[j,k]`; `Q<Bit> -> Q<Bit>`; Unitary | `diag(1, exp(2πij/2^k))`; emits a dyadic-phase hierarchy proposal. |
| `std::quantum::phase_eighth` | Source: one `Q<A> -> Q<A>` for any Basis tree; selected concrete support: atoms `A = Unit, Bit, Bits<n>`; Unitary | Exact scalar `ζ I`, preserving the input's full type. A checked Unit introduction, finite scalar leaf and Unit elimination form a closed scalar, tensored with the original owner's identity. No physical wire is added; this is not the Bit phase gate. |
| `std::quantum::unit` | One ordinary `Unit -> Q<Unit>`; Unitary | Exact coefficient +1 via existing structural `pack_unit`. Evaluates its argument fully once and creates one fresh zero-axis Unit owner. No static arguments; `unit(())` is unary. |
| `std::quantum::finish` | `Q<Unit> -> Unit`; Unitary | Exact coefficient +1 via existing structural `unpack_unit`. Consumes exactly that Unit owner, preserving preceding scalar work and any surrounding reference. No static arguments, measurement, discard or implicit conversion. |
| `std::quantum::split` | `Q<(A,B)> -> (Q<A>,Q<B>)`; Unitary | Exact coefficient +1 via existing structural `split_tuple`. Consumes one binary-product owner and returns two fresh ordered owners, retaining each complete basis tree and its axes. |
| `std::quantum::join` | Two arguments `(Q<A>,Q<B>) -> Q<(A,B)>`; Unitary | Exact coefficient +1 via existing structural `join_tuple`. Consumes two distinct owners and returns a fresh owner over their ordered concatenated axes. Neither argument need be separable from the other or from a retained reference. |
| `std::quantum::controlled_phase` | Static `[j,k]`; `(Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)`; Unitary | Controlled application of that exact phase, with the first owner as control; both owners return in order. |
| `std::quantum::init0` | `() -> Q<Bit>`; Iso | Fresh-zero preparation in the instrument profile. The current lowerer rejects initialization after observation where the needed preservation is unavailable. |
| `std::observe::measure_z` | `Q<Bit> -> Bit`; Observe | Consumes the owner and appends the ordered readout result to the instrument proposal. |
| `std::registers::take_bit` | Static `[n,k]`; `Q<Bits<n>> -> (Q<Bit>, Q<Bits<n-1>>)`; Unitary | Removes axis `k` into the first returned owner; the remaining axes keep their order. Requires `k < n`. Emits a structural `take_bit` proposal. |
| `std::registers::put_bit` | Static `[n,k]`; `(Q<Bit>, Q<Bits<n-1>>) -> Q<Bits<n>>`; Unitary | Inserts the first owner's axis at position `k` in the remaining ordered axes. Requires `k < n`; emits structural `put_bit`. |
| `std::registers::empty` | `() -> Q<Bits<0>>`; Unitary | Explicitly introduces a zero-width owner through structural `pack_empty_bits`. Zero physical width does not remove the owner obligation. |
| `std::registers::consume_empty` | `Q<Bits<0>> -> Unit`; Unitary | Explicitly consumes that zero-width owner through structural `unpack_empty_bits`; it is not a general discard operation. |
| `std::classical::empty_bits` | `() -> Bits<0>`; Unitary | Constructs the empty ordinary bit list. No quantum owner or measurement is introduced. |
| `std::classical::prepend_bit` | Static `[n]`; `(Bit, Bits<n>) -> Bits<n+1>`; Unitary | Packs the first ordinary bit before the existing ordered list; no quantum action. |

`Unitary` here classifies the quantum action at fixed classical inputs. It does
not make arbitrary classical copying, dropping or packing into a reversible
classical computation. The empty ordinary result has type `Unit` and value
`()`. `Bits<0>` and `Q<Bits<0>>` are distinct from Unit and from each other.

Common source signatures and input-dependent results are checked in
`src/frontend/check/primitive.rs`. `phase_eighth` takes no static arguments and
exactly one `Q<A>` owner, evaluated once, preserving any complete Basis tree A,
including a packaged tuple. Ordinary Unit and tuples of separate owners reject.
Its scalar contract is `ζ I`, not the Bit phase gate. The selected concrete
`src/frontend/sized/primitive.rs::quantum_endomorphism` retains its atom support;
a source-valid packaged tuple can therefore encounter a located concrete
eligibility refusal. `src/frontend/sized/check.rs` checks closed substitutions
and explicit bindings against the common checked interfaces. The selected
concrete catalog is `src/frontend/sized/primitive.rs`;
`src/frontend/sized/elaborate.rs::primitive` materializes its concrete
signatures and guards. Concrete phase arguments require
`k <= 8` and `j < 2^k`; concrete register operations require `k < n <= 8`;
classical prepend requires `n < 8`. These are current preparation capacities,
not general-size semantic theorems. Aggregate elaboration and backend-profile
limits apply in addition.

`unit` and `finish` expose existing independently checked Unit structure; they
add no native semantic constructor or acceptance authority. Their source
correspondence remains a separate obligation. They currently require the
hierarchy path; neither is an alias for a finite observing discard. Both names
are recognized by common source checking; finite concrete materialization
remains unavailable. The selected hierarchy's
`split`/`join` maps retain exact nested Unit/Bit/Bits/tuple bases, take no static
arguments and evaluate their arguments once in source order. `split` requires
an immediate binary tuple; a matching total width does not suffice. Together
with `unit`/`finish` they provide explicit packaged left/right unitors. No
implicit reassociation or owner conversion is inserted. Their independent
source-step check binds the actual structural constructor, complete basis tree,
ordered axes and full caller frame; matching endpoints alone is insufficient.

`src/frontend/sized/lower.rs` emits hierarchy/finite-leaf, structural and
instrument proposals. Source signature acceptance does not imply that every
root/interface is supported by every lowering profile. The dedicated native
hierarchy checks remain necessary. The
[production boundary](production-boundary.md) identifies these routes and the
remaining source-to-operator preservation gap. Common names across the two
lowering subsets do not establish emitter convergence or source preservation.

## Core forms and independent meaning

The public Rust `RawOp` in `src/ir.rs` contains **19 constructors**. They are
untrusted data, not accepted handles or 19 new library functions:

| Family | Constructors |
| --- | --- |
| Preparation and fixed gates | `Init0`, `Gate`, `Cnot`, `Toffoli` |
| Explicit ownership packaging | `Split`, `Join` |
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

`src/frontend/source.rs::BundledRegistry` embeds **four ordinary source
modules with nine public definitions**; one additional private basis helper is
used by `std::reflection`. Both loaders retain all four complete original sources
and their fixed manifest. They receive normal common declaration, type, owner,
access, dependency and effect checking rather than `ImportOrigin::Sealed`.
Concrete materialization and native checking occur under the actual consumer's
scope; selected source checking alone does not natively certify every bundled
specialization:

| Module and source | Public definitions | Contract provenance |
| --- | --- | --- |
| `std::basis`, `stdlib/src/basis.qli` | `xor2`, `and2` | Total finite ordinary basis-label maps. Neither is injective over its two-input domain; a coherent enclosing construction must meet its own obligations. |
| `std::transform`, `stdlib/src/transform.qli` | `hadamard2`, `qft2`, `qft3` | Ordered H tensor H; positive finite Fourier phase, first leaf least significant, output reversal included, no auxiliary or input-state promise. Fourier interfaces remain fixed-width. |
| `std::reflection`, `stdlib/src/reflection.qli` | `reflect_uniform2` | Phase-fixed reflection `2|s><s| - I` with exact computed-auxiliary cleanup. Private `nonzero2` is a normal basis helper; Hadamard is imported from ordinary transform source. |
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

Both loaders reserve `std` and `std::`. Compiler-owned modules expose only the
fixed common catalog; an unknown sealed name is an error, not a fallback to
caller source. Ordinary bundles retain their provenance and original ASTs,
with bundled bytes checked under each loader's byte policy before
parsing/copying. The selected loader additionally reserves all four bundled
module slots and counts their bytes toward its aggregate limit. The finite
loader retains its separate bounded and explicit legacy byte policies and
local filesystem discovery limits. No ambient source replacement or checking
exemption follows from
`ModuleOrigin::Bundled`. Resolution, original source identity, concrete
materialization and independent acceptance remain separate duties; new
alias/re-export syntax in #65 is not admitted here.

## Generic acceptance and library-owned algorithms

The architecture in #131 separates the following responsibilities:

| Responsibility | Boundary |
| --- | --- |
| Producer | Source elaboration, recognizers, search and Rust/Python construction produce candidates. An algorithm name or recognizer match is not acceptance. |
| Independent acceptance | Check actual gates/operations, root, dependencies, ordered interface and encodings under the enabled profile. When an independent meaning is requested, bind and check that request; otherwise disclose its absence. Changing a name cannot grant semantic evidence. |
| Mathematical specification and proof | Keep algorithm meaning and its mathematical theorems on the library/specification/proof side. Separate intended specification review from conformance proof. Mathlib proofs do not replace the Mathlib-free executable checker. |
| Execution and emission | Consume the checked artifact within its recorded scope; separately establish actual runtime/export/target correspondence for claims about those outputs. |
| Compatibility | Bind source selection, roots, dependencies and profile/checker identity; version syntax/API/schema changes through release policy. Edition identifies the constitutional regime. |

The current hierarchy still exposes specialized Fourier/QPE profiles. This
responsibility table does not claim their algorithm-specific acceptance and
proof organization has already been replaced by a general contract calculus.
The architectural Issue's later implementation consolidation is tracked in
[#273](https://github.com/MGYamada/Qleisli/issues/273); the separately approved
0.3.0 common-frontend work does not itself prove generic acceptance or source
preservation. Keep supported paths and their proofs until reviewed replacements
cover their contracts.

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

## Existing guardrails and their limits

`scripts/check_verification_inventory.py` freezes source identities including
both catalogs, public constructor families and their fields. It discovers
unlisted production checking sources. `scripts/check_production_coverage.py`
checks classified public routes and native dispatch. These checks detect drift;
refreshing their metadata is not primitive admission or proof.

The existing regression sources include:

- `tests/review_v021.rs::every_sealed_declaration_matches_the_existing_source_signature`;
- `tests/sized_source.rs::primitive_signatures_agree_through_symbolic_and_concrete_preparation`
  and `concrete_phase_and_repeat_limits_check_zero_and_unused_providers`;
- `tests/project.rs::std_prefix_and_invalid_module_names_cannot_shadow_bundled_modules`,
  `unknown_sealed_name_is_not_reinterpreted_as_user_code`,
  `algorithm_routines_are_bundled_source_with_private_helpers` and
  `import_cycles_and_name_collisions_are_rejected`;
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

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
