# Interoperability: Python, OpenQASM 3 and QIR

Status: **direction selected on 2026-09-28; initial M1.1-A connections implemented**.
The [bounded connection contract](interop-m1.1.md) specifies the current host
adapters: OpenQASM 3 input/output and QIR 2.0 Base text output. The user's added
M1.1 request added these adapters to 0.1.7; they change no `.qli` syntax,
existing capacity or evidence-checking rule. The 0.2.1
[bounded host connections](interop-m1.1.md#structured-cli-and-python) add Python orchestration,
structured CLI commands and optional LLVM-backed QIR Base input. Adaptive
operations, general format/target coverage and all-in-one binary wheels remain
pending. The Python wheel currently requires a separate Rust executable. The
internal execution consolidation below remains a distinct 0.1.6 maintenance
step; planned interfaces are not thereby implemented.

## Goal and user benefit

Let users bring an existing circuit from Python or a standard interchange file,
check it through the same independent boundary, and execute or export the
supported computation without first rewriting it in `.qli`. Qleisli remains
the language for expressing algorithm structure and semantic contracts. Shared
compiler infrastructure makes those checks useful to other frontends too.

The initial adoption target is one package-install command on each declared
supported Python/OS/architecture combination, with prebuilt wheels and no
user-installed Rust or LLVM compiler. A fresh notebook should load an existing
fixture, inspect diagnostics and execute it locally without credentials or
`.qli` translation by the user. Record the exact wheel/platform matrix, package
names and installation measurements before claiming this gate. Complete format
coverage, arbitrary circuit sizes and cloud-device setup are separate costs;
"near zero" is a usability target, not a compatibility guarantee.

## Compiler layers

The following is the selected architecture. M1.1-A connects the existing finite
verifier to the bounded OpenQASM importer/exporter and QIR writer. The 0.2.1
host layer connects Python and the declared QIR-import subset; hierarchical
production integration remains future work:

```text
.qli frontend     OpenQASM importer     QIR importer     Python circuit builder
       \                 |                  |                    /
                 untrusted typed IR and source locations
                                  |
                     independent IR/evidence checker
                                  |
                  checked semantic IR and transformation passes
                                  |
                   target capability and lowering checks
                     /                 |                 \
            reference execution     OpenQASM output     QIR output
```

Python also orchestrates compilation, import, checking, execution and export;
it is not itself a new quantum semantics. The existing finite RawProgram is
the first bridge. The [selected hierarchical IR](hierarchical-ir-spec.md) is
the later shared representation for calls, repetition, exact meanings,
encodings and bound evidence. Early interoperability does not satisfy R14 or
justify flattening scalable algorithms into global matrices or expanded calls.

The [Lean kernel migration](lean-kernel-migration.md) changes the implementation
of the independent checker in stages; frontends, diagnostics, foreign adapters,
CLI and numerical execution remain Rust responsibilities. The current finite
checker is still authoritative. The initial Lean phase-word protocol checks
only its declared cyclic action and does not consume QIRF, OpenQASM or QIR.
Future Lean-required paths must reject unavailable/unsupported checkers and
bind acceptance to the exact artifact subsequently executed or exported.

"Quantum LLVM" means reusable frontends, explicit interfaces, composable passes
and multiple targets. Retain Qleisli ownership, effects, exact phase, encodings
and cleanup evidence until their obligations have been checked. Generic LLVM
IR alone is not that semantic representation. An MLIR dialect could eventually
implement these layers, but adopting MLIR or replacing the selected hierarchy
requires a separate feasibility and compatibility decision.

Each transforming pass must preserve the specified operator/instrument and
return evidence bound to its resulting IR, or invalidate the previous evidence
and require rechecking. Reverification of resource-valid IR alone does not
establish equality to the original meaning. LLVM optimization cannot inherit
a Qleisli proof merely because metadata or a digest survived.

The current finite IR includes semantic tables and compute scopes. Its
OpenQASM terminal exporter is a restricted profile; Bell's injective `[0,3]`
lift and general algorithm examples require decomposition before export.
[Issue 132](https://github.com/MGYamada/Qleisli/issues/132) specifies a v0.4.0
experiment: untrusted LiftBasis NCT synthesis, independently checked table and
clean-workspace realization, exact phase and resource/layout binding. Parity
can reject a same-wire NCT proposal while the source remains a valid unitary.
It cannot decide general target realizability. Unsupported IR continues to
reject; this review does not claim that all examples now export.

## IR reduction and the trusted boundary

On 2026-09-28 the user also selected reduction of the existing IR and adopted
the [small trusted-core discipline](design-philosophy.md#keep-the-trusted-core-small).
Put convenience operations in untrusted desugaring and adapters. QIR/OpenQASM
spellings must not cause new convenience variants in the verifier. The core
retains the obligations external formats do not discharge: linear ownership,
effects, ordered interfaces, exact phase and evidence permitting pure cleanup.

The experimental [phase-word kernel](lean-kernel-migration.md#first-executable-slice)
is produced by the isolated Rust host experiment and consumed by its native
Lean checker. It adds no production `RawOp`, removes no existing acceptance
rule, and does not close the compatibility debt below. New M2 kernel rules
will be implemented in Lean with proofs about those actual definitions;
translation and post-verification execution obligations remain separate.
The later [0.2.2–0.2.9 verification plan](verification-migration-v0.2.md) assigns
inventory, raw-IR coverage and production dual integration to bounded packets.
It preserves the public raw-only forms below; migration to Lean does not itself
remove compatibility debt or prove legacy desugaring correspondence.

Here the **[desugaring layer](terminology.md#desugaring-layer)** is the
meaning-preserving producer of already specified core operations from convenient
source/foreign representations. Its output and proposed evidence are untrusted;
it adds no new gate meaning or checker rule. Decoding a foreign file, choosing
a hardware target and approximate gate synthesis are distinct responsibilities.
Unsupported foreign angles require rejection or a separately specified domain/
approximation extension, not rounding disguised as desugaring.

The [coefficient-domain recommendation](coefficient-domains.md) prepares for
both discrete-gate and native-rotation targets by separating exact domains,
approximation contracts and device errors. Future Python/QIR/OpenQASM artifacts
must retain the selected domain/profile, phase convention and any error claim;
a format's ability to spell an angle does not establish exact evidence for it.
No arbitrary-angle support or new interchange tag is adopted here.

The initial source inspection distinguishes **constructing** an operation from
matching it in a visitor, accounting routine or test. Current emitters and debt:

| Representation | Current production emitter / acceptance consumer | Reduction disposition |
| --- | --- | --- |
| `Gate`, `Cnot`, `Toffoli` | [Primitive lowering](../src/frontend/compile/lower/primitives.rs); raw verifier, exact extractor and simulator | Emitted today. Candidates for later desugaring into the shared unitary vocabulary; preserve separate owners, output ordering, source locations and limits. Do not remove them in a PATCH. |
| `ApplyUnitary` and `CircuitStep` | [Static lowering](../src/frontend/compile/lower/mod.rs), including source `qif`, inverse/control and repetition, plus [M1.1 OpenQASM lowering](../src/interop/profile.rs); raw verifier, exact circuit checker and simulator | Existing common finite unitary vocabulary: controls, Hadamard, exact monomial actions and retained contract calls. The internal compatibility adapter and M1.1-A importer use this vocabulary; the importer emits only the selected Hadamard/monomial subset. No foreign gate requires a new verifier rule. |
| `QuantumIf` and its `UnitaryStep` arms | No current source-lowering constructor; raw Rust callers/tests can supply them. Verifier, evidence preflight/extractor and simulator still accept them. The frontend function-contract size visitor only inspects them. | Explicit compatibility debt. First replace the dedicated numeric interpreter with an adapter to `CircuitStep`; then specify legacy desugaring and migrate this convenience variant out of the core in a MINOR. |
| `ComputeUseUncompute` / `ProtectedUse` | [Restricted source lowering](../src/frontend/compile/lower/mod.rs) emits an empty target list and only Z/T `ProtectedGate` on its single ancilla. Raw verifier/extractor/simulator also support target gates, controlled phase, source protection and broader layouts. | Emitted subset has a cleanup obligation; the larger raw-only vocabulary is additional debt. Do not expand it for hypothetical importers. Investigate migration to explicit circuits with checked cleanup evidence, without treating a name or unitarity as zero-return evidence. No equivalence or migration is implemented yet. |
| `CertifiedCompute` and retained `Contract` actions | [Certified lowering](../src/frontend/compile/lower/certified.rs) and [function contracts](../src/frontend/compile/lower/function_contract.rs), and [M1 operations](../src/frontend/compile/operations.rs) with the [meaning adapter](../src/contract/meaning.rs); independent evidence checks | Keep exact actual/logical binding and dependency checking. A convenience form may disappear only when these obligations are represented and checked elsewhere. |
| Preparation, observation, ownership structure, lifts, classical operations and branch phis | [Primitive](../src/frontend/compile/lower/primitives.rs), [expression](../src/frontend/compile/lower/mod.rs) and [branch](../src/frontend/compile/lower/branch.rs) lowering; M1.1-A emits Init0/Join/Split/MeasureZ/Discard; raw verifier and execution/extraction where applicable | Emitted today. Retain their resource, instrument and ordering obligations; external physical IDs or LLVM control flow alone do not establish them. |

**0.1.8 producer continuation:** [n-ary tuple syntax](syntax-v0.md#authoring-forms-added-in-product-018)
folds to existing binary AST nodes; basis parameter patterns use the existing
finite label binder. Their tables flow through the same lift/computed/meaning
producers above. No IR constructor, verifier rule or compatibility-debt row is
added or removed; this is source convenience, not a reduction of the trusted
acceptance base.

**0.2.0 tuple correction:** the [type contract](type-system.md) supersedes that
left-folding source rule. Public AST tuple nodes now retain immediate fields;
finite evidence adds a canonical n-ary `BasisType::Tuple` alongside binary Pair.
The [transport](machine-interface-spec.md) preserves this distinction and checks
it against independent requests. Existing lifts, ports and split/join implement
explicit conversions; no raw quantum instruction is added. This is a breaking
source/AST/evidence extension, not a reduction of the trusted acceptance base.

**0.2.0 typed layout component:** the [Lean checker](../lean-kernel/QleisliKernel/Layout.lean) is
an experimental consumer of explicit complete type/owner/axis descriptions.
It checks permutation and request binding without a new finite RawOp variant.
It is not a source producer, QIRF replacement, production authority transfer or
reduction of the current Rust acceptance base. The [shared typed-call
component](../lean-kernel/QleisliKernel/LayoutDag.lean) now consumes layout DAGs with explicit
adapters and independent entry requests. It has no source producer and does
not connect general gate or encoding rules yet. The subsequent [combined
phase/layout consumer](../lean-kernel/QleisliKernel/PhaseLayout.lean) adds sparse controlled dyadic
phases to these typed graphs, with actual normalization/composition proofs.
It still has no source producer, finite-leaf adapter or production authority;
this does not reduce the current Rust acceptance base.

**0.2.0 finite transport:** the [QIRF decoder](../src/interchange/mod.rs) is now an external producer for every frozen finite constructor. It reconstructs evidence with the existing exact checker and rechecks raw programs; it does not make the raw-only convenience variants desirable compiler targets. Their compatibility debt remains. The new trajectory sampler shares numeric execution code but adds no evidence-acceptance rule or trusted-core reduction.

**0.1.9 review continuation in 0.2.0:** finite closed static transforms now
compare emitted circuits with independently extracted verified-IR meanings
through the existing matrix equation checker. Sharing inversion/basis helpers
and source-storage accounting does not remove an IR variant or acceptance rule.
The [review record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/reviews/v0.1.9-followup.md) bounds this check to six bits and
distinguishes its new capacities from a general source-preservation proof.

This is an initial constructor-family inventory, not a proof of complete
frontend coverage. Review it when adding an emitter, core constructor or
external adapter; tests and anticipated future callers are not production
emitters. The raw-only forms are a first visible deviation from the discipline,
not an endorsed target for the future compiler core.

**Implemented internal step:** [the private compatibility adapter](../src/ir/compat.rs)
maps a verified `UnitaryStep` to the existing `CircuitStep` vocabulary. The
simulator attaches the outer control and uses its common circuit executor,
removing the separate numeric interpretation of four qif-arm variants. Primitive
monomial/scalar actions execute in place, preserving the existing state-vector
allocation and execution-step limits. Public IR and verifier acceptance are
unchanged. The independent exact extractor does not use this adapter, preserving
a separate comparison path. This reduces duplicate execution semantics, **not
the trusted evidence-acceptance base**.

The next core reduction needs a complete migration contract before implementation:

1. Select the smaller versioned core vocabulary and spell out the old-to-new
   ownership, phase, effect, layout, limit and diagnostic mapping. Retain a
   bounded legacy frontend/adapter outside the checker for supported raw callers.
2. Treat the adapter's output as untrusted and check it independently. Reject
   malformed old inputs rather than repairing aliases, invalid indices or
   missing owners into accepted core IR. State translation correspondence
   separately; core validity alone does not prove the adapter preserved meaning.
3. Rebind or invalidate evidence for transformed IR. Preserve zero-width
   ownership, branch coverage, cleanup and dependency identities. Exercise
   independent exact operators, entangled references and negative raw fixtures.
4. Only after migration and consumer coverage remove obsolete verifier and
   evidence-extractor cases. Record the actual trusted rules removed. Do not
   count file moves, numeric sharing, or deleting tests as trusted-core reduction.

These steps require MINOR when they break public IR/API contracts or reduce
specified capacities; compatible additions follow the PATCH policy.
Keep the reference executor during external-backend development. The later [M1.1-A adapter work](interop-m1.1.md) uses these existing rules.
Neither step establishes a general translation proof, a minimal kernel or M2 hierarchy.

## Initial implementation slices

Every implemented row needs a complete English contract for signatures/formats,
limits, diagnostics and migration. [M1.1-A](interop-m1.1.md) supplies it for the
bounded OpenQASM direction and QIR output; the remaining rows are future gates.

| Slice | Initial scope and obligation removed | Evidence and acceptance boundary |
| --- | --- | --- |
| Python host binding | Wrap the existing Rust compiler, verifier and exhaustive reference executor with immutable checked handles and structured exceptions. Later expose X4 sampling/trials. Users need no Rust caller or CLI-output scraping. | Calls use the same Rust checks; no Python Boolean or unchecked constructor creates a verified handle. Distinguish a distribution from sampled shots. Test FFI ownership, error translation, limits and wheel installation. |
| OpenQASM 3 import/export | Start with fixed registers, a declared exact gate set and terminal measurements. Load an existing circuit rather than rewriting its gates in `.qli`. | Specify a versioned subset, standard-gate definitions, initialization, wire/result ordering and terminal disposal. Reconstruct ownership and verify every imported operation. Reject unsupported source with locations. |
| QIR Base import/export | Start with a declared Base Profile/QIS combination. Export first to establish target conventions, then import independently produced fixtures in the same slice. | Pin a QIR revision and compatible LLVM reader/writer versions; check profile flags, entry points, instruction/call signatures, resource IDs, QIS meanings and output records. LLVM verification and Qleisli verification are both needed. |
| Adaptive interoperability | Later support the selected finite measurement, reset, Boolean feedback and post-measurement reuse fragment. | Specify instrument-preserving resource translation and target capabilities first. Test entangled references and selected/unselected branch behavior. A bounded subset is not full Adaptive Profile or full OpenQASM 3 support. |

PyO3 with wheel tooling is a binding candidate, not an adopted dependency or
Python-version decision. Keep Python and LLVM dependencies outside the small
default verification core. Evaluate PyQIR as an optional QIR reader/writer
bridge before implementing another LLVM parser; it is not the independent
Qleisli semantic checker. Package installation must not require users to build
LLVM; unsupported wheel platforms receive an explicit support statement.

## Translation obligations

1. **Untrusted input.** Importers produce raw artifacts. Reading a file never
   executes its LLVM, `extern` functions or calibration code. Imported gate
   names, annotations and claimed capabilities are not evidence. Validate
   allowed declarations and definitions against a pinned gate/QIS contract;
   reject unknown or redefined intrinsic meanings. Bound parsing, expansion
   and graph traversal before allocation, cloning or recursive processing.
2. **Physical identifiers versus ownership.** Track external qubit identifiers
   separately from fresh logical tokens. Every operation consumes and returns
   the appropriate owners; aliases do not create new owners. Imported circuits
   do not automatically acquire `.qli` type trees, logical encodings or a
   requested algorithm contract. Use an explicitly specified flat interface
   or separately validated typed metadata, never infer it from a request.
3. **Measurement and reuse.** Current `measure_z` consumes its owner, whereas
   foreign programs may continue using the measured physical qubit. The initial
   terminal-measurement subset avoids this mismatch. A later adapter must
   either reject reuse or specify fresh ownership with the same conditional
   post-measurement state; it cannot resurrect the consumed token or always
   replace the state with zero. For ideal Z measurement, preparation of a fresh
   `|b>` conditioned on result b is a candidate instrument-equivalent translation,
   requiring a separate correspondence check including all reference systems.
4. **Phase and angles.** Preserve global phase through controllable subroutines
   and gate modifiers. Do not substitute Rz and a phase gate using equality only
   up to global phase. The first exact importer may accept only the existing
   supported angle/gate fragment. Decimal angles must not be rounded into exact
   evidence. M2 dyadic phases and approximate synthesis have separate contracts;
   export to a floating parameter cannot claim exact preservation without an
   exact target expression or declared approximation/error treatment.
5. **Observation and output.** Preserve initialization, measurement bases,
   classical output order, reset semantics and hidden outcomes. Foreign terminal
   disposal must lower to explicit observing discard under a stated root
   contract. It never grants pure auxiliary release. Open quantum outputs
   require an explicit interface and are outside a closed Base entry point.
6. **Unsupported constructs.** First profiles reject dynamic allocation,
   unbounded/data-dependent loops, arbitrary classical arithmetic, unknown
   external calls, pulse calibration and timing requirements. Later support
   needs its own rules. A backend lacking required feedback, gates or output
   capabilities must diagnose the mismatch, never silently erase it.
7. **Exported assurance.** Report separately IR validity, a checked requested
   meaning, and established translation correspondence. Ordinary external
   files do not carry all Qleisli evidence. A companion artifact may preserve
   typed IR/evidence and exact output binding, but must be checked; a hash is
   only identity metadata. Changed external IR invalidates its binding. General
   foreign-frontend/backend correctness remains a separate proof obligation.

The planned **QIRF** JSON formats named in [machine interfaces](machine-interface-spec.md)
mean `qleisli.finite-ir`, not QIR Alliance LLVM IR. Keep their existing identities
and acceptance gates; use distinct names and version fields in user-facing
format selection. A QIR/QASM import is not a QIRF round trip.

## Required evidence and scheduling

Implement the Python finite-core binding and bounded OpenQASM slice as early
M1 entry points. Implement QIR Base output/input next; adaptive support follows
its instrument specification. These slices can precede operation parameters
and M2 sizes. They do not replace N1–N6, X1–X6 or H1–H5, and do not delay R14.

Before shipping, require independently produced import fixtures and independent
target parsing/profile checks, not only exporter-to-importer round trips. Cover
Bell correlations, controlled scalar phase, reversed bit/results order,
unknown gates/calls, wrong QIR attributes/IDs, malformed files, limits and stale
evidence. Adaptive support additionally needs reset/discard, reuse of a measured
qubit and entangled-reference instrument cases. Numerical output histograms
alone do not validate an open component's phase or retained state.

Verify Python error/result equivalence against Rust, fresh sampling per shot
once X4 exists, and clean-environment wheel installation without external
compilers. Record backend/device execution separately from local simulation.
Before selecting dependencies, check licenses, binary redistribution notices
and the existing Rust 1.85 minimum; any required toolchain change needs an
explicit compatibility decision.

## External semantic references

- [QIR specification](https://github.com/qir-alliance/qir-spec),
  [Base Profile](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Base_Profile.md)
  and [Adaptive Profile](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Adaptive_Profile.md).
  Pin the actual revision when implementing a target; measured-qubit reuse must
  satisfy the ownership/translation obligations above.
- OpenQASM 3.1 [quantum instructions](https://openqasm.com/versions/3.1/language/insts.html)
  and [gate modifiers/global phase](https://openqasm.com/versions/3.1/language/gates.html).
  M1.1-A supports a terminal common 3.0/3.1 subset with explicit initialization.

Current component implementation and producer debt are recorded in the
[inventory above](#ir-reduction-and-the-trusted-boundary) and the
[generated rule inventory](rule-inventory.md). Proof modules and retained
fixtures carry their detailed evidence; none enables production hierarchy
acceptance or an external schema without its binding gates.
