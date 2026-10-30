# Trust boundary

Fixed architectural policy, adopted 2026-09-29, with the explicitly dated
2026-09-30 proof-obligation amendment below. The trusted/untrusted partition
remains unchanged. Proof status and execution assumptions
remain explicit; this policy does not declare the planned proofs complete.

1. **Trusted:** Lean's proof kernel; the correspondence between the declared
   gate set and physical hardware under its stated assumptions; and `std`'s
   mathematical specifications as the intended meanings. Library implementations
   must still satisfy those specifications through ordinary verification.
2. **To prove:** the Qleisli Soundness Theorem,
   connecting accepted IR to its requested meaning, and the
   Physical Realizability Theorem,
   connecting that meaning to the actual synthesized gate implementation; and
   the Resource Safety Theorem,
   added **2026-09-30, to prove**, establishing finite statically computable
   resource upper bounds and their preservation through compilation.
3. **Untrusted; reject unless independently validated:** frontend output,
   including proposed IR and evidence. Human or LLM authorship confers no
   authority; failed validation cannot be bypassed.

## Reference specification review (2026-09-30)

The review clarifies item 1's specification assumption: a soundness theorem is
relative to its reference semantics. Lean checks the proof against definitions;
it does not decide whether those definitions express the intended quantum
operation. Gate action, complex interpretation, encoding, instruments and
resource models therefore require explicit human specification review. This
does not trust a checker implementation or enlarge its acceptance authority.

Reference semantics must be small, stable modules independent of acceptance
code. Checkers import those definitions; their normalization result or the
producer's claimed meaning must not define the reference. Semantic changes need
equations, premises, counterexamples and a recorded review. Author/AI identity
and a successful axiom audit do not substitute for that review.

The first separation is [cyclic phase-word semantics](lean-kernel/QleisliKernel/Semantics/PhaseWord.lean):
`step`, `execute`, `run` and summary action retain their public names and meanings,
while [PhaseWord](lean-kernel/QleisliKernel/PhaseWord.lean) imports them for checking.
CI forbids modules under `QleisliKernel.Semantics` from importing checker or
transport modules. Other existing operational/path/complex definitions still
need staged separation and independent review; this first move does not claim
that all reference semantics have been isolated or formally justified.

The [complex instrument reference](lean/Qleisli/Semantics/Instrument.lean)
separately defines zero insertion, full complex evolution and readout branches.
CI also forbids `Qleisli.Semantics` modules from importing project checkers or
transport. Its actual-IR conformance theorem retains finite-reader/native
premises; the mathematical definition still needs human review before production
adoption. This does not transfer production acceptance authority.

## Resource Safety amendment (2026-09-30)

**Explicit post-adoption amendment requested by the user: to prove.** Add
Resource Safety as the third pillar, alongside semantic Soundness and Physical
Realizability. The resource semantics must bind
finite, statically computed safe bounds to actual programs and preserve the
resource contract through lowering, optimization, synthesis and emission.
Scope, input/size premises, gate set, scheduling and all permitted branches
must be explicit; resource-model and compiler correspondence are proof duties.

This adds to item 2's obligations. It does not add a trusted cost estimator,
optimizer or backend, reclassify untrusted proposals, or assert a current proof.
Proposed resource annotations and certificates require independent validation;
current work/step limits and ownership checks are not this theorem. Existing
production authority and its migration gates remain unchanged. The 2026-09-29
adoption date is retained rather than backdating this extension.

## Realizability workspace clarification (2026-10-01)

The 0.2.3 review exposes a same-wire synthesis obstruction, recorded in
[Issue 120](https://github.com/MGYamada/Qleisli/issues/120). The
theorem contract
therefore binds target gate set, admitted synthesis workspace, exact phase,
zero return and physical-layout correspondence. Quantitative resources count
backend workspace too. Semantic unitarity remains independent of a target's
realizability judgment. This clarifies the future proof obligation; it adds
no trusted synthesizer, verifier restriction or current proof claim.

## Pipeline migration and execution policy

The pipeline migration policy,
adopted on 2026-09-29, preserves this partition while moving passes between
Rust and Lean. Always check the IR at their boundary; extend the verified
downstream segment only through proved or independently validated actual
transformations. The boundary's pipeline position may move, but its checking
obligation and trusted assumptions do not change merely because code moves.
Current proof coverage and transitional assumptions remain explicitly recorded.

### Single-verifier implementation amendment (2026-10-03)

[Decision #276](https://github.com/MGYamada/Qleisli/issues/276) adopts a one-time
breaking v0.2.9 migration to one production acceptance implementation in
Mathlib-free `lean-kernel/`. A fresh native decision binds a private accepted
handle to immutable artifact/request bytes. Rust proposal generation, decoding,
diagnostics, simulation and packaging remain outside semantic acceptance.
Replace each legacy path before removing it; absence, incompatibility or failure
of the selected checker must never fall back to Rust acceptance.

This changes implementation-transfer scheduling, not the trusted partition or
proof completion. S05-C1–C5 remain open; full supported-profile Soundness and
review remain v0.5.0 work. Native compiler/runtime, decoder and execution
correspondence assumptions stay explicit. Keep existing proofs, source/compiled
audits and replay until compatible replacements exist. External schema gates
remain unchanged. The [ordered cutover criteria](https://github.com/MGYamada/Qleisli/issues/276)
govern implementation and release readiness; adopting them does not complete it.

External synthesis search
may remain outside Lean permanently. Its circuits and witnesses are untrusted
proposals; the planned Lean `LeafRealizer` checker must establish their bound
realization contracts before use. Neither the oracle nor all Lean program code
is added to the trusted assumptions. This applies the de Bruijn criterion per
pass without requiring every search algorithm to migrate.

### Per-invocation execution binding (v0.3.0-beta, #362)

The QLV3 native envelope binds the actual retained Rust execution data to
Lean's freshly decoded and checked data by exact QDV1 byte comparison. It
covers finite graphs and dependency caches, typed finite contracts and both
instrument roots, original raw caller aliases, and all five hierarchy modes'
retained plans. An inspection-only decision cannot authorize an execution
view. The old external protocol is rejected; internal original QLV1 and
hierarchy payloads still pass their existing independent checks.

This removes the assumption that the two readers agree on the submitted
decoded data without a per-invocation check. Remaining assumptions are that
the Rust view walkers describe every field actually consumed by execution,
that the retained compared objects are those consumed, and that native
compilation, transport and numerical simulation implement their definitions.
Tests exercise these links; the Rust walkers and runtime are not proved.
Hierarchy bridge construction, source lowering, emitted target preservation,
and general hierarchy operator semantics retain their separate obligations.
QLV3 success is formally connected to the original decoded-root ownership
and classical-scope properties; this preserves their admitted scope and does
not admit a new guarantee or discharge broader QS, PR, RS or EXACT duties.

The internal `finite-carrier-pure-v1` mode additionally compares both ordered
typed owner forests and the independently requested exact logical matrix with
their retained Rust objects. Lean reconstructs supported nominal declarations
from the original source rows and checks code Gram/body equations using the same
QIRF dependency and Raw gates. A fresh execution-only decision binds its private
handle; inspection/caller frames and ordinary requests cannot substitute for it.
Its independent type reader follows original explicit imports and public
reexports, retaining canonical identity, category and visibility. Existing field
Nat expressions use exact symbolic arithmetic and original acyclic helpers,
including generic checking of unused/private definitions and ordered premises.
Simultaneous calls are proved against original predicate/body evaluation;
produced templates and caller-supplied success receipts grant no authority.
The helper environment is checked once across all ordered owner forests.
This bounded raw component does not enable ordinary source ADT execution.
The explicit source carrier adapter reuses the common judgment, selected
Builder and Raw emitter, requires an independent exact logical request and
replays retained source steps against the native-compared body. Extra original
source rows are covered only by exact nominal origins after independent type
checking; ordinary checking keeps evidence-only source usage. Uncovered
helper/import-only rows refuse. Its sealed result retains the source graph and
grants no ordinary runtime, inverse or controlled access; original AST-to-step
preservation remains unproved and is reported as such.
Neither declaration lookup nor these scalar checks supply a source-function
preservation theorem, inverse/control access or a new human-admitted guarantee.
All existing source/runtime/target assumptions remain.

The internal `finite-ordinary-root-v2` mode checks ordinary input/result forests.
Lean freshly reads the original selected declaration's parameters, result and
public effect, independently enumerates the entire canonical input domain,
requires exact equality with proposed input rows, and reuses the original Raw
root checks. For every canonical input, its independent ordinary-value reader
checks the complete input storage and every exact reconstructed hidden result
history, including zero-probability histories, against the exact actual SSA maps.
Internal declaration checking requires an original private non-entry function;
exported selection still requires public visibility. Both use this same root
gate and retain their exact selection in QDV; checking does not export a source name.
QLV3/QDV compares that same graph, selected entry, parameter/result forests,
input rows, storage and effect with
the retained Rust objects. No sampled or normalized history subset supplies
acceptance. The program retains the typed result; untyped rechecking refuses.
Actual original parameter/result type queries and recursive record field types
also retain their exact import/reexport paths. These independently checked
paths justify their source rows; global unused-helper checking and arbitrary
module names do not. The private Rust proposal accounts for complete source
path/text bytes and obtains no handle until native relevance and full QDV
comparison succeed. Existing source/work limits remain in force.
This does not prove source-body lowering or numerical runtime correspondence,
admit an external schema or new guarantee, or grant inverse/control access.
Closed-only simulation and sampling inspect retained source parameters as well
as Raw ports, so zero-width ordinary parameters cannot masquerade as closure.
Nongeneric public selected ordinary functions now use the same original-source
emitter and native v2 gate. Their AST/text are borrowed intact for a fresh
complete common judgment and associated indices; cached facts and newly built
indices are never mixed. The returned selected wrapper retains its immutable
instantiation and actual accepted request. Small quantum temporaries use the
same Raw emitter and complete hidden-history checks under bounded producer limits.
Internal ordinary v1 refuses without fallback.

The internal `finite-runtime-root-v2` gate separately retains full mixed runtime
type prefixes and ordered quantum owners. It checks each exact hidden map against
the original input/output codes, including padding leakage and the complete
logical Gram sum. Public effects retain actual observation and logical dimensions.
Its QLV3/QDV walker binds the actual retained graph, source selection, types,
storage and all canonical inputs. The common emitter connects nongeneric project
and selected mixed interfaces to this gate, preserving original AST/text and
zero-width owners. Selected Basis/Nat roots additionally retain original generic
headers, ordered numeric premises, complete named actuals and nominal declaration
sources. Lean independently closes the original signature and binds those actuals
in the retained-object comparison, including unused parameters. Old runtime
request versions reject. Rechecking walks the same retained objects; portable
export cannot erase them. Generic dependencies, operation-formal closure, full
qmatch and nominal finite-table/Meaning consumers remain pending. Exact computation
witnesses supply no source-body,
complex-denotation or numerical-runtime preservation theorem, inverse/control
capability, new guarantee admission or broader QS/PR/RS/EXACT discharge.

### Non-verifier backend implementation scope (2026-10-11)

[Decision #350](https://github.com/MGYamada/Qleisli/issues/350) retires the
v0.3.x non-verifier backend migration schedule. A broader backend implemented
in Lean 4, with proofs checked by its kernel, is a long-term goal with no
selected release. Rust may continue to implement untrusted transformations,
candidate/evidence generation, simulation and experimental output adapters.
The Mathlib-free Lean production verifier remains required; producer language
does not confer acceptance authority or discharge an input/output preservation
or target-realization obligation. Existing QS, PR, quantitative RS and EXACT
requirements and admitted guarantees remain in force.

The Lean execution policy continues to forbid project `unsafe def`,
`@[implemented_by]`, `@[extern]` and `partial def`, with source and
compiled-declaration CI in addition to axiom auditing. Private and generated
helpers are included. These restrictions apply to current verification and
proof code and any future Lean backend. External search is not a substitute
for checking an actual claimed transformation or realization.
