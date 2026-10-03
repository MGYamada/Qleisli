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

A substantive proved Lean backend remains required. The
backend execution policy
forbids project `unsafe def`, `@[implemented_by]`, `@[extern]` and `partial def`,
with source and compiled-declaration CI in addition to axiom auditing. Private
and generated helpers are included. External search is not an exemption for
backend implementation or a substitute for its actual-transformation proofs.
