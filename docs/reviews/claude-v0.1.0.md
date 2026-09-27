# Review of the user-supplied Claude v0.1.0 report

Status: **implementation review and compatible maintenance changes**
(2026-09-27). The supplied report describes independent use on Ubuntu and
Rust 1.85.1. Those external runs were not reproduced as such here; the local
checks below cover the reviewed working tree before version selection, when
the product version was still 0.1.0. These changes have since been assigned to
the pending [0.1.1 release](../releases/v0.1.1.md), as recorded in the
[changelog](../../CHANGELOG.md). The validation below remains the review's
historical evidence, not a completed 0.1.1 release check.

The [imaginary Qleisli 1.0 corpus prerequisite](../release-milestones.md#pre-v020-imaginary-v1-code)
remains unmet. This review fixes or tests the existing finite implementation;
new source forms and incompatible public API/IR changes remain later design
work. Finite tests are not a general compiler-soundness proof.

## Findings and disposition

| Report item | Code/specification check | Disposition |
| --- | --- | --- |
| 1. Repeated source snapshots exhaust compilation work | Reproduced both repeated calls with a comment-heavy source and five nested contracts with an unrelated 100 KB comment-only module. Each failed with `Limit` before the change. | Fixed redundant cache-hit comparisons and charges. The private cache belongs to one immutable project and fixed checked dependencies. Copies are charged once per new pair; full project snapshots and external exact `check_binding` remain. A dependency-closure digest is not needed for this correction. |
| 2. `run` loads unimported `.qli` files | Confirmed, and required by the published [module specification](../standard-library.md): both checking and execution check every declaration in the supplied root. | Retained. Reachability-only execution changes the accepted project boundary and requires a future specification/compatibility decision. Scratch or imaginary code should be outside an executable source root. |
| 3. Legacy raw-IR forms are not emitted by the frontend | Confirmed for `QuantumIf` and its older unitary-step representation. They remain accepted public raw-IR inputs, with verifier/executor coverage. | Retained. Removing public variants is potentially breaking; input normalization also needs a meaning/cost review. Frontend non-use alone does not establish dead code. |
| 4a. Certified projection has no numerical leakage alarm | Confirmed: direct execution previously projected the auxiliary without measuring the removed numerical weight. | Added a relative-weight alarm using existing `InconsistentVerifiedIr`, including non-finite weights and small-probability components. Exact certification remains the sole permission to release; numerical outputs are not renormalized. |
| 4b. Contract execution substitutes private cleanup regions | Confirmed, and explicitly permitted by [FC-EXECUTE](../function-contracts-v0.1.md). The report's earlier description of always running the full physical implementation is too broad. | Clarified the implementation comment and added direct physical-witness versus extracted-contract execution tests. A full physical execution mode under inverse/control would need a separate path and qubit/work-limit contract, so it is not introduced here. |
| 4c. Generated differential coverage is missing | Existing analytical regressions did not supply the requested generated comparison across interpreters. | Added deterministic bounded circuits compared against exact complex amplitudes, plus adjoint/control laws, correlated references, and physical auxiliary witnesses. |
| 5. IR failures point to a function declaration; contract errors lack counterexamples | Reproduced the wrong location for dirty computed regions, including an isolated nested body. | Added private source-path metadata and exact first-differing-entry diagnostics, reusing matrices already computed under the existing budget. Kept public `InvalidIr`/`Project` variants; parse messages now explicitly identify their origin. New enum variants require a compatibility decision. |
| 6. Calls are fully expanded | Confirmed. Existing work/depth limits bound finite expansion. | Shared function/call IR is a later architecture proposal, to be driven by the imaginary-code corpus and its semantics; it is not a compatible repair to the existing public IR. |
| 7. Signed shift and composition invariants | A shift of 127 can form a negative power-of-two factor, but the current maximum denominator exponent is 126. The reported overflow is latent, not a demonstrated misacceptance of current inputs. Constructors maintain the composition basis invariant. | Hardened scaling with `checked_pow`, added signed/denominator boundary regressions, and made the invariant explicit with debug assertions. Existing arithmetic limits remain. |

## Additional comments from the report

- Tiny positive probabilities are retained intentionally by the
  [numerical execution contract](../ir-prototype.md#reference-execution).
  Thresholding CLI output could hide valid small outcomes. README now makes
  this behavior visible.
- CLI output follows classical result-tuple order, not an implicit universal
  integer convention. The QPE examples return phase bits low bit first.
  README and `factor_from_phase` documentation now explain that displayed
  phase bits `100` represent integer 1. A new public conversion helper is a
  library addition for a later release, not part of this maintenance change.
- The two shift/bitwise expressions and the redundant compiler-impl lifetime
  identified by inspection were clarified. The MSRV CI job now runs Clippy as
  well as tests. Rust 1.85 is not installed locally; adding CI coverage is not
  a claim that its remote run has passed.
- Register patterns, in-place call sugar, inline operation branches, grouped
  imports, additional standard gates/measurement APIs, parameterized proofs,
  and generalized angle/error contracts are future design inputs. Each needs
  its own specification and lowering argument; calling it syntactic sugar
  does not itself establish semantic preservation. The corpus prerequisite
  applies before implementing these v0.2.0 features.

## Local validation

On macOS with Rust 1.98.1, using a fresh Cargo target directory:

- `cargo test --all-targets`: **257 passed**, including four source-diagnostic
  tests, the cache regression cases, exact arithmetic/counterexample checks,
  and four simulator unit tests containing 96 generated circuits and 16 raw
  physical-witness comparisons. The Linux-only CLI test is not run here.
- `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings`: passed.
- `python3 scripts/check_docs.py`, all **14** documentation-checker tests,
  and `git diff --check`: passed.
- CLI execution of `examples/function_contracts` and
  `examples/semantic_contracts`: both returned `101: 1.000000000000e0`.

The cache and diagnostic-location regressions were observed failing before
their respective fixes. Numerical differential comparisons use tolerance
`1e-12` and supplement, rather than replace, exact evidence checks. No new
compiler-soundness theorem is claimed. Rust 1.85 and the modified remote CI job
were not run locally. Lean sources are unchanged; Lean build and axiom audit
were not rerun for this Rust maintenance change. No version bump, commit,
tag, push, or release publication is part of this review application.
