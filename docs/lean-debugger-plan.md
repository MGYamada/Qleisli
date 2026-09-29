# Lean-assisted mathematical debugging

Status: **future work adopted on 2026-09-29; not implemented**. Target a future
0.x.0 milestone as the Lean checking and translation interfaces mature; no
specific version or date is selected. This is a tooling continuation beyond
the current Rust verifier's diagnostics, alongside [K0–K4](lean-kernel-migration.md)
and [QLT](qlt-design.md), not another quantum language or acceptance kernel.
It adds no gate to 0.2.0, 0.2.1, S05-C1–C5 or PR-C1–C4/V1-C1–C5.

## Intended author experience

Connect an independently stated expected meaning to the actual IR, contract
equations, proof obligations and relevant source locations. Explain a failed
check in terms of phase, bit/axis order, effects, encoding or exact auxiliary
return, rather than requiring the author to reconstruct these relations across
host scripts and proof logs. For observing programs, include residual states
and reference correlations, not only the distribution of measured bits.

Initial source material already exists: the [QFT/phase counterexamples](../tests/fixtures/qlt_design/README.md),
the [QPE dephasing and controlled-phase cases](../tests/fixtures/lean_qpe_instrument/README.md),
and [finite diagnostic regressions](../tests/repair_diagnostics.rs). Reuse their
original sources and mathematical expectations. They are design inputs, not
evidence that a debugger exists or has improved authoring performance.

A report should identify the requested contract, actual artifact and dependency
revision, failed obligation, available witness, evidence status and bounded
checking work. Link to a source span only when its provenance is available;
otherwise identify the IR node/rule without inventing a source location. A
rejected proof step localizes an evidence failure, not necessarily the first
semantic bug in the program. Minimal counterexample search is optional and
bounded; do not promise a unique or smallest cause.

## Diagnosis and evidence

Keep the diagnostic category separate from whether its supporting witness has
been independently checked by Lean. The following are design categories, not
adopted CLI/JSON variants:

| Category | Required interpretation |
| --- | --- |
| Contract mismatch | Exhibit a checked witness to failure of the requested mathematical claim in the declared profile, such as unequal exact operator entries. Identify phase, basis order and entry premises. A finite witness refutes that claim; it is not a proof about every other input. |
| Evidence missing or invalid | A required theorem, premise or derivation cannot be validated. This does not imply that the implementation's mathematical claim is false. |
| Invalid source or IR | Ordinary type, ownership, effect, structure or binding checks reject. Report that rejection; do not execute unchecked quantum IR to obtain a more attractive diagnosis. |
| Undecided | A resource limit, incomplete proof search or inconclusive enclosure prevents a decision. Absence of a witness proves neither equality nor inequality. |
| Unsupported or tool error | The domain/rule is unsupported, input is malformed, or evaluation/transport fails. Do not turn failure into a mathematical conclusion or partial success. |

For exact contract comparison, a future witness checker must establish a result
such as `checkMismatch(p, C, w) = true -> not (denote(p) satisfies C)` under the
profile's explicit validity and entry premises. This is a theorem target, not
an existing function or a consequence of the acceptance soundness theorem:
failure of `verify` alone does not prove a semantic mismatch. For encoded pure
contracts, inspect the declared equation `U E_in = E_out u`; for instruments,
compare the corresponding maps with residual targets and references. Preserve
phase under control and distinguish equivalent Kraus representations.

## Trust and integration

The [fixed trust boundary](../TRUST_BOUNDARY.md) is unchanged. Source maps,
search, minimization, UI explanations and LLM repair proposals are untrusted
tooling. A Lean-checked diagnosis needs a witness checker proved against the
actual IR semantics and independent replay bound to the exact artifact,
requested contract, dependency identities, coefficient domain, basis/axis
convention, profile/version and any error metric. Neither a theorem name nor
a Rust/LLM explanation supplies that evidence. Native execution assumptions
remain explicit. Any new executable evidence checker stays Mathlib-free;
mathematical interpretation proofs remain in the separate proof package.

QLT supplies mathematical comparisons and test cases; the debugger explains
and navigates their failures and production proof obligations. A Rust QLT
result retains its existing assurance label until a separate Lean certificate
has been checked. A debugger report never issues production acceptance,
weakens a contract or enables an unsupported schema. Nonphysical introspection
stays outside `.qli`. Proposed repairs must pass normal source/IR verification
and the applicable independent semantic tests again.

IR-level diagnoses can precede source-to-IR correspondence. Until source-map
and translation obligations are checked, distinguish an IR witness from a
proved explanation of source semantics. Later K4 integration should trace
backend transformations and their preservation obligations to the actual
emitted artifact under its exact or explicitly approximate contract.

## Staged work and acceptance experiments

1. Specify bounded structured reports and provenance for supported Lean
   obligations; connect actual rule/node identities to current source diagnostics.
   Freeze any public API/format only after a concrete source/repair experiment.
2. Add exact mismatch witnesses with independent Lean replay, then QLT result
   navigation and instrument/reference diagnostics as their evaluators and
   correspondence proofs become available. Keep their dependencies explicit;
   initial obligation reports need not wait for all QLT functionality.
3. During K4, extend to source/optimization/backend preservation failures and
   bounded repair feedback for human and LLM authors. Later approximate
   diagnostics need the same certified norm/enclosure contracts as QLT.

Acceptance must pair each broken example with a corrected one: inverse-QFT
sign or missing reversal; a phase difference exposed by control; invalid
auxiliary cleanup; and equal phase marginals with different target/reference
maps. A valid implementation with absent or malformed evidence must remain
distinguishable from a witnessed mathematical mismatch. Mutate artifact,
contract, dependency, source-map and witness identities and reject stale or
forged certified reports. Exercise deterministic replay, malformed input,
bounded traversal/output and exhaustion without success or false refutation.

Follow the [code-driven method](code-driven-development.md): preserve first
sources, actual diagnostics, repairs and independent references before
implementation, then record the manual tracing removed and checking cost.
The present record adds no new source syntax, debugger command, theorem or
runtime. Future release selection follows [compatibility policy](versioning.md);
compatible preparatory additions may ship in PATCH, while breaking interfaces
require a MINOR migration. Existing algorithm and proof milestones retain priority.
