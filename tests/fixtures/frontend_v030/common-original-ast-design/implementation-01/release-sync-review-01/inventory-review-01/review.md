# Release inventory review of the frozen common-original-AST unit

Status: proposal only. No active inventory, source, test, documentation, gate or
constitutional record was changed. The inspected helper's `public_surface`
function was used solely for metadata extraction; its validator/main, builds,
tests, CLI/native processes and stored command metadata were not executed.
Root's latest attempt 08 and subsequent final validation are separate facts.

The current active inventory is SHA-256
`5e5bc6ae29bcb0a7355a9a247dfba57e824b39aab26a615a2ced8ba6963a19e7`.
All 20 changed existing source rows have exact matching Git HEAD baseline bytes.
The extraction records every changed row and exact method spelling in
`surface-review.json`; no published enum declaration/field changed. Seven new
common-checker files need explicit `source` coverage rows, making 261 sources
while preserving every original row.

## Exact lexical-surface differences and effective visibility

| File | Extracted changes | Effective external API |
| --- | --- | --- |
| `effects.rs` | Adds `storage_cells`, `inferred_with`, `merge`. | Methods belong to `pub(super) BodyEffects`; the public module does not expose this type. Exported `FunctionEffect::{inferred,asserted}` is unchanged. |
| `resolve.rs` | Removes `modules`; removes private Profile argument from `imports`; adds `new_budgeted`, `imports_budgeted`, `set_scope_budgeted`. | `resolve` and Resolution/DefId are private frontend implementation. |
| `resolve/locals.rs` | Removes uncharged `Index::new`, `Table::bind_globals`, `Forest::insert`; adds `Index::new_budgeted`, `take_occurrences`, budgeted occurrence insertion and `Forest::from_occurrences` with shared Arc<Table>. | All affected types are `pub(in crate::frontend)` in private resolve; authoritative Table identity is retained, not cloned. |
| `sized/linear.rs` | Replaces uncharged variable/arithmetic/Context/solver wrappers with explicit budgeted equivalents; adds constant/copy/storage accounting methods. | The module is `pub(super)` and Linear/Context are restricted to frontend. No external size-solver API was removed. |

The inventory scanner records literal `pub fn` methods regardless of effective
containing-type/module visibility. Its refusal is appropriate review friction;
it is not evidence of an external Rust signature break. Current external
frontend, sized accessor/binding, effect-fact and SourceType signatures and all
MAX_/DEFAULT_ constant rows have unchanged extracted spelling. Source behavior
has intentional ordinary #32 migrations even though those signatures stay fixed.

## Capacity and checking migrations that require explicit prose

- One fresh 1,000,000 common source-work budget now precedes eligibility in both
  consumers and covers complete originals, interfaces, resolution/lexical maps,
  type/owner/effect/dependency work and real copies/solver contexts. It does not
  replace or lend the separate finite 1,000,000 lowering/evidence budget.
- Selected loading now counts all four actual ordinary bundled modules inside
  the existing 64 total slots, leaving 1..60 supplied locals. All four sources
  also count toward its 1 MiB aggregate; its 65,536 bytes/module and 10,000 tokens
  per module remain. This exact migration is recorded at contract-01 lines
  101..104; it is not a silent numeric constant change.
- The 4,096 type-cell/depth-64 rules remain. Selected retains 16,384 live-scope
  type cells; finite explicitly does not gain that scope ceiling. Original Q
  owners, including zero-width owners, still count and preserve exact tree tags.
- Selected closed-interface/binding validation now has a separately charged
  100,000-work allowance before concrete eligibility. Concrete elaboration keeps
  100,000 aggregate cells, 1,024 calls/folds, depth16/traversal64 and 10,000 steps;
  new provider walks and all copy work include Q-constructor work while storage
  remains Q-transparent. Closed Basis8-bit and finite Basis12-bit limits stay
  adapter capacities, not generic source-kind equivalence or native widening.
- i128 checked linear arithmetic, 32 variables, 64 alternatives, 4,096 retained
  constraints and the 50,000 solver-generation cap remain. The original
  460-premise case now genuinely hits the earlier shared 1,000,000 work cap; it
  cannot be advertised as a direct test of the 50,000 solver cap.

The proposal updates `source-structure` and `sized-source-preparation`, adds a
separate common-work capacity row and clarifies the existing source boundary/
coverage group. It changes none of the inventory authority/release/enums,
comparison/corpus baseline pins, native packaging, other groups or boundaries.
Native checks, evidence gates and pending source/provider/transformation duties
are not discharged by this metadata update.

## Meaningful existing checks and their limits

`tests/body_effects.rs` covers body-derived and transitive effects, all ordinary
stdlib bodies, false annotations, zero/dead branches, access and immutable effect
metadata. `tests/source_judgments.rs` independently exercises type/owner/Basis/
computed judgments and original diagnostic locations; `shared_resolution.rs`,
`project.rs` and resolver/local unit tests exercise private visibility, import-
only versus real dependency cycles and lexical identities. `source_collection.rs`
checks source errors before projection and ordered parse/duplicate diagnostics.

`sized_source::symbolic_capacity_errors_keep_obligation_spans_and_causes`
retains exact early1M/overflow/32-variable/64-alternative failures.
`sized_linear_seeded::seeded_generic_size_implications_agree_with_concrete_enumeration`
uses independent bounded integer enumeration, not the solver as its own oracle.
Existing concrete-elaboration, recursion/call, unused closed-binding and static-
expansion tests retain actual capacity refusals, owners and small positive
controls. These are existing test definitions, not newly claimed terminal passes.

The existing module-count test refuses65 supplied modules; it does not separately
pin the new60/61 boundary. The inspected tests do not constitute an exact boundary
oracle for every100,000 preflight charge or direct50,000 solver exhaustion after
the new preceding common cap. Do not invent those passes in an inventory report.
Do not run newly generated maximum cases to fill this gap.

## Application barrier and scope correction

`PROPOSED-inventory.json` is not active and has not been validated. Root must
review the exact proposed prose/rows and bind application to actual terminal
validation and the then-current exact source bytes. New final source changes
invalidate this frozen candidate. Full CI/release/source-preservation/constitutional
guarantee/Issue completion does not follow from source inventory synchronization.

The first extraction's key `removed_inventory_paths` means paths outside its
automatic discovery domains, not removed files. All36 extra lean/scripts paths
still exist; the proposal preserves them and every other original inventory row.

Review independence is limited: I authored the finite consumer, lexical cleanup
and concrete runtime helper among these source changes. This inventory/surface
review is not an independent semantic oracle for my own implementation. Separate
root/core reviews and actual tests supply their own evidence.
