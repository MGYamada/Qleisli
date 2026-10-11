## Target and goal

**Target: Qleisli 0.4.0. Priority: important.**

Refactor the **structure of the standard library** after its semantics have been frozen in 0.3.0.

The release boundary is now explicit:

> **0.3.0 fixes what stdlib operations mean. 0.4.0 fixes how the stdlib is organized.**

Semantic source of truth:
- #167 — freeze stdlib semantics and contracts in 0.3.0

Related:
- #154 — sealed primitive / trusted semantic axiom admission policy
- #53 — later qrate/package organization

## Scope

This issue is strictly about **structure, discoverability, and namespace architecture**.

0.4.0 may change:

- module boundaries;
- namespace hierarchy;
- file/directory layout;
- public re-exports;
- grouping of operations by mathematical family;
- visibility of internal helpers;
- placement of foundation vs derived library APIs;
- naming consistency;
- documentation organization;
- metadata/layout needed by QLT, QDB, QCP, qlidoc, and future qrate tooling.

0.4.0 must **not** redefine the mathematical/effect semantics frozen by #167 merely as part of this refactor.

## 1. Separate foundation and mathematical-library structure

The stdlib should visibly distinguish at least two structural roles.

### Foundation-facing modules

These expose language-level or constitutionally sealed boundaries.

Examples include the modules containing:

- basis-level functions;
- sealed quantum primitives;
- sealed observation primitives.

Their placement must make the trust boundary obvious, but **placement itself grants no semantic authority**.

### Mathematical-library modules

These contain ordinary checked Qleisli definitions grouped by their public mathematical role.

Examples may include:

- arithmetic;
- transforms;
- derived measurements;
- reflections;
- algorithms;
- other future mathematically coherent families.

The exact hierarchy is a 0.4.0 structural decision.

## 2. Retire catch-all organization

Do not keep a generic bucket such as `std::routines` as the default home for unrelated APIs.

Every public operation should have one structurally meaningful home.

The classification rule should be based on the already-frozen public contract from #167, not on incidental implementation details.

## 3. Define mechanical namespace admission rules

For each top-level public module, document a short structural admission rule:

> An API belongs here iff ...

The rule should distinguish nearby modules clearly enough that contributors and coding agents can place a new API without guessing.

This issue may use the 0.3.0 semantic contract as input, but it must not revise that contract.

## 4. Make the trust boundary visually obvious

The refactor should make it easy to tell:

- sealed compiler/kernel primitives;
- ordinary checked stdlib source;
- internal implementation helpers;
- public mathematical APIs.

Moving an item between modules must not change its trust status.

Add regression checks so namespace placement cannot impersonate a sealed primitive boundary.

## 5. Structure for tooling and future growth

The 0.4.0 layout should be usable by:

- QLT;
- QDB;
- QCP;
- qlidoc;
- future qrate/qargo packaging;
- AI/code-agent discovery.

Prefer a hierarchy that is:

- deterministic;
- shallow where possible;
- easy to browse;
- easy to document;
- easy to import;
- stable enough for later stdlib growth.

Do not overfit the hierarchy to the tiny current library.

## 6. Perform one atomic pre-1.0 migration

Because Qleisli is pre-1.0, perform the structural migration atomically.

Update together:

- stdlib source layout;
- imports;
- examples;
- corpus material;
- QLT fixtures;
- documentation;
- metadata;
- tests.

Avoid compatibility aliases unless a concrete migration need justifies them.

## Semantic invariance requirement

Every migrated public API must be checked against the 0.3.0 contract from #167.

The desired invariant is:

```text
old path + frozen 0.3.0 contract
        =
new path + same frozen contract
```

A namespace/file move with a semantic delta is not part of this issue and requires a separate semantic proposal.

## Non-goals

This issue does **not**:

- define or revise stdlib mathematical semantics;
- change exact phase conventions;
- change axis/bit ordering;
- change cleanup obligations;
- change reference-system behavior;
- change observation semantics;
- promote ordinary derived code into sealed primitives;
- begin large-scale stdlib expansion;
- define the final external package ecosystem.

## 0.4.0 acceptance criteria

- [ ] #167 is complete enough to act as the semantic source of truth for current public stdlib APIs.
- [ ] The stdlib has a documented structural taxonomy.
- [ ] Foundation-facing and mathematical-library modules are structurally distinguished.
- [ ] `std::routines` is removed or replaced by deliberately named families rather than retained as a catch-all.
- [ ] Every public stdlib item has exactly one canonical structural home.
- [ ] Each top-level module has a mechanical admission rule.
- [ ] Primitive/derived/internal status is visually and mechanically distinguishable.
- [ ] Imports, examples, corpus material, QLT fixtures, docs, and metadata migrate consistently.
- [ ] Regression tests detect namespace/trust-boundary confusion.
- [ ] Every public migration is validated against the same frozen 0.3.0 semantic contract.
- [ ] The refactor introduces **no semantic delta** to existing public stdlib APIs.
- [ ] The resulting hierarchy is suitable for QLT/QDB/QCP/qlidoc and later qrate growth.

## Design intent

0.4.0 should answer:

> **Given meanings that are already fixed, where should each operation live so that humans and coding agents can find, compose, document, and extend the stdlib cleanly?**

The sequence is deliberate:

```text
0.3.0  semantic freeze
        ↓
0.4.0  structural refactor
        ↓
later   controlled stdlib growth
```

> **Meaning first; structure second.**


## Effect-contract consumer boundary from #315 — 2026-10-05

#315's 0.3.0 implementation exports ordinary checked body-derived principal effects separately from optional upper-bound assertions under Unitary <= Iso <= Observe. The future structural refactor consumes these inferred facts and their retained source/interface identity; it must not recreate a handwritten authoritative effect ledger or infer authority from a new namespace. A wide Observe assertion on a Unitary body does not change its principal class, and a hidden observation body cannot assert Unitary. Exact mathematical Meaning, phase/axis contracts, clean/dirty obligations, access and primitive status remain separate.

Current consumer interfaces are immutable `ProjectEffects::function_effect`/`documentation` (finite whole-project checking with the selected native kernel) and `ParsedProgram::function_effect`/`documentation` (checked sized source premises). Source-only documentation remains explicitly unverified. A move must rerun ordinary checking on the migrated source and compare these principal/assertion facts plus #167's mathematical contracts; cached facts cannot be rebound to changed source or substituted for fresh native checks. Ordinary stdlib and user code use the same derivation; no externally unitary/isometric certificate is supported by this boundary.

This records the required consumer contract, not implementation or completion of the 0.4.0 structural migration. All twelve existing #152 acceptance criteria and its target remain unchanged. Local #315 commits are not yet published while the preceding exhaustive CI run finishes; their exact publication and full validation are tracked in #315/#142.
