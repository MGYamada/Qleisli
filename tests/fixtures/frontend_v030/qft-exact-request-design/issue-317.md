## Target and priority

**Target: Qleisli 0.3.0. Priority: important.**

The current stdlib still contains public names that reflect historical demo implementations, English collection buckets, or incidental organization rather than stable mathematical meaning.

Before the 0.3.0 semantic freeze, establish a project-wide rule:

> **Stdlib namespaces and public function names must be chosen by mathematical semantics, not by implementation history, benchmark identity, algorithm name, decomposition strategy, or an arbitrary collection of routines.**

This issue applies that rule immediately to three current problems:

1. retire the ad-hoc fixed-instance `std::arithmetic` surface and reserve the namespace for scalable arithmetic / number-theoretic semantics;
2. rename `std::transforms` to the semantic singular `std::transform`;
3. retire `std::routines` as a catch-all namespace and reclassify every public member by its actual mathematical meaning.

Related:
- #167 — primitive/derived boundary; stdlib is ordinary checked `.qli`
- #152 — 0.4.0 structural stdlib refactor after the 0.3.0 semantic freeze
- #315 — infer ordinary stdlib effects from checked bodies

---

## 1. Remove the current ad-hoc `std::arithmetic` public surface

The current public namespace contains fixed demonstration routines such as:

- `std::arithmetic::increment2`
- `std::arithmetic::add2`
- `std::arithmetic::mul2_mod15`

These are useful historical/demo circuits, but they are hard-coded small instances rather than a coherent public arithmetic library.

Audit **all** current public items under `std::arithmetic`, not only the three examples above.

For 0.3.0:

- remove the current ad-hoc public arithmetic functions;
- do not keep compatibility aliases merely to preserve historical names;
- preserve useful tiny circuits only as examples, tests, fixtures, tutorials, or corpus material where appropriate;
- allow `std::arithmetic` to be empty until a genuinely parameterized semantic API is ready.

The goal is not to delete useful test material. The goal is to prevent arbitrary fixed instances from acquiring permanent stdlib authority.

---

## 2. Reserve `std::arithmetic` for scalable arithmetic / number theory

Define the namespace by semantic admission rule:

> **An API belongs in `std::arithmetic` iff its public identity is a reusable, parameterized arithmetic or number-theoretic operation whose contract is independent of one hard-coded circuit instance.**

Representative intended API shapes include:

```text
std::arithmetic::modexp<N>
```

and, for the v1 design, the reserved semantic factorization API:

```text
std::arithmetic::primefact<N>
```

The exact generic-parameter syntax and implementation do not need to be completed by this issue. What 0.3.0 must establish is the **meaning of the namespace**.

Large reversible arithmetic, modular arithmetic, modular exponentiation, gcd-related operations, and later factorization routines are natural inhabitants when their contracts are mature.

---

## 3. Public function names describe semantics, not algorithms

Adopt the project-wide naming rule:

> **The canonical stdlib function name names what the function computes, not how it computes it.**

Therefore the future factorization API should be:

```text
std::arithmetic::primefact<N>
```

not:

```text
shor<N>
std::arithmetic::shor<N>
```

The public contract is prime factorization. Shor's algorithm is one possible realization of that contract.

The same semantic API should remain valid if the implementation later changes because of:

- a different quantum algorithm;
- a different reversible arithmetic construction;
- a better asymptotic implementation;
- backend-specific lowering;
- optimizer substitution;
- a different verified realization.

This is especially important for coding agents: API discovery should follow the user's mathematical intent, not require knowledge of historical algorithm names.

---

## 4. Algorithm choice is a parameter or policy, not the semantic function name

If callers need to request a particular realization, encode that choice as a parameter, typed policy, or equivalent configuration of the semantic operation.

Conceptually:

```text
std::arithmetic::primefact<N, alg = ...>
```

rather than defining algorithm-specific canonical public functions.

The exact syntax is not fixed here. The semantic separation is:

```text
namespace/function name = mathematical operation
algorithm parameter     = requested realization/strategy
backend lowering        = implementation decision
```

Likewise, `modexp` denotes modular exponentiation regardless of whether its implementation uses schoolbook arithmetic, windowing, Fourier arithmetic, Montgomery-style methods, or another verified construction.

---

## 5. Rename `std::transforms` to `std::transform`

The current plural namespace:

```text
std::transforms
```

is collection-oriented. It reads as a bag of functions rather than a mathematical namespace.

Rename it to:

```text
std::transform
```

The namespace denotes the semantic family **transform**, while individual functions name particular transforms.

For example:

```text
std::transform::qft<...>
```

is preferable to a plural collection bucket.

Adopt the broader convention:

> **Top-level mathematical stdlib namespaces should prefer singular semantic concept nouns rather than plural “bags of routines”.**

Update the public path atomically across source, imports, examples, corpus material, documentation, fixtures, and tests.

Because Qleisli is pre-1.0, do not retain a long-lived `std::transforms` compatibility alias unless a concrete migration requirement is demonstrated.

---

## 6. Retire `std::routines` as a public catch-all namespace

`std::routines` has no stable mathematical meaning.

It classifies APIs by the accidental fact that they are “routines”, which is true of essentially every library function. It therefore cannot provide a principled admission rule, cannot scale as the stdlib grows, and encourages unrelated operations to accumulate in one bucket.

For 0.3.0:

> **No canonical public stdlib API should live under `std::routines`.**

Audit every current public member of `std::routines` and assign it to a namespace determined by its actual mathematical semantics.

Do **not** mechanically rename the bucket to another generic name such as:

```text
std::algorithms
std::utils
std::helpers
std::misc
```

unless that namespace itself has a precise semantic admission rule. Replacing one catch-all with another does not solve the problem.

If a current routine has no defensible mathematical classification yet, it should remain internal or move to examples/tests/fixtures until its public semantic role is clear.

The desired rule is:

```text
public operation
    -> identify mathematical meaning
    -> choose one semantic namespace
    -> expose one canonical public path
```

not:

```text
public operation
    -> put it in "routines"
```

This deliberately pulls the semantic part of #152's later “retire catch-all organization” requirement forward into 0.3.0. The later 0.4.0 work may still decide file layout and re-export structure, but the public semantic classification should already be correct.

---

## 7. Every public namespace needs a semantic admission rule

For every top-level mathematical stdlib namespace, require a short rule of the form:

> **An API belongs here iff ...**

The rule must be based on mathematical meaning and be strong enough that a contributor or coding agent can classify a new API without guessing from historical placement.

Good namespace identity should survive:

- implementation replacement;
- optimizer evolution;
- backend changes;
- algorithm substitutions;
- circuit decomposition changes;
- movement of source files;
- growth of the stdlib.

Namespace identity must therefore not be inferred from current directory structure or the tiny size of the present library.

---

## 8. Design stdlib from meaning downward

The long-term direction should be:

```text
mathematical meaning
        ↓
public stdlib namespace/function contract
        ↓
generic parameters / algorithm policy
        ↓
ordinary checked .qli implementation
        ↓
optimizer/backend lowering
```

not:

```text
existing demo circuit
        ↓
accidental permanent API name
```

and not:

```text
unclassified useful function
        ↓
std::routines
```

The current stdlib is intentionally small. Historical examples must not determine the future mathematical ontology of the library.

---

## 9. Relationship to #167 and #152

This is a **0.3.0 semantic naming/admission correction**, not the full 0.4.0 structural reorganization.

Under #167:

- arithmetic, transform, and other derived routines remain ordinary checked `.qli`;
- namespace placement grants no primitive or trusted status;
- semantic authority comes from ordinary checking plus the mathematical contract, not the path.

Under #152:

- 0.4.0 may later reorganize files, visibility, re-exports, and discoverability;
- it should consume the semantic identities fixed here;
- it must not resurrect `std::routines`, plural collection buckets, or accidental demo APIs merely for structural convenience.

The reason to act in 0.3.0 is precisely to avoid freezing the wrong public contracts and then treating them as immutable semantic input to the 0.4.0 refactor.

---

## Reserved v1 identity

Reserve the following public semantic identity for the v1 stdlib design:

```text
std::arithmetic::primefact<N>
```

This reservation concerns API meaning, not a requirement that production factorization ship in 0.3.0.

The v1-facing principle is:

> **Users ask Qleisli for the mathematical operation. Algorithm selection is secondary configuration.**

---

## Non-goals

This issue does **not**:

- implement a complete number-theory library in 0.3.0;
- require `primefact<N>` to be production-ready before v1;
- choose the final syntax for algorithm-policy parameters;
- choose the final modular multiplication/exponentiation algorithm;
- make arithmetic or transform routines primitives;
- define backend gate synthesis;
- solve generic external unitarity/isometry;
- complete the full 0.4.0 stdlib directory hierarchy;
- require every future stdlib family to exist immediately.

---

## 0.3.0 acceptance criteria

- [ ] Audit every current public item under `std::arithmetic`.
- [ ] Remove the ad-hoc fixed-instance public arithmetic routines, including `increment2`, `add2`, and `mul2_mod15`.
- [ ] Preserve useful tiny circuits only as examples/tests/fixtures/corpus material where appropriate, not canonical stdlib APIs.
- [ ] Document the semantic admission rule for future `std::arithmetic` APIs.
- [ ] Reserve `std::arithmetic` for scalable parameterized arithmetic / number-theoretic operations.
- [ ] Record `std::arithmetic::modexp<N>` as a representative intended semantic API shape.
- [ ] Reserve `std::arithmetic::primefact<N>` as the v1 semantic factorization API identity.
- [ ] State normatively that algorithm names do not replace mathematical-operation names in canonical stdlib APIs.
- [ ] State that explicit algorithm selection belongs in a parameter/policy/configuration layer.
- [ ] Rename `std::transforms` to `std::transform`.
- [ ] Document the singular semantic-namespace convention for mathematical stdlib modules.
- [ ] Audit every current public member of `std::routines`.
- [ ] Remove `std::routines` as a canonical public namespace.
- [ ] Rehome each former `std::routines` API under a namespace justified by its mathematical meaning, or make it non-public until such a classification exists.
- [ ] Do not replace `std::routines` with another semantically empty catch-all.
- [ ] Give every public top-level mathematical namespace a documented semantic admission rule.
- [ ] Update source/imports/examples/docs/corpus/fixtures/tests atomically for the namespace changes.
- [ ] Do not retain compatibility aliases for accidental pre-1.0 APIs without a demonstrated migration need.
- [ ] Keep all such stdlib functions ordinary checked `.qli` under #167.
- [ ] Align #152 so its 0.4.0 structural refactor consumes these 0.3.0 semantic namespace decisions without redefining them.

---

## Design principle

> **The stdlib should expose the mathematics users ask for, not the history of how the implementation happened to be written.**

And at namespace level:

> **A namespace is a mathematical category with an admission rule, not a drawer for functions that happen to exist.**


## Scope inclusion and ordinary impact record — 2026-10-06 (Asia/Tokyo)

The maintainer explicitly requested inclusion of #317 in the active 0.3.0 plan. The selected scope is now **111 Issues**: all original108 plus #311, #315 and #317. #317 belongs to G10 and milestone0.3.0; its twenty original acceptance criteria remain intact. The release gate will require its reviewed requirements and acceptance evidence alongside every previous target. Inclusion completes none of these implementation criteria.

This semantic naming/admission correction applies existing QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01. Derived source remains ordinarily checked; paths/names grant no effect, primitive, exact Meaning or access authority. Existing two ordinary QLV1 ownership/scope guarantees retain their exact scope, premises, meanings and acceptance binding. No new constitutional interpretation, guarantee admission, edition or dependency change is authorized by this accounting update. #152 retains its later structural scope; its consumer contract must reflect the eventual0.3.0 semantic namespace decision. Current useful sources, proofs, counterexamples, validation and third-party notices will be preserved when active imports are migrated; historical records will not be rewritten.


---

## Canonical generic operation vs fixed-size specializations

The transform namespace must distinguish the **semantic generic operation** from useful fixed-size specializations.

For QFT, the canonical stdlib identity is:

```text
std::transform::qft<N>
```

Fixed-size forms such as:

```text
std::transform::qft2
std::transform::qft3
std::transform::qft4
```

may remain when they are useful as small explicit circuits, pedagogical examples, optimized specializations, regression fixtures, or convenient aliases.

However, they must be semantically subordinate to the generic family:

```text
qft2  ≃ qft<2>
qft3  ≃ qft<3>
qft4  ≃ qft<4>
```

and must not define the ontology of the API.

The project rule is:

> **When a mathematical operation forms a genuine parameterized family, the generic family is the canonical stdlib API; fixed-size names are optional specializations of that family.**

This is deliberately different from the rejected fixed-instance arithmetic APIs above. A hard-coded `qft2` is acceptable because it is a recognizable specialization of a well-defined generic semantic family `qft<N>`. An arbitrary `add2` or `mul2_mod15` is not sufficient to define the future meaning of `std::arithmetic`.

Accordingly:

- documentation should teach `qft<N>` as the primary operation;
- coding agents should prefer `qft<N>` unless a fixed specialization is explicitly useful;
- resource analysis and semantic contracts should be stated for the generic family where possible;
- specialized forms must agree with the generic family at the corresponding parameter;
- implementation specialization must not fork the mathematical meaning.

Add to the 0.3.0 acceptance criteria:

- [ ] Make `std::transform::qft<N>` the canonical semantic QFT API.
- [ ] Treat `qft2`, `qft3`, `qft4`, and analogous fixed-size forms only as optional specializations/aliases/examples of `qft<N>`.
- [ ] Verify each retained fixed-size QFT specialization is semantically equivalent to the corresponding generic instance.
- [ ] Document the general rule that parameterized mathematical families own the canonical API name; fixed-size names do not.


---

# Ordinary #317 before-code contract — 2026-10-06 (Asia/Tokyo)

Status: reviewed ordinary implementation contract for the next bounded experiment and shared frontend integration. This is not a claim of current canonical API availability or completed validation. This is an ordinary language/library contract under existing QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01, not a new constitutional interpretation or guarantee admission.

## Scope and exact QFT contract

The current #317 scope is 24 criteria: all original twenty plus the four later generic-QFT criteria. Retain their exact text and required status in the next caller-reviewed release requirements snapshot. The canonical semantic identity is `std::transform::qft<N>`. Define the positive Fourier family on `Q<Bits<N>>`, returning the same ordered basis, for static N >= 0:
`F_N[y,x] = exp(2*pi*i*x*y/2^N) / sqrt(2^N)`.
For N=0, F_0=[+1] is exact identity on the same Q<Bits<0>> logical owner, distinct from Q<Unit>. Existing native named Fourier requests reject zero; validate this case through the existing typed identity/composition path without changing that matcher. For positive N, axis zero has weight one; output-bit reversal is included in this exact operator. Every input owner returns, with no observation or auxiliary allocation; its principal effect is body-derived Unitary. The intended action remains F_N tensor identity on every external reference, with phase and axis order retained. Names or effect metadata do not prove this functional contract or grant inverse/control access.

Use ordinary checked generic .qli source, not a new primitive or compiler special-case for the qft name. The current executable static-parameter spelling is `qft[static N: Nat]` with calls `qft[N]` applied to `q`; `qft<N>` denotes the canonical generic semantic identity in this checkpoint. Do not advertise angle-bracket call syntax as implemented. Any final generic-call spelling change follows the common grammar work in #32 and its migration contract.

Retained `qft2` and `qft3` may remain optional specializations with their existing exact tuple interfaces. No implicit tuple/Bits coercion or width-based type identity is introduced. Their correspondence to the generic instances must state the explicit ordered basis encoding and check exact phase, entries and reversal. A future `qft4` may be a specialization; its mention does not require adding a new fixed API now. Preserve all original contracts, useful tiny circuits, source provenance and notices. Current target/coefficient/work limits remain explicit; unsupported exact instances reject rather than round or silently select weaker checking. A generic checked definition and bounded instance results do not establish a theorem for the whole family.

## Sequence after the frozen validation finishes

1. Preserve a local first-source experiment using ordinary inferred `fn`, the existing licensed Fourier body and an outer `if static N == 0` branch. Check only N=0,1,2,3, retaining real generic-checking or native-boundary failures; local success does not expose a canonical std API. Audit every public stdlib item and active caller. Record mathematical namespace/admission rules and the disposition of each fixed arithmetic/catch-all API; preserve current sources and counterexamples before migration.
2. Connect ordinary generic stdlib definitions to shared name resolution, generic checking, embedding and public project/selected execution paths before exposing the canonical family. Use one immutable source collection, AST/Resolution and complete common declaration checking; only then select finite/Raw/hierarchy lowering eligibility. Do not expose divergent per-profile std ASTs, omit incompatible unused/dead declarations, add a privileged QFT-name resolver, or treat the corpus function's name as a library contract. The current finite checker rejects Nat/static-fold bodies; sized loading reserves std and rejects existing basis/qif declarations. Registry injection alone cannot repair these generic frontend gaps.
3. Implement the family as ordinary source through the existing exact h/controlled-phase/register-structure operations. The retained Qualtran Fourier translation is useful prior evidence, with its license/provenance preserved; copying or changing frozen corpus material still follows corpus policy.
4. Perform one atomic active migration: singular std::transform, canonical qft family and subordinate specializations; retire ad-hoc arithmetic exports and std::routines, rehome mathematically justified APIs, and update imports, examples, corpus clients, documentation, fixtures and discovery metadata. Retain historical validation records unchanged.
5. Independently check small closed QFT instances and every retained fixed specialization against the exact contract and explicit interface encodings, including wrong phase/axis/reversal cases, fresh native acceptance and real public CLI/library paths. Add no new maximum-size generation. Source/effect tests, output-IR acceptance, general preservation proofs and quantitative resource certification remain distinct.
6. Append #152's consumer boundary: its 0.4.0 structural refactor consumes #317's frozen semantic identities/admission rules, generic QFT contract and specialization correspondences; it cannot resurrect retired catch-all or incidental demo identities. Keep #152's target and twelve criteria. Close #317 only when evidence covers all 24 criteria.

No protected Constitution text, human adoption/admission record, ledger status, dependency version, native acceptance rule, new certificate schema or project axiom changes are authorized by this checkpoint.

## Audited disposition and namespace admission

The current target inventory is ten public ordinary runtime functions and private `nonzero2`; none is a sealed primitive. Preserve the exact body/phase/instrument contract and notices while changing active paths.

| Current path | Exact contract | Disposition |
| --- | --- | --- |
| std::arithmetic::increment2 | y -> (y+1) mod 4, coefficient +1 | Local examples/tests; retire canonical std export |
| std::arithmetic::add2 | (x,y) -> (x,x+y mod 4), coefficient +1 | Local examples/tests; retire canonical std export |
| std::arithmetic::mul2_mod15 | y -> 2y mod 15 for y<15; fixes15, coefficient +1 | Local order-finding examples/tests; retire canonical std export |
| std::transforms::qft2 / qft3 | Positive F4 / F8, included reversal | Optional std::transform specializations of the one generic family |
| std::routines::hadamard2 | Ordered H tensor H | std::transform::hadamard2 |
| std::routines::reflect_uniform2 | 2P_++-I, exact fixed sign and cleanup | std::reflection::reflect_uniform2; keep nonzero2 private |
| std::routines::measure_x | Complete destructive X instrument, K_b=bra(b) H | std::measurement::measure_x |
| std::routines::measure_z2 | Complete ordered destructive two-bit Z instrument | std::measurement::measure_z2 |
| std::routines::parity_zz | Nondestructive parity, K_s=(I+(-1)^s Z tensor Z)/2, both data owners retained | std::measurement::parity_zz |

The Qualtran reflection2 corpus contract is I-2|++><++|, the negative of reflect_uniform2. Do not merge them or erase the relative phase. Namespace placement grants no authority. Public names denote mathematical operations; explicit algorithm choice belongs to a parameter/policy/configuration layer. Mathematical families own the canonical generic name; fixed sizes are subordinate specializations. Prefer singular semantic concept nouns.

`arithmetic` admits reusable parameterized arithmetic/number-theoretic operations independent of a fixed demonstration; `modexp<N>` is an intended shape and `primefact<N>` the reserved v1 factorization identity, neither an available operation merely from this record. `transform` admits named exact basis transforms with full phase/coordinate equations. `reflection` admits phase-fixed 2P-I with explicit projector/reference contracts. `measurement` admits complete outcome-indexed instruments with consumed/retained owners and outcome encoding. Audit existing foundation namespaces' admission rules against their actual catalogs before finalizing the normative Reference; do not replace routines with another empty bucket.

QFT specialization correspondence uses explicit ordered-label encodings E2(a,b)=a+2b and E3((a,b),c)=a+2b+4c. Require E_N U_fixed E_N^-1=F_N with exact scalar phase. Packing/unpacking must be explicit ordinary source with the original tuple trees and consumed empty remainder, not implicit width coercion. Preserve the first fixed circuits, historical validation sources and pinned upstream material while creating migrated active derivatives.

This contract applies existing interpretations to ordinary implementation; it does not exercise Guardian authority. All24 criteria remain required and open until their implementation and independent evidence are complete.


## Bounded local QFT authoring checkpoint — 2026-10-06 (Asia/Tokyo)

Local record-only commit `5aee1b3cfde51e347cbff83c76526d22cf249d33` retains the licensed ordinary family and N=0 identity branch under `tests/fixtures/authoring_sessions/qft-family-v030/`. Production remains the previously published source unit `238e1f0`; this study changes no Rust, Lean, stdlib or corpus implementation. It is not yet pushed while the useful hosted full run for branch `9256fe9` continues.

All31 actual observations pass: eight initial checks, four reference-client checks, fifteen complete complex basis columns at N=0–3, and four coherent/reference probes. The independent positive Fourier formula agrees with maximum coefficient error `1.3743915342634358e-15` under the declared `1e-11` numerical threshold. The zero-width client retains its Q<Bits<0>> scalar phase beside a coherent complex reference; positive-width clients retain Bell-reference correlations and low-axis ordering. A separate read-only reviewer rechecked raw logs, all14 frozen first inputs, parent200 source map, licensed provenance and analytic complex expectations; no actionable mismatch was found.

All31 native calls are existing `--hierarchy-request-pending` producer-consistency checks, with `source_meaning_verified: false`. They do not bind an independently named exact Fourier request, prove exact QFT2/3 specialization correspondence, expose canonical std source, establish arbitrary unnormalized-input behavior, discharge a general family/resource theorem or admit a guarantee. No maximum-size case is generated. The 179-member packet map SHA-256 is `b2f72c080b45aba2c5b7ad1d72095f69946ec7ca77fd70ba85dd6c3544659576`; authoring, documentation, edition and whitespace checks pass, with the actual recorder's first exit-code mistake preserved separately.

The next #32 prerequisite is a private immutable parsed-source collection and fixed bundled registry, followed by complete common declaration checking. Preserve adapter byte/parse limits and diagnostic order; do not skip unsupported/unused declarations, substitute different profile ASTs or grant privilege to a QFT name. All24 original and appended #317 criteria remain open and required. Overall confirmed completion remains14/111 (12.61%).


## Next prerequisite recorded before code — 2026-10-06 (Asia/Tokyo)

[#32's ordinary source-collection implementation unit](https://github.com/MGYamada/Qleisli/issues/32) records the independently reviewed v2 contract SHA-256 `7f58f7c3f0d24ecef405e8cf501525aeadd67503d93b4b078212dc2d135f765d`. Implement a private fixed four-source/manifest registry and immutable retained-source/common-AST collection, preserving exact bundled bytes, normal declaration targets, original paths, current source/parse capacities, first-failure ordering and complete existing checks. Sized storage will use that collection; finite loading consumes it into the mutable public Project compatibility view without a stale second cache. Public Project mutation supplies fresh untrusted compiler input, never registry authority or cached checked facts.

This infrastructure unit keeps current profile differences explicit and does not inject unsupported bundles into sized preparation, skip declarations, select a replacement AST or expose generic QFT early. Complete common generic checking precedes finite/Raw/hierarchy eligibility and canonical std migration. Broader QS/PR/RS/EXACT obligations, both existing QLV1 scopes, all24 #317 conditions and the #152 later boundary are preserved. No new Guardian interpretation, proof discharge, Issue completion or release readiness follows.


### Local retained-source implementation checkpoint — 2026-10-06 (Asia/Tokyo)

Local commit `b544cd2d96dcc94e0ef29b28e6b08979bca5d9b1` implements the private fixed bundled registry and immutable original-source/common-AST collection described before code. Finite loading consumes it into mutable Project without a parallel authoritative cache; sized preparation retains exact original sources and selected paths. Complete existing declaration checks, capacities and first-failure order remain. Independent review caught and repaired the module-count guard placement before adapter-map conversion.

Both actual Rust1.85.0 and1.98.1 pass the same eight focused targets: **82 passed/0 failed/5 existing ignores**, formatting and warnings-denied all-target Clippy. All23 frozen before/after observations match exactly, including diagnostics, native-call counts and proposal bytes. Two independent read-only reviews find no remaining defect. Reviewed inventory adds only private source.rs and four existing source hashes; parsed API/capacity/route metadata and all native/Lean/std bytes remain unchanged. All13 policy commands/66 regressions and pinned mdBook0.5.4 build/link checks pass. The bounded130-source map is not complete runtime closure; retained failed MSRV launch and raw EOF checks are not silently counted as successful runs. Final128-member packet map: `c21bbe33cb920ddfb3534bb278f4a535747233a625ec86c5cdfc30e1300895b8`.

This commit is local and not yet pushed, to avoid cancelling the useful prior hosted full run. It completes only retained-source infrastructure, not complete common checking, canonical generic QFT, namespace migration, source preservation or release readiness. All111 selected targets and all24 #317 criteria remain; confirmed completion stays **14/111 (12.61%)**. The next bounded unit shares actual common-AST declaration/interface and pattern checking before std exposure; every private/unused body remains required. QS/PR/RS/EXACT duties and both scoped QLV1 guarantees retain their exact adopted scopes; no new constitutional act or proof discharge follows.

## Common pattern-rule prerequisite — before-code checkpoint

#32 now records the concrete reviewed runtime-binding refactor, candidate-v2 SHA-256 `e178b5f0ca7c465eaed0e01cc48879c963b674c2ec6db032c7fb4f9fcf4ad0ae`, after40 actual first-source observations with preserved diagnostic order and native counts. Share wildcard linearity, duplicate binding names and exact immediate tuple/ordinary Unit shape through borrowed views of existing patterns. Keep lexical/dynamic owner identities, exact zero-width owners, RHS-first evaluation, current capacity order and native rejection paths. The existing private sized projection bridge is temporary and introduces no second AST or new profile rule. Complete generic declaration/body checking, Basis/Meaning/control/workspace support and finite/Raw/hierarchy eligibility still precede canonical std integration. This bounded refactor exposes no std API, earns no #317 completion credit, preserves all24 criteria, and adopts no interpretation/guarantee.
