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
