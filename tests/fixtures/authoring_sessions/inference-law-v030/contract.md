## Target and status

**Target: Qleisli 0.3.0. Priority: important. Type: enhancement.**

**2026-10-02 boundary decision:** this issue freezes the **inference law**, not the complete catalogue of 0.4.0 inference conveniences.

Concrete coercion/inference choices are coordinated with **#197**.

Related:
- #41 — name resolution
- #44 — generic/basis specialization
- #47 — static constraints
- #75 — method receiver adjustment
- #84 — equality/coherence/physical-map classification
- #89 — callable model
- #98 — trait resolution/coherence
- #196 — `q*** / Q<T> / unmarked`
- #197 — 0.4.0 boundary-condition umbrella

## Core 0.3.0 principle

> **Infer uniquely determined static structure. Never infer quantum meaning.**

Equivalent formulations:

> **Inference may omit bookkeeping; it may not choose physics.**

> **If more than one semantically distinct elaboration is possible, require explicit source information or reject.**

This is the 0.3.0 law.

## Required 0.3.0 properties

### 1. Uniqueness

Any inferred parameter, type, trait choice, capability, receiver adjustment or effect classification must be uniquely determined by normative rules.

No “best candidate” heuristic may select between distinct semantic meanings.

### 2. No implicit physical operations

Inference/coercion must never hide:

- preparation;
- observation;
- discard/reset;
- axis permutation;
- nontrivial phase;
- coherent-control choice;
- quantum access-mode choice;
- ancilla release;
- target-dependent implementation choice.

### 3. Equality categories are respected

Coordinate with #84:

- definitional equality may be used directly;
- canonical coherence may be used only when the Language Reference has admitted that unique coherence;
- physical maps remain explicit.

0.3.0 fixes this classification even though #197 decides the concrete 0.4.0 catalogue of implicit coherence.

### 4. No hidden `Q<T> -> T` or `T -> Q<T>`

Under the adopted type model:

```text
T       ordinary value
Q<T>    quantum ownership
```

expected-type inference or coercion must not create implicit observation or preparation.

The removal of `CBit/CBits` does not create a generic coercion between ordinary and quantum values.

### 5. Capability/trait resolution cannot manufacture semantics

Constraint or trait resolution may check whether declared facts justify an obligation.

It must not:

- search for an implementation merely to make a program type-check;
- synthesize semantic evidence from absence of contradiction;
- equate mathematical semantic existence with executable capability;
- use cyclic guessing to justify a selected associated type/implementation.

### 6. Callable resolution cannot cross categories by guesswork

Name resolution should identify the callable category before ordinary checking.

Ambiguity between:

- ordinary/source function;
- static builder;
- `Op` value;
- trait/associated operation;
- other callable classes

must reject rather than choose by preference.

### 7. Effect inference cannot downgrade meaning

If effect inference is supported:

- it computes the unique effect implied by the body;
- annotations may check/restrict according to the normative effect rules;
- no coercion may downgrade an effect to make a call fit.

### 8. Determinism and boundedness

For a fixed source/dependency/toolchain context, inference must be deterministic and terminate under the accepted static language/work limits.

Diagnostics should identify unresolved variables or competing interpretations.

## Examples 0.3.0 must classify at the law level

The Reference should establish at least:

- unique static inference is permitted in principle;
- ambiguous static substitutions reject;
- physical preparation is never expected-type coercion;
- ordinary `T` and `Q<T>` do not implicitly interconvert;
- axis permutation is never ordinary coercion;
- ambiguous trait/capability resolution rejects;
- ambiguous callable-category resolution rejects;
- effect inference cannot semantically downgrade a body.

## Deferred to 0.4.0 (#197)

0.4.0 decides concrete ergonomic questions such as:

- exactly when `N` may be inferred from `Bits<N>`;
- exactly when `T` may be inferred from `Q<T>`;
- which tuple/unit/owner coherence maps may be inserted;
- whether `Bits<0>` normalizes to `Unit`;
- which static annotations may be omitted;
- detailed return-position/argument coercion;
- `qfor` carry inference;
- `qmatch` pattern inference;
- which ordinary finite functions may be lifted/reused automatically.

These choices must remain instances of the 0.3.0 uniqueness/no-physics law.

## Non-goals

0.3.0 does not introduce:

- arbitrary coercion search;
- overload ranking by conversion cost;
- backtracking over semantic interpretations;
- theorem-prover-driven “make it type-check” elaboration;
- runtime overload resolution;
- implicit physical operations.

It also does not need to freeze every 0.4.0 convenience.

## Acceptance criteria

- [ ] The Language Reference states the uniqueness/no-physics inference law.
- [ ] Multiply solved or semantically ambiguous inference rejects.
- [ ] `T` and `Q<T>` cannot implicitly interconvert.
- [ ] Physical maps cannot be inserted as ordinary coercions.
- [ ] #84's three equality categories constrain inference.
- [ ] Trait/capability resolution cannot manufacture semantic authority.
- [ ] Callable-category ambiguity rejects.
- [ ] Effect inference cannot downgrade meaning.
- [ ] Inference is deterministic, bounded and explainable.
- [ ] Concrete boundary conveniences are explicitly deferred to #197.

## Design principle

> **Infer syntax. Infer uniquely determined static structure. Do not infer physics.**

And:

> **0.3.0 freezes the inference law; 0.4.0 chooses the permitted conveniences.**

## 2026-10-04 target type contract

Require uniquely determined static structure and reject unresolved or competing meanings. Expected types do not prepare, measure, permute axes, manufacture capabilities or downgrade effects. Static substitutions retain exact tree/provider identity. The conservative explicit 0.3.0 contract leaves #197's ergonomic inference choices for their existing later scope.

The [target Language Reference](https://github.com/MGYamada/Qleisli/blob/codex/v0.3.0-foundation/docs/src/reference/type-model.md) and [foundation analysis](https://github.com/MGYamada/Qleisli/blob/codex/v0.3.0-foundation/docs/src/design/type-foundation.md) record this ordinary implementation decision under the approved 0.3.0 plan and adopted authority hierarchy. Edition remains 2026. This is not a new Guardian interpretation or guarantee admission.

Status: target rules selected; implementation and conformance remain in progress in #307. Current alpha syntax still contains CBit/CBits and general Basis polymorphism is not yet implemented. Required positive and negative tests, exact lowering/interface preservation and native acceptance evidence remain open. Documentation alone does not complete this issue.

