## Status

**Target: Qleisli 0.3.0. Priority: very important. Type: enhancement.**

Qleisli 0.3.0 should stop treating hand-written effect contracts on ordinary derived stdlib functions as semantic authority.

The standard library is ordinary checked `.qli` by #167. Therefore, for ordinary derived functions whose bodies are available to the normal checker, the default source of truth should be:

```text
.qli body
    ↓
ordinary type / ownership / effect checking
    ↓
inferred semantic effect
```

not:

```text
human reads body
    ↓
human guesses Unitarty / Iso / Observe
    ↓
annotation becomes the declared contract
```

The current explicit annotations are not necessarily wrong. They are useful pre-0.3.0 scaffolding. But keeping them as the primary semantic source duplicates information already present in ordinary checked `.qli`, creates drift risk, and weakens the architectural meaning of #167.

Related:
- #167 — stdlib is ordinary checked `.qli`; primitive vs derived boundary
- #100 — infer uniquely determined effects; annotations may check/restrict but may not manufacture meaning
- #27 — ownership and semantic effects are orthogonal
- #48 — authoritative 0.3.0 Language Reference
- #152 — later stdlib structural refactor
- #154 — future primitive admission policy
- #283 — **post-v1, unresolved** externally unitary/isometric realization rule

---

## Core principle

> **For ordinary checked `.qli`, the body is the semantic evidence for its effect class.**

Equivalently:

> **Derived stdlib code should not need a second hand-maintained effect ledger.**

For a normal source definition, Qleisli should compute the unique effect implied by the body:

```text
infer_effect(body) = Unitary | Iso | Observe | ...
```

subject to the adopted 0.3.0 effect lattice / composition rules.

If a source-level annotation is retained, its role should be an **assertion checked against the inferred result**, not an unchecked declaration that supplies missing semantic authority.

Conceptually:

```text
fn f(...) { body }              // effect inferred

unitary fn f(...) { body }      // if retained: assert/check inferred effect
```

The second form must reject if the body does not satisfy the stated class.

---

## Why this matters specifically for stdlib

#167 establishes:

```text
stdlib = ordinary derived Qleisli source
```

Therefore stdlib placement should grant no special need to hand-author semantic effect classifications.

Today, much of the stdlib effectively does:

1. inspect the implementation;
2. classify it manually as unitary / isometry / observe;
3. write that classification into the declaration.

That is semantically reasonable but architecturally redundant.

The desired 0.3.0 direction is:

```text
ordinary .qli implementation
        ↓
normal checker
        ↓
principal / uniquely determined effect
        ↓
qlidoc / interface metadata / diagnostics
```

This makes stdlib trustworthy for exactly the same reason as user code: the ordinary checker derives the accepted semantics from the source program.

---

## Public API contracts may still be recorded

This issue does **not** require deleting all visible contract information from documentation or interfaces.

A public API may still expose:

- inferred effect class;
- input/output ownership shape;
- exact mathematical Meaning where separately specified and verified;
- phase / axis / ordering conventions;
- cleanup guarantees;
- capabilities such as controllable / adjointable where independently justified.

The distinction is authority:

```text
recorded contract  = checked/exported fact
not
recorded contract  = unchecked source of truth
```

`qlidoc` and other tooling should preferably print the inferred effect even when the source omits a redundant annotation.

Exact mathematical `Meaning` may require explicit specification; this issue does not claim that arbitrary mathematical operator identities can always be inferred syntactically. The requirement is that mechanically derivable effect classification must not be maintained as an independent handwritten semantic ledger.

---

## Explicit annotations, if retained

0.3.0 should decide whether explicit effect syntax remains mandatory, optional, or becomes primarily an assertion form.

Whichever surface choice is adopted, the semantic law should be:

> **An annotation on an ordinary body may constrain/check inference; it may not make an otherwise invalid body unitary or isometric.**

Required behavior:

- inferred `Unitary` + asserted `Unitary` → accept;
- inferred stronger class where a normative weakening is allowed → handle only by explicit language rule;
- inferred `Observe` + asserted `Unitary` → reject;
- unresolved/ambiguous classification → reject rather than trust the annotation;
- annotations must not downgrade away observation or ownership effects.

This is consistent with #100.

---

## Stdlib migration

Audit the current derived stdlib and classify existing effect annotations as one of:

1. **redundant inferred fact** — remove from the semantic source of truth, and preferably from source where ergonomically appropriate;
2. **checked public assertion** — retain only if it improves API stability/readability, but verify it against inference;
3. **true primitive/kernel fact** — this item is not ordinary stdlib under #167 and must be moved to the primitive boundary;
4. **not currently inferable** — identify the missing language/checker rule instead of silently retaining a trusted handwritten stdlib contract.

Do not solve an inference limitation by giving ordinary stdlib privileged semantic authority.

---

## Critical non-goal: externally unitary / externally isometric

**This issue must not introduce, solve, or silently assume `externally unitary` / `externally isometry`.**

As already recorded in #283:

> externally unitary/isometric realization is a **long-term, post-v1 verified extension** and remains unresolved.

In particular, #283 concerns implementations whose internal realization may include hidden measurement / feed-forward while the induced public channel is independently certified as unitary or isometric.

That is a fundamentally different boundary from ordinary body-derived effect inference.

For 0.3.0:

```text
ordinary checked .qli body
    -> infer effect from the body

opaque / foreign / externally certified realization
    -> NOT solved here
    -> remains the long-term open problem in #283
```

Do **not** add an `externally unitary` or `externally isometry` escape hatch merely to make stdlib migration easier.

Do **not** reinterpret a handwritten stdlib annotation as an external certificate.

If a function cannot be justified through ordinary `.qli` checking, #167/#154 determine whether it belongs at the primitive boundary; #283 remains the future extension point for externally certified implementations.

---

## Trust-boundary consequence

The desired architecture is:

```text
small constitutional primitive boundary
        ↓
ordinary .qli checker
        ↓
body-derived effect classification
        ↓
stdlib and user code uniformly
```

not:

```text
primitive contracts
        +
stdlib handwritten contracts
        +
user-code inference
```

There should be only one ordinary derived-code rule.

This keeps the trusted semantic surface small and prevents stdlib from becoming a second quasi-primitive layer.

---

## Acceptance criteria

- [ ] The Language Reference states that ordinary checked `.qli` effects are derived from the body by the normative checker.
- [ ] Effect inference is deterministic and uniquely determined under #100.
- [ ] A handwritten effect annotation on an ordinary body cannot manufacture semantic authority.
- [ ] If explicit annotations remain, their assertion/checking semantics are specified.
- [ ] An annotation cannot hide or downgrade `Observe`.
- [ ] The current derived stdlib is audited for redundant hand-written effect contracts.
- [ ] Redundant stdlib effect annotations are removed or converted into checked assertions rather than trusted declarations.
- [ ] `qlidoc` / interface metadata can expose inferred effect classes without requiring duplicate source annotations.
- [ ] Exact mathematical `Meaning` specifications remain distinguished from mechanically inferred effect classification.
- [ ] Anything that genuinely requires trusted semantic authority is classified under the primitive boundary of #167/#154, not ordinary stdlib.
- [ ] No ordinary stdlib function gains privileged effect authority because of its module/path/name.
- [ ] #152's later structural refactor consumes these checked/inferred contracts without redefining them.
- [ ] **`externally unitary` / `externally isometry` are explicitly left unresolved and deferred to the long-term post-v1 work in #283.**
- [ ] No 0.3.0 escape hatch is introduced that approximates the future #283 mechanism.

---

## Design principle

> **If Qleisli can read the body, Qleisli should derive the effect.**

And:

> **The standard library should not tell the checker what its ordinary Qleisli source already proves.**

The future external-contract problem is separate:

> **If Qleisli cannot justify the implementation through ordinary source checking, that is a trust-boundary problem — not a reason to make stdlib annotations authoritative.**

