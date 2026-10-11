# Next common checking unit: ordered generic formal kinds

Status: non-normative read-only architecture candidate for #32/#317. No new
rule, adoption, implementation, completed common checker or Issue closure is
claimed. This author inspected the actual source and selected retained contract
and Reference sections. No CLI/native command, test, build, Git command or
GitHub mutation was performed. Desired snippets below were not executed and
are not recorded first diagnostics. The inspected hash subset is separate from
compiled-source or complete runtime-closure attestation.

## Recommendation

Implement one substantive **ordered generic formal-kind and access judgment**
over the retained common `ast::Decl` and its actual lexical `Index`. Both
finite `Compiler::abstract_bindings` and sized `check::declaration` must consume
its checked facts. It should own the rule that an operation kind refers only
to preceding Nat/Basis parameters, and that each access requirement targets
one actual operation binder and occurs at most once per capability.

This is more than a spelling/set helper: its output determines which exact
type a formal operation acts on and which operations a generic body may use.
Keep using the existing `types::Type<N>` tree, `TypeParameter` binder identity,
`Stage` and `classify_source`; these constructor rules are already shared.
Do not introduce another AST, a copied header syntax or a name/width-based
substitute for the original declaration and lexical identities.

## Actual remaining split

Finite `signature` reads the common Decl, checks names per argument, classifies
runtime/result types and applies its existing Basis-pattern rule. Later,
`abstract_bindings` calls signature, classifies every Op basis, optionally binds
a phase-fixed Meaning target, constructs abstract operations, then resolves
Access requirements and rejects duplicate capabilities. Its closed type size
is `Infallible`; finite profile preflight rejects Nat, opaque Basis, register
types and symbolic predicates before these stages. Meaning refinement remains
a separate finite mathematical/evidence obligation.

Sized projection already uses the common constructor classifier, but produces
`Type<projected Natural>` and a private `Function`. `declaration` then installs
all symbolic naturals, applies natural premises and feasibility, installs
Basis/Op formals in order, checks access, and finally binds runtime patterns
and types. Its checked type is `Type<Linear>`. Op kinds use only preceding
naturals and already installed bases; whole-declaration premises do not grant
a later formal permission to occur in an earlier kind. Meaning-refined Op and
Basis/Meaning declarations reject in projection instead of being skipped.

The common lexical resolver intentionally registers all static names before
their annotations. That makes later names resolvable, not kind-admissible.
`BinderKey` contains the declaration-local structural identity; `UseInfo.target`
is distinct from its global/static compatibility candidates. The new rule must
use the actual local target and binding category, not fall back by spelling to
a static/global candidate when the resolved local has another category.

## Concrete common invariant and consumption

For the same current Decl/DefId/Index:

1. Associate every original static parameter with its actual BinderKey, kind,
   source ordinal and original identifier/type spans. Preserve complete counts;
   no zip truncation, search by name/span, filtered unsupported sibling or cache
   over a mutable finite Project is permitted.
2. When checking an Op kind at ordinal `i`, each Named basis occurrence must
   resolve to an earlier StaticBasis binder; each name in its natural size
   expression must resolve to an earlier StaticNatural binder. Enforce this at
   the existing ordered name-resolution points while classifying/evaluating the
   kind, not by an eager all-reference prewalk before arithmetic. For example,
   a nonlinear left subexpression must not lose its earlier error to a later
   unavailable name. Resolve structural source occurrences through the existing
   borrowed Index; any new traversal is bounded and iterative, left-to-right.
   Do not trust a public AST's stored Natural.depth or a parser-only bound as
   evidence of actual tree depth.
3. Classify that original basis through the common `Stage::Basis` constructor
   rule and the existing profile size/accounting context. Preserve nested-Q
   rejection, opaque A/B identity, tuple shape, Unit/Bits0 and Bit/Bits1.
   This unit does not merge finite bit limits and sized symbolic capacities.
4. An Access requirement resolves to a checked StaticOperation key from this
   declaration. Derive its Apply/Adjoint/Controlled set once in original
   requirement order; reject unknown/non-operation targets and the first
   repeated capability. Its source name/requirement spans remain available to
   current error adapters. Formal access is an explicit generic assumption,
   never provider/effect/Meaning evidence or permission inferred from unitarity.
5. Finite abstract Operation.basis/access and sized Scope.operations consume
   those same checked type/key/capability facts. Removing the old independent
   policy branches is a mechanical acceptance condition. Merely running a
   common preflight and rebuilding unchecked formals afterward is insufficient.

The result is declaration-local scope facts using existing type trees, not a
second source AST or an accepted handle. Initially share the unrefined Op
contract; preserve finite Meaning checks and sized unsupported refinement.
Do not erase refinement merely to make the two profiles look alike. Moving the
linear premise solver or completing refinement requires its own bounded unit.

## Diagnostic ordering is part of the contract

Keep a phased judgment initially, rather than an eager whole-header preflight:

- Finite retains resolution/profile preflight, lexical/dependency order, its
  signature's per-argument name/type checks, then Op kind/Meaning and Access.
- Sized retains per-module projection before parsing the next module, static
  uniqueness/natural insertion, premises/feasibility, ordered kinds, Access,
  each runtime name/type/binding, return type, then complete body/effect checks.

The rule and derived facts become common; those outer priority differences
remain explicitly transitional. A single global header/error schedule would
be a public behavior change requiring a concrete #32 before-code contract and
small real before/after observations. The preceding parameter-name contract
expressly preserves the existing schedules and cannot authorize that change.

One concrete unexecuted ordering control, using the retained collision spelling,
is:

```qli
pub fn f[static U:Op<Bit>]((U,q):(Unit,Q<Bit>))->Q<Bit>
requires Apply(missing) { q }
```

It contains a runtime pattern colliding with static U and an invalid access
target. Inspection predicts finite signature rejects the repeated runtime name
before abstract Access checking; sized Access precedes bind_name's static-shadow
rule. These are predictions, not produced diagnostics. Freeze the small source
before a later authorized check and retain genuine first outputs. A nested-Q
argument is unsuitable for this particular control: sized projection rejects
it before declaration Access, so it does not isolate the two schedules. Do not
rewrite the existing retained collision source to add the new control.

## Bounded desired programs and checks

Use ordinary existing spelling, not new generic syntax, for a later first study:

```qli
pub fn apply_once[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A>
requires Apply(U) { U(q) }
```

The selected profile already supports this shape; finite still has an explicit
Basis profile rejection. A small dependent-kind version uses preceding
`static n:Nat, static U:Op<Bits<n>>`. Their reverse orders must fail the ordered
kind rule. Retain unknown/non-Basis names, `Controlled(n)`, duplicated `Apply(U)`,
distinct A/B owners and nested Q as semantic negatives at the actual stage
reached. Do not use an earlier finite unsupported error as proof of a later
kind, access, owner or body condition.

Existing `tests/basis_polymorphism.rs` and `tests/sized_source.rs` retain actual
forward-kind, wrong-category, duplicate-access, invalid unused-body, static-arm
and zero-fold coverage. `tests/operation_parameters.rs` retains finite unrefined
and Meaning-refined generic contracts. They were read, not run here. Later
tests must exercise both real consumers, preserve public mutable-AST behavior,
and compare raw diagnostic/native/proposal behavior where unchanged. No new
maximum-size case, mirrored helper-only test or favourable-instance rescue is
needed. A closed instance success is not a generic theorem.

## Boundary to ordinary generic std integration

This unit is a necessary common declaration judgment, not sufficient std
integration. It does not remove finite profile preflight, sized projection,
generic body/call checking, complete sibling/unused checks, static termination,
Basis/Meaning support gaps or lowering eligibility differences. Introducing
ordinary generic std into the finite registry while skipping unsupported
unused declarations would violate the current collection/Reference contract.

The eventual language path must check every complete original declaration once
under common generic type/kind/body/owner/effect rules, then choose a lowering
profile only for the selected closed use. That architecture needs further
bounded work. Keep canonical QFT namespaces, explicit tuple/Bits reshaping,
source/provider/artifact correspondence, analytic family proofs and native
acceptance distinct. No algorithm name, annotation, version or header check can
supply those missing obligations. Existing QS/PR/RS/EXACT status and the two
ordinary QLV1 guarantees remain unchanged.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
