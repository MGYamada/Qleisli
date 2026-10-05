# Candidate: one common pattern-binding judgment

**Status: local draft for ordinary technical review; not normative, adopted,
implemented or tested.** This is a bounded implementation proposal under
[#32](https://github.com/MGYamada/Qleisli/issues/32). All remaining #32 and
[#317](https://github.com/MGYamada/Qleisli/issues/317) conditions stay required.

## Additive correction to the first draft

This v2 candidate preserves `contract.md` and its first-files snapshot unchanged.
The first draft incorrectly said that invalid unused declarations reject
before native execution. The existing finite route can check an earlier
entry natively and then reject the complete preparation for an invalid
unused sibling; the selected source route rejects that case with zero
native calls. The required boundary is rejection before publishing a
checked preparation or proposal. Native checker calls are not program
runtime execution, and the first-source experiment did not run programs.
No binder algorithm, capacity rule, or declaration/signature scope changed.

## Selected unit and non-goals

Factor the existing actual runtime pattern-binding traversal into one private
`frontend/pattern.rs` helper. Both finite lowering and sized generic checking
must call it when they currently bind runtime parameters, let patterns or fold
carry patterns. Share the judgments for a linear wildcard, a repeated name
within the caller's existing name set, and exact immediate tuple/Unit shape.
The adapters retain name insertion/shadow checks, value handling, diagnostic
formatting and all current accounting in the same order.

Do not rewrite declaration signatures or static/runtime duplicate policy in
this unit. Do not introduce a preflight whose success substitutes for actual
binding, a cached checked-pattern certificate, new source acceptance authority,
new syntax, a registry injection, a primitive or a new exported interface.
Do not remove complete unused-declaration, branch, zero-fold or native checks.

## Actual callers and preserved order

The source-input snapshot records exact reviewed file identities.

| Consumer | Current call sites | Requirements for the factor |
| --- | --- | --- |
| `compile/lower/mod.rs::Lowerer::bind` | `call_user_inner` runtime parameters; `block_inner` let statements | Use the caller's existing `BTreeSet<String>`. Runtime-parameter bindings currently share their set across the argument list; each let gets a fresh set. Keep argument type/capacity checks and RHS evaluation before binding. |
| `sized/check.rs::bind` | `declaration` runtime arguments; `Checker::block` lets; `Checker::expr` fold carry | Keep a fresh set per pattern. The separate declaration-wide runtime-name visitor and all static-name policy remain unchanged. A fold uses its already prepared inner scope and explicit carry; no outer quantum capture is added. |
| `sized/elaborate.rs::bind` | concrete arguments, lets and each fold activation | Remains unchanged in this first unit. Its already checked concrete type/value consistency and fresh frame/owner checks continue independently; do not describe it as migrated. |
| `compile/basis.rs::bind_basis_pattern` | Basis parameters and coherent basis binding | Remains unchanged. Classical finite-label binding/injectivity is a separate stage and must not be conflated with runtime owner disposal. |

Existing source-order diagnostics remain observable. The helper checks and
commits one leftmost child before advancing to its sibling, as both existing
binders do. It must not first prevalidate the complete pattern, collect all
leaves, sort names, flatten products or merge error stages. If a later leaf
rejects, the already private checking scope may have earlier mutations; no
partially checked program/facts/accepted handle can escape that failure.

Finite `Compiler::signature` and sized `declaration` keep their current
argument-list/static-name checks, source locations and diagnostic categories.
The finite capability to shadow certain static names and the sized prohibition
remain explicit existing policy differences. This factor does not settle them.

## Borrowed source view, not another AST

The preferred input is directly `common ast::Pattern`. Finite binding already
has that value. Sized generic binding currently has the existing private
projected `sized::ast::Pattern`: Name carries a checked lexical `BinderKey` and
shadow metadata, while let/fold patterns are inside its projected body.

Use an internal borrowed `PatternView` for these two existing representations.
It exposes only Name, Wildcard and the original immediate child slice with the
existing per-node span. Implement the common-AST view in the common helper;
implement the temporary sized view inside its existing private module. Do not
create/copy a common or replacement pattern tree, add another projection/cache,
reparse text or recover original nodes by spelling/span alone. Identical spans
are not lexical identities. A direct-only sized common-AST consumer requires
later checker traversal migration or explicit structural source references;
that larger work is not falsely claimed by this bridge.

All functions and traits are frontend-private. A schematic implementation API:

```rust
enum Node<'a, P: PatternView> {
    Wildcard(Span),
    Name(&'a P::Name, Span),
    Tuple(&'a [P], Span),
}

trait PatternView: Sized {
    type Name;
    fn node(&self) -> Node<'_, Self>;
    fn spelling(name: &Self::Name) -> &str;
}

trait BindingContext<P: PatternView> {
    type Value;
    type Size: Clone;
    type Error;
    fn linear(&self, value: &Self::Value) -> bool;
    fn pattern_type<'v>(
        &self, value: &'v Self::Value,
    ) -> Cow<'v, frontend::types::Type<Self::Size>>;
    fn into_fields(&mut self, value: Self::Value) -> Vec<Self::Value>;
    fn bind_name(
        &mut self, name: &P::Name, span: Span, value: Self::Value,
    ) -> Result<(), Self::Error>;
    // Formatting hooks produce the caller's existing located errors for
    // linear wildcard, repeated name, and tuple/Unit shape failure.
}

fn bind<P, C>(
    pattern: &P, value: C::Value, names: &mut BTreeSet<String>, context: &mut C,
) -> Result<(), C::Error>
where P: PatternView, C: BindingContext<P>;
```

This is a design sketch, not a compiled Rust artifact. Error-hook signatures
may use borrowed actual-type/name data; they must not add a large owned error
or recompute payload types just for formatting. The common helper selects the
three shared rejection judgments. Adapters cannot waive one based on a name,
module, effect annotation or presumed separability.

## Exact shared algorithm

1. Wildcard: use the adapter's current linearity query. Reject a linear value
   with the existing ownership error; otherwise perform no binding.
2. Name: insert its existing spelling into the caller's current name set. On a
   repeat, return its existing duplicate-name error **before** calling the name
   adapter. Otherwise call the existing name insertion adapter once.
3. Tuple: obtain the actual shared `Type<N>` view only here and call its existing
   `pattern_fields(immediate_arity)`. Reject if it returns None. With zero
   children, the established type is ordinary Unit; return without field
   extraction. For nonzero children, release the borrowed type view, consume
   the exact existing payload fields, and bind children left to right using
   the same name set.

The payload field count/order is structurally identical to the checked type:
finite fields come from the existing `Value::into_fields`; sized fields come
from consuming the existing `Type::Kind::Tuple`. No filtering, fallback,
reassociation, implicit quantum splitting or width-based cast is permitted.

The empty pattern matches ordinary Unit only. It rejects `Q<Unit>` and
`Q<Bits<0>>`, both of which own a logical quantum value despite zero physical
wires. A nonempty tuple pattern matches only an ordinary tuple with the same
immediate arity and nesting. `Q<(Bit,Bit)>` remains one owner and requires an
explicit existing split to produce a tuple of owners. `Q<Bits<2>>` is also one
owner and is not the same type as either of those product encodings.

One typed tuple pattern is one function argument. Two separately declared
arguments remain two arguments. The helper receives an already determined
argument value/type; it never packs, spreads or left-folds the argument list.

## Adapter-specific state and capacity

Finite wildcard uses `Value::owns_quantum()` as it does today. Do not rebuild
`value.ty()` for every wildcard/name, which would copy product/type trees and
introduce allocation/work absent from the current path. Finite tuple matching
uses its existing `value.ty()` allocation once, retains the existing quantum-
owner help text and Name-versus-Tuple spans, then uses the existing
`into_fields()` allocation. Pair and general Tuple representation stay intact.
Keep earlier argument/tree/work charges, Env/register/caller-frame accounting,
tuple diagnostic origins and dynamic register IDs unchanged.

Sized matching borrows its existing `Type<Linear>` for the tuple shape test and
then moves its owned tuple field vector. Do not clone that type/vector or build
another fields list. `bind_name` keeps its current order: type boundedness,
retained scope-cell capacity, static/index-shadow prohibition, live-owner-shadow
rejection, checked fresh binding identity, removal of the lexical shadowed key,
and insertion. Its limits remain 4096 inferred type cells/depth 64 and 16,384
retained scope cells. Dynamic identities remain distinct from source BinderKey.

Shared recursion uses only the current already bounded pattern/type depth;
it adds no all-leaf buffer or independent full-tree pass and raises no limits.
The spelling-set allocations are exactly those already made by both binders.
Keep parser/source capacities, source-order failures and scope-closure checks.

RHS evaluation still precedes new binder insertion. A consumed/hidden local
continues to resolve as that lexical local and cannot fall back to a global
declaration with the same name. Name spelling is for diagnostics and duplicate
policy; storage and shadowing use the existing BinderKey/Table facts, not a
new string-keyed ownership map. A repeated fold/call gets its existing fresh
dynamic bindings, never a reused source-owner ID.

## Bounded first-source examples and acceptance

These are desired cases for the separate actual experiment, not invented test
results. Capture original commands/diagnostics before implementation.

| Case | Required observation/rule |
| --- | --- |
| `fn f(u: Unit) -> Unit { let () = u; () }` | Ordinary scalar Unit empty pattern succeeds. |
| `fn f(q: Q<Unit>) -> Unit { let () = q; () }` | Type/shape rejection; zero width does not erase the owner. |
| `fn f(q: Q<Unit>) -> Unit { let _ = q; () }` | Linear wildcard rejects. |
| Corresponding Q<Bits<0>> negative | Sized rejects owner disposal; finite retains its earlier unsupported register-profile diagnostic, with no retry. |
| `fn f((a,b): (Q<Bit>,Q<Bit>)) -> (Q<Bit>,Q<Bit>) { (a,b) }` | One exact tuple argument binds its two immediate owners. |
| Nested `((a,b),c)` with exact nested type; mismatched nesting | Exact tree succeeds; same-width incorrect tree rejects. |
| `let q = h(q)` versus hiding live `q` with a fresh init0 result | RHS move makes ordinary rebinding legal; a live old owner still rejects at its existing stage. |
| Duplicate names in one pattern and across runtime parameters | Preserve each caller's actual existing code/span/order; no global per-block name set. |
| Use a consumed local whose spelling equals a helper | Reject the local use; never invoke the helper as a fallback. |
| Invalid unused sibling; invalid zero-fold/both-branch pattern | Whole current preparation rejects before a checked preparation or proposal is published. Earlier per-entry native checks are not ruled out; preserve the existing route's order and observed calls. |
| Two independent defects ordered left-to-right | The same earlier type/duplicate/capacity failure wins; do not replace it with bulk prevalidation. |

Use existing small quantum cases only. Compare real text/JSON diagnostics,
exit codes, native-call counts and bounded proposal/artifact bytes where a
comparison is claimed. Current Rust and actual MSRV checks cover the changed
finite/sized binding consumers plus existing ownership/type/effect/selected
CLI suites. Keep all prior actual failure records; a successful parser, helper
or output-IR check does not establish source preservation. No maximum case is
newly generated. Independent review must verify the helper is consumed in
actual binding and that hooks preserve accounting/error order.

## Constitutional impact and later gates

QS-2026-01 keeps exact argument/type trees, linear disposal, lexical and dynamic
identity, eager evaluation, caller frames, effects, phase and reference-sensitive
meaning. This factor introduces no separability assumption. PR-2026-01 retains
the exact source/provider/request/artifact binding and every independent native
acceptance path; ordinary pattern binding neither performs a physical map nor
grants inverse/control access. RS-2026-01 remains a pending quantitative program
resource obligation; source/type/work limits are engineering capacities, not a
resource theorem. EXACT-2026-01 supplies no epsilon substitute or new exception.

Both admitted ordinary QLV1 ownership/scope guarantees keep their existing
premises and evidence. They do not automatically certify this source factor,
the sized hierarchy route or runtime preservation. Broader QS/PR/RS/EXACT
obligations remain pending. No protected text, interpretation, admission event,
ledger status, dependency, edition or native rule changes are proposed. AI cannot
adopt an interpretation or guarantee; this draft performs no such act.

The completion claim is restricted to the shared **runtime pattern-rule unit**.
It does not finish common declaration/signature/body checking, scope-policy
convergence, Basis/Meaning/with_computed/qif support, generic Nat/Bits/fold
convergence, canonical std/QFT exposure, namespace migration, #32/#317 or any
release gate. The complete common collection must eventually be checked before
finite/Raw/hierarchy eligibility and canonical std migration; no incompatible
private/unused declaration may be hidden to reach that later gate.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
