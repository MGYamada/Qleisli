# Lowering state and lexical scope refinement

Status: **scope projection extracted; its lookup model proved in Lean;
whole-lowerer adequacy open** (2026-09-27). This is the first implementation
refinement step for [SPEC-4](../ROADMAP.md). It connects the
[boundary relation BC](source-ir-correspondence.md#1-boundary-relation-and-the-preservation-statement)
to concrete environment operations. It changes no source acceptance rule,
language form, sealed operation, or public API.

## 1. Representations and the boundary

The Rust [value module](../src/frontend/compile/lower/value.rs) separates
lexical bindings from the complete register store:

| Rust representation | Mathematical reading |
| --- | --- |
| `Env = BTreeMap<String, Option<Value>>`, missing key | Absent name: no local binding hides a function. |
| Present key with `None` | Spent binding: it cannot be read, but still hides a function. |
| Present key with `Some(v)` | Live value, with its entire exact mixed type tree. |
| `Value::Quantum(slot, basis)` | One owned port, including when `basis` is `Unit`. |
| `Value::Pair(a,b)` | Ordered mixed value; its ownership occurrence list is the concatenation of the two child lists. |
| `registers[slot]` | Current SSA token, ordered wires, and exact basis for this owned port. |

Registers also cover pending tuple components and actual arguments, suspended
callers, and protected computed inputs. Consequently, counting only the
current `Env` does not establish BC. For a complete boundary, let `H` contain
the visible environment's values, the current result, and all these suspended
holders. BC requires a bijection of their typed ownership occurrences with
the live register slots/tokens, disjoint live wires of the right widths,
consistent classical SSA decoding, and the recorded fresh-ID history.

The Lean `Value` representation uses natural-number identifiers and exact
`Basis` trees. Mapping a well-typed Rust basis/value tree to it is structural;
the finite-map lookup uses `none`, `some none`, and `some (some v)` for the
three distinct states above. The model does not encode Rust execution,
integer capacity, work budgets, or diagnostics. These are refinement
premises, not consequences of a successful Lean build.

## 2. The scope-closing algorithm

[`block`](../src/frontend/compile/lower/mod.rs) snapshots an entry environment
`E`, evaluates statements and the final expression in a separate local map
`L`, and records the names of each successful direct `let` pattern in `B`.
Its result value is already a separate holder when it invokes
[`close_scope`](../src/frontend/compile/lower/scope.rs).

Write `Q(v)` when a value contains at least one quantum leaf. Closure first
rejects if, for some name `n`,

```text
L[n] = live(v) and Q(v) and (n in B or E[n] != L[n]).
```

Otherwise it produces exactly this environment:

```text
E'[n] = absent                        if E[n] = absent
        spent                         if E[n] = spent
        live(v)                       if E[n] = live(v) and not Q(v)
        live(v)                       if E[n] = live(v), Q(v), n not in B,
                                         and L[n] = live(v)
        spent                         otherwise.
```

The Rust function performs a read-only rejection pass before mutating `E`.
It then changes only consumed/rebound quantum entries to `None`. It returns
the first leaking name in the map's lexical order; `block` attaches the
existing `Ownership` diagnostic and whole-block source span. On success,
`block` commits the projected snapshot to its caller. On rejection the
entry map is unchanged. This is not a rollback guarantee for the whole
lowerer: earlier operations may already have changed its private IR/store,
and compilation returns an error without exposing that partial program.

The extraction preserves the previous two-loop algorithm. Previously the
second loop mutated the original caller map, which remained equal to the
entry snapshot while only `local` was evaluated. It now mutates that snapshot
and assigns it back. The two charged environment clones, guard, map iteration
order, and diagnostic remain the same.

## 3. Why value equality needs the rebound set

A move followed by `let q = ...` creates a new lexical binder even when its
value has the same slot and basis as the old one. For example, the body
`{ let carry=q; let q=carry; () }` leaves a new quantum owner unreturned.
Equality of the entry and local values alone would miss that leak; `q in B`
rejects it. The same reasoning applies to mixed tuples and `Q<Unit>`.

In the other direction, a classical branch can replace the token/wires of
an untouched outer owner through a complete phi. The slot and value tree
stay the same, so the original lexical binding must survive. Comparing
register contents instead of values would incorrectly reject this case.

Connecting snapshot equality to the lexical `Close` rule requires the
following trace invariant, separate from the pointwise closure theorem:

1. Original bindings are immutable except for moving a quantum value to a
   spent marker. A successful direct binder insertion records its name in `B`.
2. Nested blocks project their own scopes before returning. Their direct
   binders need not be added to the enclosing block's `B`; their consumption
   of an enclosing owner is already reflected by a spent marker in `L`.
3. While a block evaluates, its caller's map is unchanged. The maps retain
   entry names, distinguishing absent names from spent ones.

These conditions explain the implementation's correspondence by cases.
An induction establishing them for every successful Rust execution is still
required. In particular, the Lean model takes `E`, `L`, and `B` as inputs;
it does not prove that all Rust paths construct the intended three inputs.

## 4. Checked result and conditional BC preservation

[Scope.lean](../lean/Qleisli/Scope.lean) models lookups as functions from names
to `Option (Option Value)`. `Approved E L B` is precisely the absence of the
rejection condition. Its noncomputable `close` specifies universal approval;
the finite Rust map implements a scan of the names that are present.

The [SC theorem ledger](lean-resource-proof.md#7-lexical-scope-projection)
records classical restoration, spent-marker preservation, exact entry-domain
restoration, quantum retention, and rejection of introduced/rebound quantum
owners. `Value.ownsQuantum_eq_true_iff` identifies the Boolean guard with a
nonempty ownership occurrence list; this includes zero-width registers.

The key result, `Scope.close_preserves`, says that successful closure retains
the entry name domain and exactly the current quantum footprint at each
name. `Scope.close_footprintOn` concatenates this equality over any finite
name list. To interpret it as a complete environment footprint, choose a
duplicate-free list covering both finite map domains. No bound on the number
of names, nesting of values, or register width appears in these theorems.

As a paper corollary, suppose the post-body holders `values(L) + result + frame`
and register store satisfy the [resource accounting invariant](lean-resource-proof.md#1-exact-statement-and-model).
Successful scope projection replaces only `values(L)` by `values(E')` with
the same typed ownership occurrences. The result, frame, store, and ID history
are unchanged, so resource coverage and uniqueness still hold. This step
does not itself establish the post-body premise, classical decoding for all
paths, freshness, effects, or quantum meaning. Restoring a classical binding
restores its original immutable SSA identifier; new local classical results
can separately escape in the block's result.

## 5. Surrounding implementation obligations

The following audit identifies where the missing premises must be supplied.
It is a source inspection, not a mechanized Rust semantics.

| Transition | Observed implementation and obligation remaining |
| --- | --- |
| [`input`](../src/frontend/compile/lower/mod.rs) / [`register`](../src/frontend/compile/lower/mod.rs) | Recursively constructs exact value trees and fresh slots/tokens/wires, including empty wire lists for `Q<Unit>`. Prove initial BC, classical port ordering, and capacity/history bounds. |
| [`expr_inner`](../src/frontend/compile/lower/mod.rs), names | Clones classical values, takes the entire quantum-containing value, and leaves `None`. Prove ownership transfer to a temporary holder and that all evaluation contexts include it in the frame. |
| [`bind`](../src/frontend/compile/lower/mod.rs) | Rejects quantum wildcards, duplicate pattern names, and hiding a live quantum binding; decomposes exact pairs and records successful names. Prove the trace invariant through all patterns and nested evaluation. Partial changes on failure are not successful paths. |
| [`block`](../src/frontend/compile/lower/mod.rs) / [`close_scope`](../src/frontend/compile/lower/scope.rs) | Evaluates the final result once and projects the entry scope. The local lookup theorem is checked; its Rust data-structure representation and trace premises remain explicit. |
| [`call_user_inner`](../src/frontend/compile/lower/mod.rs) | Uses a fresh formal environment in the defining module, exact parameter/result types, and a shared register store. Function exit additionally rejects any unconsumed parameter. Prove pending-argument and caller-frame coverage, substitution, and declared-effect accounting. |
| [`branch`](../src/frontend/compile/lower/branch.rs) / [`merge_results`](../src/frontend/compile/lower/branch.rs) | Checks both arm scopes, requires equal residual bindings, pairs quantum results by position and the remaining frame by slot. Register snapshots are restored between arms without rewinding ID counters. Prove complete holder coverage and the finite-map realization of phi/history premises. |
| [`computed`](../src/frontend/compile/lower/mod.rs) | Builds a private scope with outer quantum names masked as spent and retains their registers in the protected frame. Its auxiliary binder can reuse an outer spelling. Prove that the masking/result/cleanup boundary maintains BC and the exact structured certificate. |

The raw verifier has no source lexical names or spent markers. Successful IR
verification therefore cannot replace this scope correspondence. It remains
an independent check on the emitted resource/effect operations.

## 6. Finite implementation evidence and next step

The unit test
[`scope_projection_matches_a_finite_lexical_identity_model`](../src/frontend/compile/lower/scope.rs)
compares **7,225 two-name cases** with an oracle that tracks explicit binder
identities and manually classified linear values. Its eight value states
include spent, unit, classical scalar/product, quantum unit/bit, and mixed
values with quantum ownership on either side. It covers unchanged binders,
moves, fresh binders with equal values,
and fresh binders subsequently moved; rejection must leave the snapshot
unchanged. It is a finite boundary model, not an enumeration of all source
execution traces.

[Source regressions](../tests/source_scope.rs) add three tests containing
eight accepted/executed cases and seven rejected cases. They check nested
classical restoration, equal-value rebinding and non-revival, mixed/zero-width
ownership, pending Bell references across calls and branches, and ordinary/
static name hiding by spent markers. Rejections assert both diagnostic text
and source spans; probability expectations use a direct Bell correlation.
Run results are in the [conformance record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md).

The next step is a compositional state relation for inputs, moves, binders,
and pending/caller holders that establishes the trace and coverage premises
above. Complete branch snapshots/phi and issued-ID history must then preserve
that relation. The general Rust adequacy theorem, verifier correctness,
operator/instrument preservation, and numerical error bounds remain open.
