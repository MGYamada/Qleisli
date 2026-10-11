# Implementation review: shared parameter-name claiming

Status: additive local technical review of the frozen `candidate-01.md`, not
normative, adopted, implemented or tested. This reviewer did not author that
candidate. Root must first preserve the separate first-source observations and
post the concrete ordinary Issue contract before authorizing production edits.

The reviewed current source is at observed HEAD
`7e2bf08cb2a9367e1d5fefe8ced451c3e6f57149`. That observation is not a trusted
constitutional base or a build attestation. The earlier candidate's recorded
HEAD and pending validation statements remain unchanged as historical context.

## Minimal three-file implementation

1. `src/frontend/pattern.rs`: add a frontend-private one-name `claim` and an
   iterative `claim_pattern_names` over the original common `ast::Pattern`.
   Keep the existing runtime value binder and its borrowed temporary sized
   view unchanged. Declaration spelling checks neither construct a value nor
   grant an owner, effect, operation capability or native accepted handle.
2. `src/frontend/compile/mod.rs`: replace only the static insertion and current
   per-argument name visitor inside `Compiler::signature`. Keep its combined
   static/runtime borrowed-string set and all type/basis/return stages in place.
3. `src/frontend/sized/check.rs`: pass the exact original common `Decl` into
   the existing `declaration` call, use its static names and per-argument
   original patterns at the former insertion/visitor locations, and retain
   the projected kind/type/BindingName for current semantic work. Do not
   replace `Function`, change its projection, add a parallel header cache or
   change `ParsedProgram`/Resolution representation.

No changes to `sized/ast.rs`, `sized/parser.rs`, `sized.rs`, lexical Table,
public APIs, source capacities, stdlib, native rules or dependency versions
are required for this bounded unit. A lexical Table identity getter is a
possible separate cleanup, but is unnecessary when the caller already has
the actual resolved `DefId` used by its existing typed pass.

The following private API is schematic, not compiled code:

```rust
fn claim<K: Ord, E>(
    names: &mut BTreeSet<K>,
    key: K,
    duplicate: impl FnOnce() -> E,
) -> Result<(), E>;

fn claim_pattern_names<'a, E>(
    pattern: &'a ast::Pattern,
    names: &mut BTreeSet<&'a String>,
    duplicate: impl FnMut(&ast::Ident) -> E,
) -> Result<(), E>;
```

`claim` owns the insertion/repeat judgment and constructs its error lazily only
on a repeat. The actual keys are the unchanged common `Ident.text`: finite
static/runtime and sized runtime borrow it; sized static clones it once, as
its current owned-string set already does. A generic key type is solely a
storage/lifetime distinction, not permission to alter spelling or waive a
repeat. Each caller retains its current error category, message and span.

The pattern visitor starts with the existing `vec![pattern]` work stack. Pop
one node: Name invokes `claim`, Tuple extends the stack with its immediate
children in reverse, and Wildcard does nothing. This visits Name occurrences
left to right without recursion, an all-leaf buffer, tree copies, flattening,
a second pass or new capacity. Invoke it for one argument at a time, never
pre-scan the whole header ahead of each argument's current type/binding work.

## Exact original declaration association

`check::program` already has a resolved `DefId` for each actual projected
function. At that existing point, retrieve the original declaration using
the same structural mapping already used by the effect-assertion pass:

```text
program.resolution.declaration(id)
  -> resolved module identity and ast_index
  -> program.syntax(resolved module).decls[ast_index]
```

Pass that borrowed declaration alongside the current `Function`. Do not find
an original declaration by spelling/span, pair two sorted lists, zip them,
reparse source text, clone the header or recover nodes from diagnostic spans.
The caller's existing resolution lookup establishes the actual `DefId`; it
does not authorize a separate spelling search through original declarations.
Module and source order remain the existing program loop order, not DefId
allocation order (Resolution assigns IDs after sorting declaration names).

Check both cardinalities unconditionally at the private paired-declaration
entry, before ordinal access:

```text
projected.parameters.len() == original.static_params.len()
projected.arguments.len() == original.params.len()
```

Then enumerate the current projected loops and index the exact original
parameter at the same ordinal. Do not use `zip`, including a zip preceded
only by debug assertions: release checking must not silently accept a prefix.

Hard `assert_eq!` checks are appropriate existing private construction
invariants here, rather than new language diagnostics. The actual constructor
projects every common static parameter and every runtime parameter with
`map(...).collect`; module projection similarly maps every declaration and
rejects unsupported forms instead of filtering them. `parse_inputs` rebuilds
each indexed function at Resolution's exact `ast_index`, and `ParsedProgram`
keeps its source/projection/Resolution fields private. No legitimate current
untrusted text or public caller can create unequal paired cardinalities. A
failure means an internal projection defect and must halt rather than publish
an accepted prefix. These count assertions do not prove semantic preservation
of the projection; its exact constructor/ordinal correspondence still requires
ordinary source review and remains outside the two admitted Lean guarantees.

Finite public mutable `Project` does not enter this sized pair assertion.
`process_loaded_project_details` resolves and builds declaration references
from the actual current Project AST for every invocation, then applies its
existing profile, lexical and topological stages. Signature still consumes
that current common Decl. Keep its name visitor iterative so externally
constructed patterns do not acquire a new parser-depth assumption, recursive
name walk or stale SourceCollection/header authority. This preserves that
visitor's existing bounded traversal; it does not claim the complete mutable
AST pipeline is proved or generally free of recursion.

## Preserved stage, allocation and diagnostic order

Finite signature first claims all static names, then for each argument claims
its original pattern names, classifies its whole type, performs the existing
non-name Basis-pattern label/shape check where applicable, and advances.
Return-type classification remains last. Keep Ownership, each repeated
identifier's own span, `duplicate static parameter` and
`duplicate parameter name` unchanged. Profile rejections and earlier finite
native checks stay at their existing outer stages.

Sized declaration retains the current static loop's interleaved Natural
BinderKey/Linear insertion. Its static name claim uses the original text
clone, but its error remains code `name`, the complete Function span and
`duplicate static parameter NAME`. Then preserve natural premises/feasibility,
preceding Nat/Basis/Op kind construction and access requirements in exactly
their current order. The lexical table's recording of all static names does
not make a later Nat or Basis legal in an earlier kind.

Only after those stages does the runtime-only borrowed name set scan each
original argument pattern. Preserve `name`, the repeated original Name span
(the projection currently copies exactly that Ident span) and
`duplicate runtime parameter`. The projected argument type and actual shared
runtime binding follow immediately, with the current boundedness, retained
scope, static/index-shadow, live-owner-shadow, fresh dynamic ID and insertion
order unchanged. Return type, full body/scope, effects and dependency checks
remain where they are.

Finite therefore continues to reject a static/runtime parameter collision in
its combined name set before that argument's type; sized continues to reject
it at actual bind after type/capacity checks. The common helper must not
silently unify those existing stages or categories. Each typed pattern remains
one argument; tuple/Unit/Q-owner shape belongs to the existing type/value
checks, not this spelling visitor. Both unused/private declarations and the
existing zero-fold/both-branch checks remain complete. Earlier native checker
calls are not excluded; a failed complete preparation publishes no checked
preparation/proposal.

## Review risks and bounded acceptance

- A bulk header scan would change which duplicate/type/kind/access failure
  wins. Compare the captured per-argument diagnostic order, not just rejection.
- A recursive visitor would change behavior for manually constructed common
  patterns. Retain the original iterative work stack and allocations.
- Changing sized static keys from owned to borrowed, or cloning sized runtime
  names, changes retention/allocation without helping the unit. Preserve each.
- Original/projected tuple and ordinal association comes from the actual
  complete constructor, not equal widths, spans, names or successful output IR.
- Every actual signature/declaration route must consume the shared helper;
  a separate unused preflight is insufficient. Do not remove native checks or
  claim the helper proves source meanings.

The separate first-source study should freeze its actual tiny source files
and record real finite/selected text/JSON diagnostics, exit values, native
argv/counts and proposal bytes before editing. Root will determine actual
observations; this review performed no new Qleisli/native command, Rust/Lean
build or test, and predicts no measured result for the new nine projects.
After implementation, the fixed after study must guard all original records
and current inputs and compare actual outputs. Any repair keeps its genuine
failure and original source history. No maximum-size case is introduced.

## Constitutional scope

The applicable adopted requirements remain QS-2026-01, PR-2026-01,
RS-2026-01 and EXACT-2026-01. Current raw names/types/owners/effects and the
source/request/artifact binding must be preserved; this refactor supplies no
approximate replacement, separability assumption, new capability or resource
theorem. The broader obligations remain pending. Only the two scoped ordinary
QLV1 ownership/scope guarantees are admitted, with their original meanings,
premises and current evidence. They do not certify this source refactor,
sized hierarchy or runtime meaning.

For this review, `python3 scripts/check_constitution.py --base-ref
faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2` returned exit 0 after rereading
startup originals. That is identity/continuity checking, not fresh Lean replay,
human adequacy/adoption, full constitutional CI or release approval. No
protected record, edition, dependency, stdlib or native rule is proposed for
change. Complete common type/kind/declaration/body checking, Basis/Meaning,
canonical std/QFT and all remaining #32/#317 criteria stay pending.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
