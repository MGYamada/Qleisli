# Common parameter-name checks — candidate 1

Status: local non-normative read-only design under #32. This is a possible
next bounded implementation unit, not an adopted language rule, implementation,
completed common checker, proof, canonical std API or Issue completion.
No new desired-source check, CLI/native command, build or test was run.

## Governing contracts and actual input

The current Reference type-model and source-text chapters require one typed
pattern to remain one argument, exact tuple/ordinary Unit shape, unique names
across the complete parameter list, distinction from static parameters, linear
quantum disposal and complete checking of unused declarations. Static kinds
refer only to preceding parameters. Existing temporary profile policies and
error order remain in force until an explicit ordinary migration decision.

The retained #32 connector snapshot was read with updated_at
2026-10-05T16:39:34Z. Its common collection, lexical identity and runtime-pattern
contracts do not complete common declaration checking or permit skipped
private/unused declarations. The new runtime pattern helper's first compile
failure and one-line repair are separate historical records; this candidate
neither reruns nor asserts success of its pending parent validation.

The source input map identifies only the inspected files. Current observed
HEAD is b544cd2d96dcc94e0ef29b28e6b08979bca5d9b1; the runtime-pattern unit is
uncommitted concurrent work. Source hashes are not compiled-HEAD attestation
or complete runtime closure. Borrowed common source must come from the same
fresh declaration/Resolution, never a cached approved header or mutable
Project's obsolete parallel snapshot.

## Finite declaration path and order

Compiler::signature in src/frontend/compile/mod.rs reads a common ast::Decl
directly. Its actual sequence is:

1. Scan all static parameters in declared order, inserting the spelling into
   one BTreeSet. A repeat rejects with Ownership, the repeated identifier's
   own span, and "duplicate static parameter".
2. For each runtime/basis argument in order, iteratively visit its original
   common pattern, left to right, using that same set. A repeated spelling,
   including one previously used by a static parameter, rejects with Ownership
   at the repeated name span and "duplicate parameter name".
3. Classify that argument's complete type through the shared classify_source
   path. Basis declarations use Stage::Basis; ordinary/Meaning declarations
   use Stage::Runtime. For a non-name basis pattern, the existing finite
   bind_basis_pattern validates exact shape with label zero.
4. Proceed to the next argument, then classify the declared return type.

There is no bulk all-runtime-name pass before every argument type. For example,
an error in argument1's type can precede a duplicate in argument2. A new helper
must be called per pattern at exactly the former point.

Signature is not the entire public finite checker. process_loaded_project_details
first re-resolves the current mutable Project, applies profile::check to every
declaration, builds lexical tables and orders dependencies. Unsupported static
Nat/Basis, register types, symbolic requirements or other profile forms can
reject before signature duplicate checks. Entry signature checking and ordinary
basis/Meaning/generic/body stages have their own existing order. Static Op
basis/Meaning/access checks live in Compiler::abstract_bindings, after signature,
not in signature itself.

The finite path checks all declarations through its existing topological
passes. An earlier declaration can obtain a native checker result before a
later invalid sibling rejects the complete preparation; a new global
all-signature preflight would alter that observable order and is not part
of this minimal refactor. No failed complete preparation publishes success.

## Sized declaration path and order

The sized path also parses and retains the complete common Module. Its existing
sized::parser projects every supported declaration and exact original patterns,
types and spans before check::program runs. The projection rejects unsupported
forms, including Basis/Meaning declaration categories and Meaning-refined Op
parameters, rather than ignoring them. Common syntax is not sized availability.

sized/check.rs::declaration currently consumes the private projected Function:

1. Scan static parameters in order with a separate spelling set. A repeated
   static name rejects with code name at the complete function span and
   "duplicate static parameter NAME". For each preceding Natural entry, retain
   the actual lexical BinderKey and Linear variable as before.
2. Build the natural context, apply all Predicate premises and check
   feasibility. This happens before installing Basis/Op parameters or
   runtime arguments.
3. Install Basis/Op entries in order. Operation kind checking uses only
   preceding Naturals; preceding Basis entries are retained. All static names
   being recorded by lexical resolution does not make a later parameter legal
   in an earlier kind. Generic type checking, arithmetic and solver budgets
   are separate from spelling uniqueness.
4. Check Access requirements in original order, binding their actual resolved
   operation keys. Access errors and duplicates precede runtime name checks.
5. For each runtime argument, visit every pattern name left to right using
   an initially empty runtime-only set shared across all arguments. A repeat
   rejects with name, its projected name span and
   "duplicate runtime parameter", before that argument's type/binding.
6. Classify that argument under the symbolic scope and call actual bind.
   bind_name then checks type capacity, retained scope capacity, static/index
   shadow, live-owner shadow, fresh dynamic identity and insertion in its
   existing order. A runtime name colliding with a static name is rejected
   here, after its type/capacity checks, rather than by the runtime-only set.
7. Classify the return type. The program caller separately rechecks it before
   the body, then performs complete body/scope/effect/cycle checks.

All supplied private and unused functions are visited in module/source order.
Both static branches and zero-fold bodies remain checked. Host selection and
finite/Raw/hierarchy eligibility do not confer an exemption.

The static duplicate and access diagnostics currently lose some original
identifier specificity: static duplicate uses Function.span; Access uses its
whole requirement span, while finite Access failures use the constraint name
span. This design preserves those observable differences rather than quietly
improving them.

## Duplication and boundaries that are already shared

Both signature and sized declaration independently implement the same iterative
Name/Tuple/Wildcard traversal for runtime parameter uniqueness: tuple children
are pushed in reverse to visit left to right, wildcards introduce no name,
and one set extends across the argument list. Static duplicate rejection also
uses the same spelling-insertion test, with different error adapters.

Source syntax, lexical declaration/binder IDs and basic type constructor rules
are already shared. Runtime binding now has its separate private shared
pattern traversal. Declaration uniqueness must not call a value binder or
invent temporary owners merely to validate names.

The following are not duplicate representations to collapse in this unit:
finite closed Ty versus symbolic Linear Ty, generic natural premises, opaque
Basis kinds, phase-fixed Meaning refinement, access evidence, basis-label
binding, actual runtime-owner scopes and concrete elaboration. They have
different existing responsibilities, not interchangeable certificates.

## Smallest proposed shared unit

Share only source-spelling claiming and the actual iterative runtime
parameter-name scan, over the retained common ast::Ident and ast::Pattern.
The helper's rule is fixed: insert the actual spelling into the caller's
existing set; reject the first repeat before advancing or type/binding work.
Only existing located error formatting is delegated.

Keep each static loop in its caller, including its current interleaved
Natural insertion. A shared one-name claim can preserve current key
representation/allocation: finite currently borrows source strings, sized
static currently owns clones, and sized runtime currently borrows pattern
strings. Do not introduce a new copied pattern tree, all-leaf buffer, cached
success object, certificate, reinterpretation by name or independent policy flag.

The pattern walk remains iterative with the original pending child stack.
Do not reuse a recursive value-binder traversal in a way that changes handling
of the already supported externally constructed common AST beyond parser depth.
No new limit, count-first pass or larger declaration collection is introduced.

A schematic frontend-private interface, not a compiled API:

    claim(set, existing_spelling_key, duplicate_error) -> Result<(), Error>
    claim_pattern_names(common_pattern, same_caller_set, duplicate_error)
        -> Result<(), Error>

The shared implementation owns insertion/repeat rejection and left-to-right
traversal. String keys must be exactly the common Ident.text; existing lifetime/
allocation representation and diagnostics remain in small adapters. No adapter
may waive a repeat based on module origin, visibility, selected entry or effect.

Finite Compiler::signature uses the original common pattern directly and keeps
its combined static/runtime set. Sized declaration should borrow the original
Decl through the existing mapping:

    program.resolution.declaration(id).ast_index
        -> program.syntax(module).decls[ast_index].

The module/source/DefId association is structural, not inferred from source
spans or function spelling. check::program already has this DefId and reads
that same original declaration for effect assertions. Pass the borrowed Decl
into declaration alongside the current projected Function, or use an equivalent
private borrowed declaration view. Index each original static/runtime
parameter at its actual source ordinal, while keeping the current projected
kind/type/BindingName for semantic scope work.

The projection already maps every parameter and argument one for one.
Do not use zip truncation to make mismatched lengths appear valid, select a
replacement AST, pair nodes by span/name, or omit unsupported declarations.
The complete original mapping/count invariant must remain explicit and
reviewed. If it fails, repair the concrete source association before claiming
a shared check; source similarity is not identity.

Sized runtime name scanning still uses an empty runtime-only set. Its current
bind_name continues to reject static collisions after type/capacity checks.
Finite still rejects such collisions through the pre-seeded set. This preserves
the Reference's rejection requirement while retaining actual stage differences.
This unit moves a real check to common source consumption; it does not claim
one complete declaration policy or body checker.

## Preserved actual observations and unexecuted counterexamples

The common-pattern authoring session has an actual frozen duplicate case:

    pub fn entry(q: Q<Bit>, q: Q<Bit>) -> Q<Bit> { q }

Its raw finite JSON reports ownership / "duplicate parameter name"; selected
JSON reports name / "duplicate runtime parameter". Both locate the second q at
bytes99..100, return exit1 and record zero native calls. These are existing
observations read for this audit, not rerun here. Original notices, leading
text, exact manifests and diagnostics are preserved, not reauthored as a new
experiment.

The earlier lexical-resolution study's exact source

    pub unitary fn f[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>
      requires Apply(U){let U=q;U}

has a retained historical result: finite.check ok; sized rejection at75..76,
name / "binding U shadows a static parameter/index or discards a value".
That history is evidence of the explicit temporary local-shadow policy, not
a current rerun or permission to erase it. Its old README also mentions the
then-current one-function restriction, which has since been removed; do not
import that obsolete claim as today's boundary.

The following new sources are suggested future bounded first experiments.
Their results are code-derived predictions, NOT observed outcomes:

| Source/case | What later capture must distinguish |
| --- | --- |
| Duplicate static U in two Op<Bit> parameters, q returned unchanged | Finite repeated-name span/Ownership versus sized full-function span/name; keep earlier profile gates. |
| Static U and runtime U: Q<Bit>, with Apply(U) and runtime U returned | Both reject; finite declaration-name check precedes argument type, sized static-shadow check follows symbolic type/capacity. |
| Duplicate names inside ((a,b),a) with two or three tiny fields | Source-order second occurrence wins; no flattened/reassociated parameter or full-tree prevalidation. |
| First argument has a type error and a later argument repeats a name | Preserve the earlier per-argument type error; do not pre-scan all names. |
| Earlier duplicate pattern plus later unsupported Bits<0> type | Preserve actual finite profile rejection versus sized declaration-stage rejection, without retry/fallback. |
| Op<Bits<n>> kind declared before static n: Nat versus n first | The lexical table's forward name does not waive the existing ordered-kind rule; finite Nat/profile rejection remains separate. |
| Invalid private unused sibling plus valid public entry | Complete preparation rejects; retain actual native counts rather than assuming zero. |
| Valid nested tuple containing Unit and Q<Bit>; two separate parameters | Exact source argument arity/tree survives shared name scanning and actual binding; no manufactured owner or implicit cast. |
| Basis fn with ordinary tuple/wildcard pattern | Finite basis stage and label/shape rules stay intact; sized ordinary-only projection still rejects rather than skips it. |

Keep all systems tiny (zero to three physical bits), with explicit edition2026
manifests. Freeze first executable translations and source maps before any
authorized command. Existing ignored/capacity regressions are not converted
into new maximum-case generation. Any desired canonical convergence syntax
belongs to a separate pending decision rather than an unlabelled implementation.

## Pending ordinary decisions and later gates

The Reference already requires unique parameter names and earlier-parameter
kind dependencies. No new policy is necessary to extract the name visitor.
However, final common checking must explicitly settle the observable boundary:
static/runtime duplicate error categories/spans, global declaration/profile
diagnostic ordering, stage of type/shape errors, and the finite versus sized
local static-shadow rule. Harmonizing these in this unit would be a behavior
change requiring its concrete ordinary Issue contract and migration evidence.

Do not move all-signature checking ahead of existing project profile/native
stages merely to obtain one common phase. The later complete common checker
must verify every original declaration/body before eligibility and canonical
stdlib exposure, but that larger cutover and its diagnostic migration are not
implemented here. It must retain Basis/Meaning, type/kind/owner/effect/access,
static totality, provider identity and source/request/artifact obligations.

Existing QS/PR/RS/EXACT interpretations apply. Both scoped ordinary QLV1
ownership/scope guarantees keep their exact meanings/premises and current
evidence. Broad obligations remain pending. Name uniqueness has no native
acceptance authority, creates no quantum/evidence capability and proves no
source preservation, general family semantics or quantitative resource bound.
No constitution, ledger, adopted record, dependency or edition change is
proposed. This candidate invokes no Guardian authority and earns no completion
credit for #32, #27 or #317.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
