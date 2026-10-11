# Direct original-AST source judgment: next-unit candidate

Non-normative, **not adopted**. Prepared read-only by
`/root/isometry_cli_tests` after the phased formal implementation and its four
post-implementation controls. This note changes no production, source fixture,
public contract, Issue criterion or guarantee. No compiler/test/CLI/native/build
was executed for this analysis. Root owns before-code decisions and validation.
Reading a source file is not a stable implementation review or build result.

## Recommended coherent unit

Implement one mandatory **whole-source generic judgment over the retained
original common AST**, before any finite/Raw/hierarchy eligibility decision.
It must own actual checked declaration interfaces and complete type, owner,
access, termination and principal-effect judgments, used by both adapters. A
second syntax tree, one more accessor/visitor helper, a union of profile-success
flags or a fallback from one existing checker to the other is insufficient.

This is substantially larger than the preceding seven-file factor. The current
union of existing source forms has to be covered. Type/owner facts are not
accepted IR evidence: existing concrete cleanup, injectivity, Meaning/provider,
output-IR and native checks remain mandatory and separate. No QFT-name privilege
or new native primitive is needed. The unit is bounded by existing source/work
limits and small tests, not by pretending that its semantic scope is a tiny
helper. Canonical std exposure and atomic namespace migration stay later gates.

## Actual obstacles

`ParsedProgram::parse_inputs` completes `sized::parser::project` for each module
before parsing the next, then makes a second indexed projection and calls
`sized::check::program`. Projection rejects Basis/Meaning declarations,
Meaning-refined Op, qif, coherent/computed forms and several static operator
constructors before semantic checking. The current generic checker consequently
cannot inspect the whole bundled sources. Its provider path also refuses a
primitive reference as an operation, even when the primitive has an existing
finite contract. Retaining a declaration name is not enough.

Finite `process_loaded_project` calls `profile::check` before its lexical Forest
and source/generic checks. It rejects Nat/Basis/Bits/predicates/static-fold/direct
controlled forms before their semantic errors are observable. Its abstract
generic checker constructs discarded placeholder IR through Lowerer; concrete
functions run native checks. That concrete path must remain, but cannot be the
sole generic frontend when source checking precedes lowering eligibility.

The fixed registry's actual four sources are ordinary bodies:

- transforms has qif arms referring directly to sealed id/s/t, with exact
  split/join tree order;
- arithmetic uses toffoli as well as cnot/x;
- basis has two total, noninjective two-argument predicates;
- routines includes private basis nonzero2 and **with_computed**, plus Z,
  observation and a retained-meter parity instrument.

Therefore Basis plus qif support alone does not complete bundled std checking.
Skipping routines/private nonzero2, substituting selected-only bodies or
replacing noninjective predicates with primitives would violate the contract.
Current phase_eighth is scalar phase, not T; it cannot repair the t catalog gap.

## Concrete implementation boundaries

Use a private `frontend::check` module with checked interfaces and source
obligations, not another AST. Port the actual current sized symbolic judgment
to borrowed original Decl/Type/Natural/Block/Expr/Pattern nodes. Reuse common
types, Formals, pattern rules, ordinary Boolean rules and BodyEffects. Port the
finite-only source judgments rather than invoke its lowerer as an oracle.

Likely production touch points, to refine in the concrete before-code contract:

1. `frontend/mod.rs` and new `frontend/check/{mod,scope,types,basis,operations}.rs`:
   whole-program entry, interfaces, scope/owner transitions and existing form
   judgments. The split is implementation organization, not distinct policies.
2. `resolve.rs` / `resolve/locals.rs`: original occurrence lookups and source
   primitive signature lookup independent of emitter eligibility. Every
   primitive must retain its actual existing contract and type/effect rule;
   taking the union of name strings is insufficient.
3. `sized/linear.rs`: retain the existing normalization/solver with a borrowed
   original-Natural lookup, including preceding-key restrictions and recursive
   error order. Do not eagerly scan Natural names or recreate projected trees.
4. `compile/mod.rs`, `compile/profile.rs`, `compile/basis.rs` and
   `compile/lower/operations.rs`: consume the common source judgment before
   profile decisions; keep finite table/evidence/native work. Retire the old
   generic source authority only after replacement rules cover its forms.
5. `sized.rs`, `sized/check.rs`, `sized/parser.rs`, `sized/elaborate.rs`: source
   checking uses originals and common facts, not Function projections.
   Existing concrete projection, if temporarily retained, becomes a later
   lowering adapter. It must never filter the original source collection,
   publish unchecked facts or reject a declaration before the common judgment.
   An unsupported lowering obligation remains a located refusal, not success.

No Lean/native rule, source schema, dependency, edition, std body or corpus
upstream change belongs in this unit. Source-checking support for an existing
primitive does not grant new emitter support.

## Original occurrence lifetime and accounting

The caller borrows the complete original source collection immovably for one
check. Build each existing Index once for its actual DefId/module/ast_index;
retain temporary indexes during that borrow. Type/Natural/name use lookups
consult these indexes at the real node, not spelling/span or an index of a
newly copied tree. Cross-declaration calls consume already checked interfaces,
not a freshly reindexed callee body. Return owned checked types, actual numeric
BinderKeys/Table facts and obligations; never retain address maps inside a
movable ParsedProgram. A later concrete pass can use its existing lifetime-safe
lookup over originals. Mutable public Project input must be checked afresh.

Keep lexical BinderKey and dynamic owner/binding instances distinct. A fold
binder can have multiple execution instances. Exact tuples, Q<Unit> and
Q<Bits<0>> retain linear owners, even when width is zero. Each RHS/runtime
argument is checked in source order before binding. Dead arms and zero folds
still check type/access/effect/owners and call dependencies. Fold quantum
capture enters only through explicit carry; both ordinary/static branches
reconcile owner states and exact result trees. Keep actual Natural decrease
checks before effect fixed-point solving; no mutual recursion is admitted.

Keep each entry's existing byte/parser bounds, 4096-cell/depth64 type bounds,
finite basis-domain12-bit/work1,000,000 bounds, selected Basis8-bit,
100,000-cell preparation,1024 calls/folds, depth16 and10,000 concrete steps.
Their stages and counters need an explicit crosswalk; the common pass must not
add an unaccounted second tree/owner table or spend no work before an allocation.
Do not generate maximum cases to validate this crosswalk.

## Required semantic coverage and evidence boundary

Check every declaration, including private/unused Basis/Meaning and runtime
definitions, every original parameter/requirement and every body occurrence.
Basis typing checks exact declared argument arity/tree and result, Boolean
operands, calls, cycles and total supported expression syntax. Noninjectivity
of xor2/and2 is valid for an ordinary basis function; an enclosing coherent
lift must still establish its own full-map injectivity at its existing gate.

qif evaluates/consumes control then target and requires the correct Controlled
access of each arm. Arms must preserve the complete exact target basis and have
principal Unitary effects; a name or effect assertion grants no capability.
All existing static operator constructors need their current typed access
algebra, including distinct inverse/control/conjugation permissions and Meaning
references, without a favorable closed provider repairing an invalid body.

CoherentLift, WithComputed and CertifiedComputed need their existing source
arity/type/capture/owner/effect rules in the common pass. Keep the legacy and
protected three-argument scopes distinct. Exact injectivity, computed cleanup,
Meaning equation/provider and reference-extension checks remain concrete
obligations of the existing gates. Do not report an unresolved obligation as a
generic clean/evidence proof or allow it to authorize run/output acceptance.
Principal effects cover all checked branches/callees; annotations remain upper
bounds and the externally-unitary semantic rejection stays explicit.

## Tiny desired controls

Preserve first actual outputs before changing gates. These are desired existing
forms, **not executed programs or new APIs**:

```qli
use std::quantum::split;
use std::quantum::join;
use std::quantum::id;
use std::quantum::s;
pub fn quarter(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> {
    let (c,q)=split(q);
    let (c,q)=qif(c,q){0=>id,1=>s};
    join(c,q)
}
fn sized_identity[static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> {
    for static i in 0..n carry a=q {yield a}
}
pub fn main()->Unit {()}
```

This combines a finite qif body and an unused generic Nat/fold body in one
unchanged source collection. Add independent malformed variants in the private
fold/body, wrong qif access/type/effect, forward kind and both Natural/Basis
diagnostic phases. A valid main cannot hide these errors. Source judgment and
the existing finite lowering refusal must be recorded separately.

Also use private `basis fn nonzero2((a,b):(Bit,Bit))->Bit` and a correct/incorrect
with_computed wrapper from the existing actual rules; a two-argument predicate
must fail the one-explicit-domain contract rather than be silently tupled.
Check all four **unchanged** registry ASTs before a private preparation success
is claimed. Existing fixed qft2/qft3 contracts and licensed generic qft study
provide separate controls; instantiate only N=0,1,2,3 when root authorizes it.
Closed native checks remain fresh and independently requested where applicable.
Names, round trips and uniform probabilities are not Fourier contracts.

## Scheduling and mechanical completion

The change intentionally moves semantic checks ahead of profile eligibility;
old Unsupported-first outputs cannot all remain identical. Record explicit
old/new priorities in #32 before code and preserve originals. Keep parsing and
source-size errors at their adapter boundary, then complete collection and
resolution, original indexes, declaration/premise/ordered-kind/access stages,
all body rules, cycle/decrease/effect solution, then lowering/evidence/native
eligibility. The existing full Basis-parameter scan before Natural normalization
and source-order failing declaration must remain concrete, tested priorities.

Temporary module-cycle/self-import and static-shadow differences are documented
already. This note does not silently choose a new policy. The before-code
contract must explicitly retain an adapter compatibility boundary or record an
ordinary source migration before claiming one canonical source policy. A
profile tag hidden inside type/owner rules would not establish convergence.
Such ordinary implementation decisions under existing interpretations are not
a new Guardian interpretation or guarantee admission.

Mechanical exit requires both public paths to consume the same actual generic
facts; no early semantic projection/profile barrier; all original declarations
and both branch/zero-fold bodies counted and rejected correctly; the unchanged
four bundles genuinely checked; old finite Meaning/computed/ownership/effect
controls preserved; declared diagnostic migration captured in text/JSON; actual
small proposal/phase/axis/reference/native tests on both toolchains; independent
actual-caller review; current source identity/policy checks. If a source variant
is still semantically unsupported, keep the refusal and label the unit partial
rather than omit it or declare complete common checking/std integration.

Inspected actual paths are those named above, the original ast.rs/types.rs,
effects.rs/source.rs, all four stdlib/src files, STDLIB.md, type-model and
source-text References. Fresh read-only GitHub snapshots: #32 updated
2026-10-05T18:24:49Z and #317 updated2026-10-05T17:27:59Z. Source files were read
during root's current validation, not frozen as a compiled-source closure.
The initial connector calls used an incorrect parameter shape and returned
schema errors; corrected read-only calls supplied repository_full_name and
issue_number and returned those snapshots. No GitHub content was changed.

No general preservation/QFT/resource theorem, canonical std API, release gate,
new guarantee or Issue completion is established. Both protected QLV1 scopes
and pending QS/PR/RS/EXACT obligations retain their current meanings.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
