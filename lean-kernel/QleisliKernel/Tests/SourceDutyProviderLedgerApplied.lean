import QleisliKernel.Qirf.SourceDutyProviderLedger

/-! The smallest mixed bare/applied completeness control uses one original
Op actual containing both forward leaves. Every original entry and per-demand
provider ordinal is retained, including closed children under zero power and
an unused formal. The one final graph supplies both concrete programs; no
provider gets a separate root or a silently omitted body. This remains the
provider subset, with Meaning/selected-root/general-supplier duties pending.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderLedgerApplied
open QleisliKernel Finite SourceTypes Qirf

private def sourceA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn stamp[const A: Basis, const n: Nat](q: Q<A>) -> Q<A> {\n    global_phase_eighth(q)\n}\nunitary fn keep(q: Q<Unit>) -> Q<Unit> { q }\npub unitary fn route[const unused: Nat](s: Q<Tag>, q: Q<Unit>) -> (Q<Tag>, Q<Unit>) {\n    b::choose[then_op(stamp[type(Unit), 7], keep)](s, q)\n}\nfn main() -> Unit { () }\n"
private def sourceB : String := "#![no_implicit_prelude]\npub unitary fn choose[const U: Op<Unit>](s: Q<a::Tag>, q: Q<Unit>) -> (Q<a::Tag>, Q<Unit>)\n    requires Applicable(U), Controllable(U) {\n    qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }\n}\n"

private def zeroB := sourceB.replace "a::Tag::A => U, a::Tag::B => U"
  "a::Tag::A => power(U, 0), a::Tag::B => power(U, 0)"
private def unusedB := sourceB.replace "qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }" "(s, q)"

private def program (phase : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[],0⟩],[],if phase then [.pure (.applyUnitary 0 1 [⟨[],.monomial [] [0] [1]⟩])] else [],
    [if phase then 1 else 0],[],.unitary⟩

private def artifact (b : String) (omitted : Bool) : Artifact :=
  ⟨#[program (!omitted),program false],#[],#[("a",sourceA),("b",b)],0,none⟩

private def itemRequests {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (omitted missingBare : Bool) (item : GenericDutyQueue.Item catalogue) :
    (planned : SourceDutySlots.ItemExpectation queue item) → SourceDutyProviderLedger.ItemRequests queue item planned :=
  match item with
  | .demand _ _ => fun _ => fun _ provider _ =>
    if provider.2.name == "stamp" then
      let offset := provider.2.signature.original.occurrence.body.head?.map (·.span.startByte) |>.getD 0
      (.pure 0,.mk [⟨offset,0,if omitted then 0 else 1⟩] [] [] [] [])
    else (.pure (if missingBare then 99 else 1),.mk [] [] [] [] [])
  | .header .. | .call .. => fun _ => ()
  | .pendingRecursion .. => fun impossible => nomatch impossible

private def requests {sources catalogue queue} (plan : @SourceDutySlots.Plan sources catalogue queue)
    (omitted missingBare : Bool) : SourceDutyProviderLedger.Requests plan :=
  fun entry => itemRequests queue omitted missingBare entry.subject entry.subjectExpectation

private abbrev Address := Nat × SourceDutyProviderLedger.Branch × String × List Nat

private def addresses {artifact catalogue queue item planned}
    (prepared : @SourceDutyProviderLedger.ItemPrepared artifact catalogue queue item planned) : List Address :=
  match prepared with
  | .demand _ _ _ source => source.providers.map fun provider =>
    (provider.index.val,provider.prepared.branch,provider.provider.2.name,provider.provider.1.path)
  | .header .. | .call .. => []

private def complete {artifact catalogue queue item planned}
    (prepared : @SourceDutyProviderLedger.ItemPrepared artifact catalogue queue item planned) : Bool :=
  match prepared with
  | .demand _ _ original source =>
    source.providers.map (·.index.val) == List.range original.providers.length &&
      source.residual.pending == original.pending
  | .header .. | .call .. => true

private def describeProvider {artifact : Artifact}
    {catalogue : GenericCatalogue.Checked artifact.sources} {record : GenericDutyQueue.RecordIndex catalogue}
    {invocation : GenericDutyQueue.Invocation catalogue record} {demand : GenericDutyQueue.Demand invocation}
    {view : SourceDutySlots.View demand.transported.subject.description}
    {provider : SourceDutySlots.Provider demand view} {prepared : SourceDutyProviderFresh.Checked provider}
    {request : RuntimeProviderHeader.Request} {header : SourceDutyProviderHeader.Checked artifact prepared request}
    (root : Validity.Root)
    (source : @SourceDutyProviderBody.Discovered artifact catalogue record invocation demand view provider prepared request header)
    (checked : SourceDutyProviderBody.Checked source root) : Nat := checked.body.result.actions.length

private def describe {artifact : Artifact} (root : Validity.Root)
    (contribution : SourceDutyProviderBody.Contribution artifact) : SourceDutyProviderBody.Result root contribution → Nat :=
  match contribution with
  | .provider source => fun checked => describeProvider root source checked

private def actual (b : String) (omitted : Bool := false) (missingBare : Bool := false)
    (incompleteOrder : Bool := false) :
    WorkM (List Address × List Nat × Bool) := do
  let artifact := artifact b omitted
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let ledger ← SourceDutyProviderLedger.read artifact plan (requests plan omitted missingBare)
  let positions := ledger.entries.flatMap fun entry => addresses entry.prepared
  let every := ledger.entries.map (·.index.val) == List.range plan.entries.length &&
    ledger.entries.map (·.source.index.val) == List.range queue.items.length &&
    ledger.entries.all (fun entry => complete entry.prepared)
  let contributions := ledger.providerContributions
  guard (positions.length == contributions.length) .request
  let order := if incompleteOrder then #[0] else #[0,1]
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order
    (contributions.flatMap SourceDutyProviderBody.Contribution.rows)
    ((artifact.root :: contributions.flatMap SourceDutyProviderBody.Contribution.roots).eraseDups))
  let final : SourceDutyProviderBody.Final artifact :=
    ⟨contributions,order,root.val,by with_reducible exact root.property⟩
  let checked ← SourceDutyProviderBody.read final
  return (positions,checked.entries.map (fun entry =>
    describe final.root (final.contributions[entry.index.val]'entry.index.isLt) entry.result),every)

private def pair : List Address := [(0,.applied,"stamp",[0]),(1,.bare,"keep",[1])]
private def zeroPair : List Address := [(0,.applied,"stamp",[0,0]),(1,.bare,"keep",[0,1])]

-- Mixed source kinds occupy separate original provider ordinals at the formal
-- A/C duty and each of the two written arm duties. Header links add no copy.
#guard (actual sourceB).run 10000000 |>.1.toOption ==
  some (pair ++ pair ++ pair,[1,0,1,0,1,0],true)
#guard (actual zeroB).run 10000000 |>.1.toOption ==
  some (pair ++ zeroPair ++ zeroPair,[1,0,1,0,1,0],true)
#guard (actual unusedB).run 10000000 |>.1.toOption == some (pair,[1,0],true)

-- An inert enclosing execution does not discharge either actual forward body.
#guard (match (actual zeroB true).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual unusedB true).run 10000000 with | (.error .equation,_) => true | _ => false)

-- A supplied request cannot remove provider ordinal 1. Its actual missing
-- forward subject refuses instead of constructing a shorter complete ledger.
#guard (match (actual sourceB false true).run 10000000 with | (.error .request,_) => true | _ => false)

-- Both genuine forward subjects are roots. The original incomplete schedule
-- is retained as the observed graph-invalid negative, rather than dropping
-- the identity provider root or granting it authority from the phase root.
#guard (match (actual unusedB false false true).run 10000000 with | (.error .invalid,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderLedgerApplied
