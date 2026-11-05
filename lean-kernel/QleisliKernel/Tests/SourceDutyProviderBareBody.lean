import QleisliKernel.Qirf.SourceDutyProviderBody

/-! The exact frozen bare-forward first sources use the maintained preparation
entry and actual same-final-root body consumer. The finite provider-only subject
contains only the genuine a/b query rows. An audited unused spare is a separate
final-graph fault, not an invented source-use grant. No runtime handle, wire,
full Meaning graph or whole-catalogue consumption claim is made here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderBareBody
open QleisliKernel Finite SourceTypes Qirf

private def directA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn direct[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::choose[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def transitiveA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn transitive[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::forward[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def sourceB : String := "#![no_implicit_prelude]\npub unitary fn choose[const U: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(U), Controllable(U) {\n    qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }\n}\npub unitary fn forward[const V: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(V), Controllable(V) {\n    choose[V](s, q)\n}\n"

private def spare := "#![no_implicit_prelude]\nunitary fn unused(q:Q<Bit>)->Q<Bit>{q}\n"

private def program (omittedPhase : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],if omittedPhase then [] else [.pure (.gate .z 0 1)],
    [if omittedPhase then 0 else 1],[],.unitary⟩

private def artifact (sourceA : String) (omittedPhase withSpare : Bool) : Artifact :=
  ⟨#[program omittedPhase],#[],
    if withSpare then #[("a",sourceA),("b",sourceB),("spare",spare)] else #[("a",sourceA),("b",sourceB)],0,none⟩

private def item (artifact : Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (wanted : String) (omittedPhase wrongOffset : Bool)
    (entry : GenericDutyQueue.Item catalogue) :
    SourceDutySlots.ItemExpectation queue entry → WorkM (List (SourceDutyProviderBody.Contribution artifact)) :=
  match entry with
  | .demand invocation _ => fun planned => do
    let some root := catalogue.records[invocation.id.root]? | throw .request
    if root.name != wanted then return []
    planned.providers.mapM fun provider => do
      -- The context is untrusted data from the exact original token span.
      -- prepareBare reads the real Body once; discovery checks its event order.
      let some token := provider.2.signature.original.occurrence.body.head? | throw .request
      guard (token.text == "phase") .request
      let context : RuntimeContextRequest.Context :=
        .mk [⟨token.span.startByte+(if wrongOffset then 1 else 0),0,if omittedPhase then 0 else 1⟩] [] [] [] []
      let prepared ← SourceDutyProviderBody.prepareBare artifact provider.2 (.pure 0,context)
      return prepared.contribution
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def pathOnlyProvider {artifact : Artifact}
    {catalogue : GenericCatalogue.Checked artifact.sources} {record : GenericDutyQueue.RecordIndex catalogue}
    {invocation : GenericDutyQueue.Invocation catalogue record} {demand : GenericDutyQueue.Demand invocation}
    {view : SourceDutySlots.View demand.transported.subject.description}
    {provider : SourceDutySlots.Provider demand view} {prepared : SourceDutyProviderFresh.Checked provider}
    {request : RuntimeProviderHeader.Request} {header : SourceDutyProviderHeader.Checked artifact prepared request}
    (root : Validity.Root)
    (_source : @SourceDutyProviderBody.Discovered artifact catalogue record invocation demand view provider prepared request header) :
    WorkM (Nat × OperationPaths.Paths × Nat) := do
  let paths ← RuntimeProviderPaths.read header.binding.header root view.requested
  return (invocation.depth,view.requested,paths.ir.original.program.operations.length)

private def pathOnly {artifact} (root : Validity.Root) (contribution : SourceDutyProviderBody.Contribution artifact) :
    WorkM (Nat × OperationPaths.Paths × Nat) := do
  match contribution with
  | .provider source => pathOnlyProvider root source

private def describeProvider {artifact : Artifact}
    {catalogue : GenericCatalogue.Checked artifact.sources} {record : GenericDutyQueue.RecordIndex catalogue}
    {invocation : GenericDutyQueue.Invocation catalogue record} {demand : GenericDutyQueue.Demand invocation}
    {view : SourceDutySlots.View demand.transported.subject.description}
    {provider : SourceDutySlots.Provider demand view} {prepared : SourceDutyProviderFresh.Checked provider}
    {request : RuntimeProviderHeader.Request} {header : SourceDutyProviderHeader.Checked artifact prepared request}
    (root : Validity.Root)
    (source : @SourceDutyProviderBody.Discovered artifact catalogue record invocation demand view provider prepared request header)
    (checked : SourceDutyProviderBody.Checked source root) : Nat × OperationPaths.Paths × Nat :=
  (invocation.depth,view.requested,checked.body.result.actions.length)

private def describe {artifact} (root : Validity.Root) (contribution : SourceDutyProviderBody.Contribution artifact) :
    SourceDutyProviderBody.Result root contribution → Nat × OperationPaths.Paths × Nat :=
  match contribution with
  | .provider source => fun checked => describeProvider root source checked

private def actual (sourceA wanted : String) (omittedPhase consumeBody : Bool)
    (withSpare : Bool := false) (wrongOffset : Bool := false) :
    WorkM (List (Nat × OperationPaths.Paths × Nat)) := do
  let artifact := artifact sourceA omittedPhase withSpare
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let contributions ← plan.entries.mapM fun entry =>
    item artifact queue wanted omittedPhase wrongOffset entry.subject entry.subjectExpectation
  let contributions := contributions.flatten
  guard (!contributions.isEmpty) .request
  let rows := contributions.flatMap SourceDutyProviderBody.Contribution.rows
  guard (rows.any (fun row => row.1 == "a") && rows.any (fun row => row.1 == "b") &&
    !rows.any (fun row => row.1 == "spare")) .request
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact #[0] rows
    ((artifact.root :: contributions.flatMap SourceDutyProviderBody.Contribution.roots).eraseDups))
  let final : SourceDutyProviderBody.Final artifact :=
    ⟨contributions,#[0],root.val,by with_reducible exact root.property⟩
  if consumeBody then
    let checked ← SourceDutyProviderBody.read final
    return checked.entries.map fun entry =>
      describe final.root (final.contributions[entry.index.val]'entry.index.isLt) entry.result
  else contributions.mapM (pathOnly final.root)

private def ac : OperationPaths.Paths := ⟨true,false,true⟩
private def c : OperationPaths.Paths := ⟨false,false,true⟩

-- All original instances/child uses remain ordered, with the formal A/C
-- demand distinct from the two written qmatch control demands.
#guard (actual directA "direct" false true).run 10000000 |>.1.toOption ==
  some [(1,ac,1),(1,c,1),(1,c,1)]
#guard (actual transitiveA "transitive" false true).run 10000000 |>.1.toOption ==
  some [(1,ac,1),(2,ac,1),(2,c,1),(2,c,1)]

-- Correct Z and coordinated identity both have actual path evidence. Only
-- the original-body continuation distinguishes their phase at the SAME root.
#guard (actual directA "direct" false false).run 10000000 |>.1.toOption ==
  some [(1,ac,1),(1,c,1),(1,c,1)]
#guard (actual directA "direct" true false).run 10000000 |>.1.toOption ==
  some [(1,ac,0),(1,c,0),(1,c,0)]
#guard (actual transitiveA "transitive" false false).run 10000000 |>.1.toOption ==
  some [(1,ac,1),(2,ac,1),(2,c,1),(2,c,1)]
#guard (actual transitiveA "transitive" true false).run 10000000 |>.1.toOption ==
  some [(1,ac,0),(2,ac,0),(2,c,0),(2,c,0)]
#guard (match (actual directA "direct" true true).run 10000000 with
  | (.error .equation,_) => true | _ => false)
#guard (match (actual transitiveA "transitive" true true).run 10000000 with
  | (.error .equation,_) => true | _ => false)

-- Actual unused-source coverage is still required by the final graph. A
-- previously audited row cannot gain relevance from catalogue validation.
#guard (match (actual directA "direct" false true true).run 10000000 with
  | (.error .invalid,_) => true | _ => false)
#guard (match (actual directA "direct" false true false true).run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderBareBody
