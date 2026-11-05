import QleisliKernel.Qirf.SourceDutyProviderBody

/-! Closed Basis/Nat provider controls from the frozen original first sources.
All actual source queue entries are traversed in order. Only their concrete
provider contributions enter this bounded final graph; this is not complete
Meaning/reference/host/group/selected-root coverage or a wire slot count.
A forward provider under power zero or an unused Op formal still retains its
own actual body and full demanded access. Neither empty execution nor equal
physical width/matrix identifies the source instance or supplies a path.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderApplied
open QleisliKernel Finite SourceTypes Qirf

private def sourceA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn stamp[const A: Basis, const n: Nat](q: Q<A>) -> Q<A> {\n    global_phase_eighth(q)\n}\npub unitary fn route[const unused: Nat](s: Q<Tag>, q: Q<Unit>) -> (Q<Tag>, Q<Unit>) {\n    b::choose[stamp[type(Unit), 7]](s, q)\n}\nfn main() -> Unit { () }\n"
private def sourceB : String := "#![no_implicit_prelude]\npub unitary fn choose[const U: Op<Unit>](s: Q<a::Tag>, q: Q<Unit>) -> (Q<a::Tag>, Q<Unit>)\n    requires Applicable(U), Controllable(U) {\n    qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }\n}\n"

private def zeroB := sourceB.replace "a::Tag::A => U, a::Tag::B => U"
  "a::Tag::A => power(U, 0), a::Tag::B => power(U, 0)"
private def unusedB := sourceB.replace "qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }" "(s, q)"
private def otherA := sourceA.replace "type(Unit), 7" "type(Unit), 8"
private def wrongBasis := sourceA.replace "type(Unit), 7" "type(Bits<0>), 7"

private def program (omitted : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[],0⟩],[],if omitted then [] else [.pure (.applyUnitary 0 1 [⟨[],.monomial [] [0] [1]⟩])],
    [if omitted then 0 else 1],[],.unitary⟩

private def artifact (a b : String) (omitted : Bool) : Artifact :=
  ⟨#[program omitted],#[],#[("a",a),("b",b)],0,none⟩

private def item (artifact : Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (omitted wrongOffset : Bool)
    (entry : GenericDutyQueue.Item catalogue) :
    SourceDutySlots.ItemExpectation queue entry → WorkM (List (SourceDutyProviderBody.Contribution artifact)) :=
  match entry with
  | .demand _ _ => fun planned =>
    planned.providers.mapM fun provider => do
      let some token := provider.2.signature.original.occurrence.body.head? | throw .request
      guard (token.text == "global_phase_eighth") .request
      let context : RuntimeContextRequest.Context := .mk
        [⟨token.span.startByte+(if wrongOffset then 1 else 0),0,if omitted then 0 else 1⟩] [] [] [] []
      return (← SourceDutyProviderBody.prepareApplied artifact provider.2 (.pure 0,context)).contribution
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private abbrev Summary := Nat × OperationPaths.Paths × List (String × Nat) × Nat × Bool

private def describeProvider {artifact : Artifact}
    {catalogue : GenericCatalogue.Checked artifact.sources} {record : GenericDutyQueue.RecordIndex catalogue}
    {invocation : GenericDutyQueue.Invocation catalogue record} {demand : GenericDutyQueue.Demand invocation}
    {view : SourceDutySlots.View demand.transported.subject.description}
    {provider : SourceDutySlots.Provider demand view} {prepared : SourceDutyProviderFresh.Checked provider}
    {request : RuntimeProviderHeader.Request} {header : SourceDutyProviderHeader.Checked artifact prepared request}
    (root : Validity.Root)
    (source : @SourceDutyProviderBody.Discovered artifact catalogue record invocation demand view provider prepared request header)
    (checked : SourceDutyProviderBody.Checked source root) : Summary :=
  let core := header.binding.header.original.supplied.provider.signature
  let body := header.binding.header.original.body.checked
  let authentic := match source.eligibility with
    | .nongeneric _ => false
    | .applied origin _ =>
      origin.supplier.original.entry.body.name == "route" && origin.application.name == "stamp" &&
        !origin.supplier.original.entry.body.definition.original.header.formals.isEmpty &&
        origin.application.target.header.formals.length == 2
  (invocation.depth,view.requested,core.staticArguments.naturals,checked.body.result.actions.length,
    authentic && !core.original.declaration.isPublic &&
    decide (header.binding.header.original.supplied.context = .source "a") &&
    core.staticArguments.bases == [("A",[.unit])] && core.staticArguments.operations.isEmpty &&
    core.inputs == [[.unit]] && core.outputs == [[.unit]] &&
    decide (body.signature.parameters.map (·.tree) = [Semantics.RuntimeType.owner [.unit]]) &&
    decide (body.signature.result.tree = Semantics.RuntimeType.owner [.unit]) &&
    body.signature.arguments.naturals == core.staticArguments.naturals &&
    source.rows.any (fun row => row.1 == "a") && source.rows.any (fun row => row.1 == "b"))

private def describe {artifact : Artifact} (root : Validity.Root)
    (contribution : SourceDutyProviderBody.Contribution artifact) :
    SourceDutyProviderBody.Result root contribution → Summary :=
  match contribution with
  | .provider source => fun checked => describeProvider root source checked

private def actual (a b : String) (omitted : Bool := false) (wrongOffset : Bool := false) : WorkM (List Summary) := do
  let artifact := artifact a b omitted
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let contributions ← plan.entries.mapM fun entry =>
    item artifact queue omitted wrongOffset entry.subject entry.subjectExpectation
  let contributions := contributions.flatten
  guard (!contributions.isEmpty) .request
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact #[0]
    (contributions.flatMap SourceDutyProviderBody.Contribution.rows)
    ((artifact.root :: contributions.flatMap SourceDutyProviderBody.Contribution.roots).eraseDups))
  let final : SourceDutyProviderBody.Final artifact :=
    ⟨contributions,#[0],root.val,by with_reducible exact root.property⟩
  let checked ← SourceDutyProviderBody.read final
  return checked.entries.map fun entry =>
    describe final.root (final.contributions[entry.index.val]'entry.index.isLt) entry.result

private def ac : OperationPaths.Paths := ⟨true,false,true⟩
private def c : OperationPaths.Paths := ⟨false,false,true⟩

-- The actual n is retained through the generic caller and original private
-- supplier, including the two distinct original qmatch arm occurrences.
#guard (actual sourceA sourceB).run 10000000 |>.1.toOption ==
  some [(1,ac,[("n",7)],1,true),(1,c,[("n",7)],1,true),(1,c,[("n",7)],1,true)]

-- A zero repetition never erases the concrete forward leaf's source body or
-- original demand. This is provider-only consumption, not a whole-arm proof.
#guard (actual sourceA zeroB).run 10000000 |>.1.toOption ==
  some [(1,ac,[("n",7)],1,true),(1,c,[("n",7)],1,true),(1,c,[("n",7)],1,true)]

-- The unused actual keeps the original formal A/C premise and scalar phase.
#guard (actual sourceA unusedB).run 10000000 |>.1.toOption == some [(1,ac,[("n",7)],1,true)]

-- The same physical matrix with another unused Nat is a distinct actual
-- original instance. Its retained runtime Body receives 8 rather than 7.
#guard (actual otherA sourceB).run 10000000 |>.1.toOption ==
  some [(1,ac,[("n",8)],1,true),(1,c,[("n",8)],1,true),(1,c,[("n",8)],1,true)]

-- Actual source/body equality rejects the coordinated empty identity even
-- though the whole zero-power arm or unused runtime argument could be inert.
#guard (match (actual sourceA sourceB true).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual sourceA zeroB true).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual sourceA unusedB true).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual sourceA sourceB false true).run 10000000 with | (.error .request,_) => true | _ => false)

-- Equal zero physical widths cannot repair a different original Op<Unit>
-- argument type, even when the receiving body never applies its actual.
#guard (match (actual wrongBasis sourceB).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual wrongBasis unusedB).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderApplied
