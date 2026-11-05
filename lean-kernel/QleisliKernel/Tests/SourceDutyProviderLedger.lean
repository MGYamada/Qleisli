import QleisliKernel.Qirf.SourceDutyProviderLedger

/-! The native typed provider ledger traverses the exact complete original
plan, including open duties and canonical header references. The frozen a/b
sources and same-final-root Z/identity contrast remain unchanged. Contributions
are provider-only; retained Meaning/reference/host/group/recursive obligations
are not discharged by preparation or by a successful provider body.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderLedger
open QleisliKernel Finite SourceTypes Qirf

private def directA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn direct[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::choose[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def transitiveA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn transitive[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::forward[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def sourceB : String := "#![no_implicit_prelude]\npub unitary fn choose[const U: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(U), Controllable(U) {\n    qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }\n}\npub unitary fn forward[const V: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(V), Controllable(V) {\n    choose[V](s, q)\n}\n"

private def program (omittedPhase : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],if omittedPhase then [] else [.pure (.gate .z 0 1)],
    [if omittedPhase then 0 else 1],[],.unitary⟩

private def artifact (sourceA : String) (omittedPhase : Bool) : Artifact :=
  ⟨#[program omittedPhase],#[],#[("a",sourceA),("b",sourceB)],0,none⟩

private def itemRequests {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (omittedPhase wrongOffset : Bool) (item : GenericDutyQueue.Item catalogue) :
    (planned : SourceDutySlots.ItemExpectation queue item) → SourceDutyProviderLedger.ItemRequests queue item planned :=
  match item with
  | .demand _ _ => fun _ => fun _ provider _ =>
    let token := provider.2.signature.original.occurrence.body.head?
    let phase := token.map (·.text) == some "phase"
    let offset := (token.map (·.span.startByte)).getD 0
    let positions : List SourceSequence.Position := if phase then
        [⟨offset+(if wrongOffset then 1 else 0),0,if omittedPhase then 0 else 1⟩]
      else []
    (.pure 0,.mk positions [] [] [] [])
  | .header .. | .call .. => fun _ => ()
  | .pendingRecursion .. => fun impossible => nomatch impossible

private def requests {sources catalogue queue} (plan : @SourceDutySlots.Plan sources catalogue queue)
    (omittedPhase wrongOffset : Bool) : SourceDutyProviderLedger.Requests plan :=
  fun entry => itemRequests queue omittedPhase wrongOffset entry.subject entry.subjectExpectation

private def metadata {artifact catalogue queue item planned}
    (source : @SourceDutyProviderLedger.ItemPrepared artifact catalogue queue item planned) : Nat × Nat × Bool :=
  match source with
  | .demand _ _ original prepared =>
    (prepared.residual.conditional.length,0,prepared.residual.pending == original.pending)
  | .header .. => (0,1,true)
  | .call .. => (0,0,true)

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

private def actual (sourceA : String) (omittedPhase consumeBody : Bool) (wrongOffset : Bool := false) :
    WorkM (Nat × Bool × List (Nat × OperationPaths.Paths × Nat)) := do
  let artifact := artifact sourceA omittedPhase
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let ledger ← SourceDutyProviderLedger.read artifact plan (requests plan omittedPhase wrongOffset)
  let status := ledger.entries.map fun entry => metadata entry.prepared
  let ordered := ledger.entries.map (·.index.val) == List.range plan.entries.length &&
    ledger.entries.map (·.source.index.val) == List.range queue.items.length
  let retained := status.any (fun item => item.1 > 0) && status.any (fun item => item.2.1 > 0) &&
    status.all (·.2.2) && ordered
  let contributions := ledger.providerContributions
  let rows := contributions.flatMap SourceDutyProviderBody.Contribution.rows
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact #[0] rows
    ((artifact.root :: contributions.flatMap SourceDutyProviderBody.Contribution.roots).eraseDups))
  let final : SourceDutyProviderBody.Final artifact :=
    ⟨contributions,#[0],root.val,by with_reducible exact root.property⟩
  let results ← if consumeBody then do
      let checked ← SourceDutyProviderBody.read final
      pure (checked.entries.map fun entry =>
        describe final.root (final.contributions[entry.index.val]'entry.index.isLt) entry.result)
    else contributions.mapM (pathOnly final.root)
  return (ledger.entries.length,retained,results)

private def ac : OperationPaths.Paths := ⟨true,false,true⟩
private def c : OperationPaths.Paths := ⟨false,false,true⟩

-- Exact all-queue first indices (15/18), open original formal duties and
-- canonical header references remain present. No wanted-root filter is used.
#guard (actual directA false true).run 10000000 |>.1.toOption ==
  some (15,true,[(1,ac,1),(1,c,1),(1,c,1)])
#guard (actual transitiveA false true).run 10000000 |>.1.toOption ==
  some (18,true,[(1,ac,1),(2,ac,1),(2,c,1),(2,c,1)])

#guard (actual directA false false).run 10000000 |>.1.toOption ==
  some (15,true,[(1,ac,1),(1,c,1),(1,c,1)])
#guard (actual directA true false).run 10000000 |>.1.toOption ==
  some (15,true,[(1,ac,0),(1,c,0),(1,c,0)])
#guard (actual transitiveA false false).run 10000000 |>.1.toOption ==
  some (18,true,[(1,ac,1),(2,ac,1),(2,c,1),(2,c,1)])
#guard (actual transitiveA true false).run 10000000 |>.1.toOption ==
  some (18,true,[(1,ac,0),(2,ac,0),(2,c,0),(2,c,0)])
#guard (match (actual directA true true).run 10000000 with
  | (.error .equation,_) => true | _ => false)
#guard (match (actual transitiveA true true).run 10000000 with
  | (.error .equation,_) => true | _ => false)
#guard (match (actual directA false true true).run 10000000 with
  | (.error .request,_) => true | _ => false)

private def pendingMeaningResult {artifact catalogue queue item planned}
    (prepared : @SourceDutyProviderLedger.ItemPrepared artifact catalogue queue item planned) : Bool :=
  match prepared with
  | .demand _ _ _ source =>
    source.residual.pending.contains .meaningGraphBinding && source.residual.pending.contains .meaningEquation &&
      !source.residual.meaning.referenceIndices.isEmpty
  | _ => false

private def sourcePlan (source : String) : WorkM (Nat × Bool × Bool) := do
  let artifact : Artifact := ⟨#[program false],#[],#[("main",source)],0,none⟩
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let ledger ← SourceDutyProviderLedger.read artifact plan (requests plan false false)
  let pending := ledger.entries.any fun entry => pendingMeaningResult entry.prepared
  return (ledger.providerContributions.length,pending,ledger.entries.isEmpty)

private def pendingMeaning := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\nunitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn dormant[const unused:Nat](q:Q<Bit>)->Q<Bit>{checked_op(sign,Identity)(q)}\n"

-- Preparing the provider does not consume the original false Meaning or its
-- quantum reference; the original graph-binding/equation duties remain pending.
#guard (sourcePlan pendingMeaning).run 10000000 |>.1.toOption.map (fun result =>
  result.1 > 0 && result.2.1 && !result.2.2) == some true

private def withheld : WorkM Unit := do
  let catalogue ← GenericCatalogue.read #[("main",pendingMeaning)]
  let _ ← SourcePendingMeaning.read catalogue
  pure ()
#guard (match withheld.run 10000000 with | (.error .request,_) => true | _ => false)

-- Empty original roots are still audited and the actual ledger conversion
-- handles an empty entry range without constructing an accepted runtime root.
#guard (sourcePlan "#![no_implicit_prelude]\nunitary fn keep(q:Q<Unit>)->Q<Unit>{q}\n").run
  10000000 |>.1.toOption == some (0,false,true)

private def genericZero := "#![no_implicit_prelude]\npub enum Tag{A,B}\n" ++
  "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn route(s:Q<Tag>,q:Q<Bit>)->(Q<Tag>,Q<Bit>){" ++
  "qmatch(s,q){Tag::A=>power(leaf[0],0),Tag::B=>power(leaf[0],0)}}\n"

private def hasClosedProvider : WorkM Bool := do
  let catalogue ← GenericCatalogue.read #[("main",genericZero)]
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let hasProviders (item : GenericDutyQueue.Item catalogue) : SourceDutySlots.ItemExpectation queue item → Bool :=
    match item with
    | .demand _ _ => fun planned => !planned.providers.isEmpty
    | _ => fun _ => false
  return plan.entries.any fun entry => hasProviders entry.subject entry.subjectExpectation

private def bareOnlyItem (artifact : Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (item : GenericDutyQueue.Item catalogue) :
    SourceDutySlots.ItemExpectation queue item → WorkM Unit :=
  match item with
  | .demand _ _ => fun planned => do
    for provider in planned.providers do
      let _ ← SourceDutyProviderBody.prepareBare artifact provider.2 (.pure 0,.mk [] [] [] [] [])
    pure ()
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure ()

private def bareOnlyGenericZero : WorkM Unit := do
  let artifact : Artifact := ⟨#[program false],#[],#[("main",genericZero)],0,none⟩
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  for entry in plan.entries do
    bareOnlyItem artifact queue entry.subject entry.subjectExpectation

-- Zero power still keeps both actual children. The integrated source-only
-- ledger now prepares their authenticated Nat applications; body/IR/Meaning
-- equations are not inferred from this metadata result. The former explicit
-- Bare-only refusal remains a separately exercised historical subset.
#guard hasClosedProvider.run 10000000 |>.1.toOption == some true
#guard (sourcePlan genericZero).run 10000000 |>.1.toOption == some (2,false,false)
#guard (match bareOnlyGenericZero.run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderLedger
