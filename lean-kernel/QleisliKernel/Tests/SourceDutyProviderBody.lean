import QleisliKernel.Qirf.SourceDutyProviderBody

/-! The frozen original H→Z provider body is consumed for both written arm
occurrences under one actual final graph. These controls introduce no handle,
wire route or claim about the remaining Meaning/full-runtime obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderBody
open QleisliKernel Finite SourceTypes Qirf

-- Exact desired source from the preserved first observer.
private def source : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn leaf(q: Q<Bit>) -> Q<Bit> { phase[1,1](h(q)) }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::A => leaf, Tag::B => leaf }\n}\nfn main() -> Unit { () }\n"

private def program (fault : Nat) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],
    if fault == 1 then [.pure (.gate .h 0 1)]
    else if fault == 2 then [.pure (.gate .z 0 1),.pure (.gate .h 1 2)]
    else [.pure (.gate .h 0 1),.pure (.gate .z 1 2)],
    [if fault == 1 then 1 else 2],[],.unitary⟩

private def contributions (artifact : Qirf.Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (fault : Nat) (item : GenericDutyQueue.Item catalogue) :
    SourceDutySlots.ItemExpectation queue item → WorkM (List (SourceDutyProviderBody.Contribution artifact)) :=
  match item with
  | .demand _ _ => fun planned => planned.providers.mapM fun provider => do
    let prepared ← SourceDutyProviderFresh.read provider.2
    let [first,last] := prepared.original.body.checked.events | throw .request
    let positions : List SourceSequence.Position :=
      [⟨first.offset,0,1⟩,⟨last.offset,1,if fault == 1 then 0 else 1⟩]
    let positions := if fault == 3 then positions.reverse else positions
    let request : RuntimeProviderHeader.Request := (.pure 0,.mk positions [] [] [] [])
    let header ← SourceDutyProviderHeader.read artifact prepared request
    let discovered ← SourceDutyProviderBody.discover header
    return .provider discovered
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def count {artifact} (root : Validity.Root) (contribution : SourceDutyProviderBody.Contribution artifact) :
    SourceDutyProviderBody.Result root contribution → Nat × Bool :=
  match contribution with
  | .provider (view := view) _ => fun checked =>
    (checked.body.result.actions.length,view.requested == (⟨false,false,true⟩ : OperationPaths.Paths))

private def actual (fault : Nat) : WorkM (List (Nat × Bool)) := do
  let artifact : Qirf.Artifact := ⟨#[program fault],#[],#[("main",source)],0,none⟩
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← SourceDutySlots.read queue
  let prepared ← plan.entries.mapM fun entry => contributions artifact queue fault entry.subject entry.subjectExpectation
  let prepared := prepared.flatten
  guard (prepared.length == 2) .request
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact #[0]
    (prepared.flatMap SourceDutyProviderBody.Contribution.rows)
    ((artifact.root :: prepared.flatMap SourceDutyProviderBody.Contribution.roots).eraseDups))
  let final : SourceDutyProviderBody.Final artifact :=
    ⟨prepared,#[0],root.val,by with_reducible exact root.property⟩
  let checked ← SourceDutyProviderBody.read final
  return checked.entries.map fun entry =>
    count final.root (final.contributions[entry.index.val]'entry.index.isLt) entry.result

-- Both actual source occurrences consume H then the original nonzero phase;
-- their original control demand is retained, not reduced to forward access.
#guard (actual 0).run 10000000 |>.1.toOption == some [(2,true),(2,true)]

-- Each mutant is structurally unitary IR. The omitted or reordered phase
-- nevertheless fails the actual original body equation on the same graph.
#guard (match (actual 1).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual 2).run 10000000 with | (.error .equation,_) => true | _ => false)

-- Original event order is retained even when nested source-call byte offsets
-- are not sorted. A reordered context is rejected before the final graph.
#guard (match (actual 3).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderBody
