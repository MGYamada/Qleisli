import QleisliKernel.Qirf.SourceDutyProviderHeader

/-! Artifact/header preparation for two original provider occurrences. No
root, finite equation, body-context or accepted handle is checked here. The
extra original module is audited but earns no selected source-row relevance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderHeader
open QleisliKernel Finite SourceTypes

private def text := "#![no_implicit_prelude]\n" ++
  "pub enum Tag{A,B}\n" ++
  "unitary fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "unitary fn route(s:Q<Tag>,q:Q<Bit>)->(Q<Tag>,Q<Bit>){" ++
  "qmatch(s,q){Tag::A=>leaf,Tag::B=>leaf}}\n"

private def spare := "#![no_implicit_prelude]\nunitary fn unused(q:Q<Bit>)->Q<Bit>{q}\n"

private def program : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],[.pure (.gate .z 0 1)],[1],[],.unitary⟩

private def artifact (name : String := "main::leaf") (sourceIndices : List Nat := [0])
    (implementation : Nat := 0) : Qirf.Artifact :=
  ⟨#[program],#[⟨[.bit],implementation,.circuit 0,name,"main::leaf",sourceIndices⟩],
    #[("main",text),("spare",spare)],0,none⟩

private def item (artifact : Qirf.Artifact) {catalogue}
    (queue : GenericDutyQueue.Checked catalogue)
    (request : Qirf.RuntimeProviderHeader.Request) (original : GenericDutyQueue.Item catalogue) :
    Qirf.SourceDutySlots.ItemExpectation queue original → WorkM (List (List Nat × Bool × Nat)) :=
  match original with
  | .demand _ _ => fun plan => plan.providers.mapM fun provider => do
    let prepared ← Qirf.SourceDutyProviderFresh.read provider.2
    let bound ← Qirf.SourceDutyProviderHeader.read artifact prepared request
    return (bound.roots,
      bound.rows.all (fun row => row.1 == "main") && !bound.rows.isEmpty &&
        bound.binding.header.original.body.checked.events.length == 1,
      bound.binding.header.subject.programIndex)
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def prepare (artifact : Qirf.Artifact) (subject : Qirf.SourceProviderSubject.Subject) :
    WorkM (List (List Nat × Bool × Nat)) := do
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  let request : Qirf.RuntimeProviderHeader.Request := (subject,.mk [] [] [] [] [])
  let rows ← plan.entries.mapM fun entry => item artifact queue request entry.subject entry.subjectExpectation
  return rows.flatten

-- The same concrete pure program index is retained separately for both
-- original arm occurrences. Header binding does not deduplicate body slots.
#guard (prepare artifact (.pure 0)).run 10000000 |>.1.toOption ==
  some [([0],true,0),([0],true,0)]

-- Function binding also retains its actual evidence-graph node, with the
-- same source Body and exact source row. The spare module stays irrelevant.
#guard (prepare artifact (.function 0)).run 10000000 |>.1.toOption ==
  some [([0,1],true,0),([0,1],true,0)]

#guard (match (prepare artifact (.pure 7)).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- Equal ports and a present program cannot repair a different function name.
#guard (match (prepare (artifact "main::other") (.function 0)).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- A valid unused source row cannot stand for the provider's original row.
#guard (match (prepare (artifact "main::leaf" [1]) (.function 0)).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- Discovery retains a literal forward program, not just an evidence index
-- whose implementation happens to be absent from the same artifact.
#guard (match (prepare (artifact "main::leaf" [0] 7) (.function 0)).run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderHeader
