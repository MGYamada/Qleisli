import QleisliKernel.Qirf.RuntimeClosedProviderSite

/-! Coverage is indexed by the entire ordered closed child tree. An open
provider or nested written Meaning leaves its own residual at its original
position. Native formal forwarding preserves the selected occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeClosedProvider
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Subject)
open QleisliKernel.SourceTypes.OperationDescription (Node)
open RuntimeClosedSubject (Paired ChildRead)
open RuntimeNativeSubject (Cursor Formal)
open RuntimeInterval (Computed)
abbrev Need := Option OperationPaths.Paths

private def noLocal : GenericOperation.Node → Bool
  | .provider .. | .requested .. | .formal _ => false
  | _ => true

inductive Local {artifact catalogue context description graph implementations references prepared root requested checked}
    (subject : Subject artifact.sources) (index : Nat)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (need : Need) : GenericOperation.Node → Bool → Type where
  | structural (node : GenericOperation.Node) (supported : noLocal node = true) : Local subject index cursor need node true
  | pending (node : GenericOperation.Node) (reason : Pending) : Local subject index cursor need node false
  | unidentified (node : GenericOperation.Node) (slot : Native cursor) (site : Option (Site subject index))
      (reason : Pending) : Local subject index cursor need node false
  | partialSite (node : GenericOperation.Node) (owner name : String) (slot : Native cursor) (site : Site subject index)
      (identity : Identity site slot owner name) (reason : Pending) : Local subject index cursor need node false
  | bare {owner name : String} (slot : Native cursor) (site : Site subject index) (required : OperationPaths.Paths)
      (path : need = some required) (binding : Bare site slot owner name required) :
      Local subject index cursor need (.provider owner name [] [] [] []) true

private def readLocal {artifact catalogue context description graph implementations references prepared root requested checked}
    (subject : Subject artifact.sources) (index : Nat)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (need : Need) (node : GenericOperation.Node) (original : subject.description.nodes[index]? = some node) :
    WorkM (Σ ok,Local subject index cursor need node ok) := do
  if simple : noLocal node = true then return ⟨true,.structural node simple⟩
  else match node with
  | .provider owner name _ _ _ _ =>
    let slot ← nativeAt cursor
    match ← readSite catalogue subject index with
    | .error reason => return ⟨false,.unidentified _ slot none reason⟩
    | .ok site =>
      match ← readIdentity site slot owner name with
      | .error reason => return ⟨false,.unidentified _ slot (some site) reason⟩
      | .ok identity =>
        match need with
        | none => return ⟨false,.partialSite _ owner name slot site identity.down .paths⟩
        | some required =>
          match ← readBare site slot owner name required identity.down with
          | .error reason => return ⟨false,.partialSite _ owner name slot site identity.down reason⟩
          | .ok binding =>
            have same := Option.some.inj (original.symm.trans binding.originalNode)
            return ⟨true,same.symm ▸ Local.bare slot site required rfl binding⟩
  | .requested .. => return ⟨false,.pending _ .meaning⟩
  | _ => return ⟨false,.pending _ .arguments⟩

/-- Unknown original Op-argument prerequisites still visit every child; their
path demand remains unknown and a descendant provider cannot be promoted. -/
private def childNeeds (node : GenericOperation.Node) (need : Need) : WorkM (List (Nat × Need)) := do
  exactWork (Exact.charge (16*(GenericOperation.Meter.node node+1)*(node.children.length+1)))
  let unknown := fun _ : Unit => node.children.map fun index => (index,none)
  let some paths := need | return unknown ()
  let known := match node with
    | .provider _ _ _ _ operations premises => operations.all fun op => premises.any (·.1 == op.1)
    | _ => true
  if known then
    let shape ← node.pathShape
    return (shape.children paths).map fun (index,required) => (index,some required)
  else return unknown ()

mutual
inductive Tree {artifact catalogue context description graph implementations references prepared root requested}
    (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :
    Nat → Cursor checked → Cursor checked → Need → Bool → Type where
  | node {index : Nat} {cursor : Cursor checked} {need : Need} {here nested : Bool} (payload : Node)
      (selected : closed.data.description.nodes[index]? = some payload)
      (same : RuntimeClosedSubject.shape cursor.node = RuntimeClosedSubject.shape payload)
      (source : GenericOperation.Node) (original : subject.description.nodes[index]? = some source)
      (edges : payload.children = source.children) (localResult : Local subject index cursor need source here)
      (needs : List (Nat × Need)) (planned : Computed (childNeeds source need) needs)
      (children : Forest subject closed checked cursor payload.children.zipIdx needs nested) :
      Tree subject closed checked index cursor cursor need (here && nested)
  | formal {index : Nat} {cursor terminal : Cursor checked} {need : Need} {ok : Bool} (chosen : Formal cursor)
      (selected : Computed (RuntimeNativeSubject.readFormal cursor) chosen)
      (tail : Tree subject closed checked index chosen.child.cursor terminal need ok) :
      Tree subject closed checked index cursor terminal need ok

inductive Forest {artifact catalogue context description graph implementations references prepared root requested}
    (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :
    Cursor checked → List (Nat × Nat) → List (Nat × Need) → Bool → Type where
  | nil {cursor : Cursor checked} : Forest subject closed checked cursor [] [] true
  | cons {cursor terminal : Cursor checked} {index position plannedIndex : Nat} {need : Need} {indices needs} {first rest : Bool}
      (child : ChildRead cursor position) (original : plannedIndex = index)
      (tree : Tree subject closed checked index child.val.cursor terminal need first)
      (tail : Forest subject closed checked cursor indices needs rest) :
      Forest subject closed checked cursor ((index,position)::indices) ((plannedIndex,need)::needs) (first && rest)
end

private abbrev Visit {artifact catalogue context description graph implementations references prepared root requested}
    (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :=
  {index : Nat} → {cursor terminal : Cursor checked} → Paired checked closed.data.description index cursor terminal →
    (need : Need) → WorkM (Σ ok,Tree subject closed checked index cursor terminal need ok)

private def children {artifact catalogue context description graph implementations references prepared root requested checked}
    (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (next : Visit subject closed checked) :
    Nat → {indices : List (Nat × Nat)} → RuntimeClosedSubject.Children checked closed.data.description cursor indices →
      (needs : List (Nat × Need)) → WorkM (Σ ok,Forest subject closed checked cursor indices needs ok) :=
  Nat.rec (fun {_} items needs => match items,needs with | .nil,[] => pure ⟨true,.nil⟩ | _,_ => throw .limit)
    (fun _ later {_} items needs => match items,needs with
      | .nil,[] => pure ⟨true,.nil⟩
      | .cons (index := index) child _ paired rest,(j,need)::tail => do
        exactWork (Exact.charge 8)
        if same : j = index then
          let first ← next paired need
          let more ← later rest tail
          return ⟨first.1 && more.1,.cons child same first.2 more.2⟩
        else throw .request
      | _,_ => throw .request)

private def visit {artifact catalogue context description graph implementations references prepared root requested}
    (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :
    Nat → Visit subject closed checked :=
  Nat.rec (motive := fun _ => Visit subject closed checked)
    (fun {_ _ _} _ _ => throw .limit)
    (fun _ next {index cursor _} paired need => match paired with
      | .formal chosen selected child => do
        exactWork (Exact.charge 8)
        let tail ← next child need
        return ⟨tail.1,.formal chosen selected tail.2⟩
      | .node payload selected _ same _ _ items => do
        exactWork (Exact.charge (16*(subject.description.nodes.length+payload.children.length+1)))
        match original : subject.description.nodes[index]? with
        | none => throw .request
        | some source =>
          have edges : payload.children = source.children := by
            obtain ⟨node,_,found,_,_,_,edges⟩ := closed.originalNodeAt _ selected
            exact Option.some.inj (found.symm.trans original) ▸ edges
          let here ← readLocal subject index cursor need source original
          let needs ← NaturalAffine.witness (childNeeds source need)
          let nested ← children subject closed cursor next (payload.children.length+1) items needs.val
          return ⟨here.1 && nested.1,.node payload selected same source original edges here.2 needs.val
            (by with_reducible exact needs.property) nested.2⟩)

structure Checked {artifact catalogue context description graph implementations references prepared root requested checked
    index cursor terminal} (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested checked
      closed.data.description index cursor terminal) (required : OperationPaths.Paths) where
  complete : Bool
  tree : Tree subject closed checked index cursor terminal (some required) complete
  traversed : Computed (visit subject closed checked (prepared.occurrences.length+1) paired (some required)) ⟨complete,tree⟩

def Checked.AllBound {artifact catalogue context description graph implementations references prepared root requested checked
    index cursor terminal subject closed paired required}
    (report : @Checked artifact catalogue context description graph implementations references prepared root requested checked
      index cursor terminal subject closed paired required) : Prop := report.complete = true

def read {artifact catalogue context description graph implementations references prepared root requested checked
    index cursor terminal} (subject : Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested checked
      closed.data.description index cursor terminal) (required : OperationPaths.Paths := ⟨false,false,false⟩) :
    WorkM (Checked subject closed paired required) := do
  exactWork (Exact.charge (16*(prepared.occurrences.length+1)))
  let result ← NaturalAffine.witness (visit subject closed checked (prepared.occurrences.length+1) paired (some required))
  return ⟨result.val.1,result.val.2,by with_reducible exact result.property⟩

end QleisliKernel.Qirf.RuntimeClosedProvider
