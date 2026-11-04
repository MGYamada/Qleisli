import QleisliKernel.Qirf.RuntimeFormalActual
import QleisliKernel.Qirf.RuntimeClosedSubject
import QleisliKernel.SourceTypes.OperationSourceUses
import QleisliKernel.SourceTypes.GenericFormalPaths

/-! A written child path inside an operation argument selects one original
substitution step and one checked native occurrence. Repeated formal uses
retain separate argument tokens and child positions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeInteriorSupply
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Step UsedChild)
open RuntimeNativeSubject (Cursor Formal)
open RuntimeClosedSubject (Paired Children)
open RuntimeInterval (Computed)
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

structure Native {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (native : OperationDescription.Description) where
  index : Nat
  cursor : Cursor checked
  terminal : Cursor checked
  paired : Paired checked native index cursor terminal

private def pick {artifact catalogue context description graph implementations references prepared root requested checked native cursor}
    (record : Nat) :
    Nat → {indices : List (Nat × Nat)} →
    @Children artifact catalogue context description graph implementations references prepared root requested checked native cursor indices →
    Option (Nat × Native checked native) :=
  Nat.rec (fun {_} _ => none) (fun _ next {_} children => match children with
    | .nil => none
    | .cons (index := index) (position := position) child terminal paired rest =>
      if child.val.cursor.tree.2.located.position.val = record then
        some (position,⟨index,child.val.cursor,terminal,paired⟩)
      else next rest)

private def selectChild {artifact catalogue context description graph implementations references prepared root requested checked native
    index cursor terminal} (paired : @Paired artifact catalogue context description graph implementations references prepared
      root requested checked native index cursor terminal) (record : Nat) : WorkM (Nat × Native checked native) := do
  match paired with
  | .formal .. => throw .request
  | .node node _ _ _ _ _ children =>
    let count := node.children.length
    exactWork (Exact.charge (16*(count+1)))
    let some found := pick record (count+1) children | throw .request
    return found

private def nativeChild {artifact catalogue context description graph implementations references prepared root requested checked native}
    (current : @Native artifact catalogue context description graph implementations references prepared root requested checked native)
    (edge : SourceOperation.Edge) : WorkM (Nat × Native checked native) := do
  let selected ← RuntimeOperationOccurrenceTree.follow current.cursor.tree [edge]
  selectChild current.paired selected.2.located.position.val

private def originalPosition (edge : SourceOperation.Edge) (position : Nat) : Prop :=
  match edge with | .child n => position = n | .actual _ => True

private instance (edge : SourceOperation.Edge) (position : Nat) : Decidable (originalPosition edge position) := by
  cases edge <;> dsimp [originalPosition] <;> infer_instance

-- Symbolic Basis/Nat payloads may change under substitution. These are the
-- constructors whose original ordered Op child positions survive the change.
private def compatible : GenericOperation.Node → OperationDescription.Node → Bool
  | .inverse _, .inverse _ | .controlled _, .controlled _ | .power .., .power .. |
    .thenOp .., .thenOp .. | .tensor .., .tensor .. | .conjugate .., .conjugate .. => true
  | .requested _ a b, .requested _ c d => a == c && b == d
  | .provider a b _ _ ops _, .provider c d _ _ children =>
    a == c && b == d && ops.map Prod.fst == children.map Prod.fst
  | _,_ => false

structure Point {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (native : OperationDescription.Description) where
  index : Nat
  occurrence : Native checked native

structure EdgeAt {artifact catalogue context description graph implementations references prepared root requested checked native
    sources app original}
    (transfer : @GenericOperationSubstitute.Checked sources app original)
    (current : @Point artifact catalogue context description graph implementations references prepared root requested checked native)
    (edge : SourceOperation.Edge) where
  next : Point checked native
  position : Nat
  ordinal : originalPosition edge position
  followed : Computed (nativeChild current.occurrence edge) (position,next.occurrence)
  parent : Step app original
  parentAt : transfer.result.steps[current.index]? = some parent
  constructor : compatible parent.node current.occurrence.cursor.node = true
  edgeIndex : parent.node.children[position]? = some next.index
  row : Step app original
  used : UsedChild transfer parent next.index row

private theorem usedChild {sources app original transfer parent row prior} {i j : Nat}
    (atParent : (@GenericOperationSubstitute.Checked.result sources app original transfer).steps[i]? = some parent)
    (atChild : transfer.result.steps[j]? = some row) (found : parent.previous[j]? = some prior) :
    UsedChild transfer parent j row := by
  obtain ⟨child,used,_⟩ := transfer.child_at atParent found
  exact Option.some.inj (used.atIndex.symm.trans atChild) ▸ used

private def readEdge {artifact catalogue context description graph implementations references prepared root requested checked native
    sources app original}
    (transfer : @GenericOperationSubstitute.Checked sources app original)
    (current : @Point artifact catalogue context description graph implementations references prepared root requested checked native)
    (edge : SourceOperation.Edge) : WorkM (EdgeAt transfer current edge) := do
  let followed ← NaturalAffine.witness (nativeChild current.occurrence edge)
  let position := followed.val.1
  let occurrence := followed.val.2
  if ordinal : originalPosition edge position then
    return ← build position occurrence ordinal (by with_reducible exact followed.property)
  else throw .request
where
  build (position : Nat) (occurrence : Native checked native) (ordinal : originalPosition edge position)
      (followed : Computed (nativeChild current.occurrence edge) (position,occurrence)) :
      WorkM (EdgeAt transfer current edge) := do
    exactWork (Exact.charge (16*(transfer.result.steps.length+1)))
    match parentAt : transfer.result.steps[current.index]? with
    | none => throw .request
    | some parent =>
      exactWork (Exact.charge (16*(GenericOperation.Meter.node parent.node+
        RuntimeStructuredRoot.argumentFields {operations := [("",⟨[current.occurrence.cursor.node],0⟩)]}+
        parent.previous.length+transfer.result.steps.length+1)))
      if constructor : compatible parent.node current.occurrence.cursor.node = true then
        match edgeIndex : parent.node.children[position]? with
        | none => throw .request
        | some index =>
          match atChild : transfer.result.steps[index]?, found : parent.previous[index]? with
          | some row,some _ =>
            return ⟨⟨index,occurrence⟩,position,ordinal,followed,
              parent,parentAt,constructor,edgeIndex,row,usedChild parentAt atChild found⟩
          | _,_ => throw .request
      else throw .request

inductive Path {artifact catalogue context description graph implementations references prepared root requested checked native
    sources app original}
    (transfer : @GenericOperationSubstitute.Checked sources app original) :
    @Point artifact catalogue context description graph implementations references prepared root requested checked native →
    List SourceOperation.Edge → Point checked native → Type where
  | nil (point : Point checked native) : Path transfer point [] point
  | cons {start edge rest finish} (step : EdgeAt transfer start edge)
      (tail : Path transfer step.next rest finish) : Path transfer start (edge :: rest) finish

private def follow {artifact catalogue context description graph implementations references prepared root requested checked native
    sources app original}
    (transfer : @GenericOperationSubstitute.Checked sources app original) :
    Nat → (start : @Point artifact catalogue context description graph implementations references prepared root requested checked native) →
    (path : List SourceOperation.Edge) → WorkM (Σ finish, Path transfer start path finish) :=
  Nat.rec
    (fun start path => match path with | [] => pure ⟨start,.nil start⟩ | _ :: _ => throw .limit)
    (fun _ next start path => match path with
      | [] => pure ⟨start,.nil start⟩
      | edge :: rest => do
        let step ← readEdge transfer start edge
        let tail ← next step.next rest
        return ⟨tail.1,.cons step tail.2⟩)

private def formalAt {artifact catalogue context description graph implementations references prepared root requested checked native
    index cursor terminal} (paired : @Paired artifact catalogue context description graph implementations references prepared
      root requested checked native index cursor terminal) :
    Option {selected : Formal cursor // Computed (RuntimeNativeSubject.readFormal cursor) selected} :=
  match paired with
  | .node .. => none
  | .formal selected read _ => some ⟨selected,read⟩

structure Leaf {artifact catalogue context description graph implementations references prepared root requested checked native
    caller original}
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app original)
    (start : @Point artifact catalogue context description graph implementations references prepared root requested checked native)
    (path : List SourceOperation.Edge) (key : Parameter) where
  finish : Point checked native
  route : Path transfer start path finish
  followed : Computed (follow transfer (path.length+1) start path) ⟨finish,route⟩
  selected : {value : Formal finish.occurrence.cursor // Computed (RuntimeNativeSubject.readFormal finish.occurrence.cursor) value}
  wrapper : formalAt finish.occurrence.paired = some selected
  choice : RuntimeFormalActual.Choice
  choiceRead : Computed (RuntimeFormalActual.readChoice selected.val) choice
  supply : RuntimeFormalActual.SupplyAt event app transfer finish.index key choice
  supplied : Computed (RuntimeFormalActual.readSupplyAt event app transfer finish.index key choice) supply

def readLeaf {artifact catalogue context description graph implementations references prepared root requested checked native
    caller original}
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app original)
    (start : @Point artifact catalogue context description graph implementations references prepared root requested checked native)
    (path : List SourceOperation.Edge) (key : Parameter) : WorkM (Leaf event app transfer start path key) := do
  exactWork (Exact.charge (16*(path.length+1)))
  let found ← NaturalAffine.witness (follow transfer (path.length+1) start path)
  let point := found.val.1
  match wrapper : formalAt point.occurrence.paired with
  | none => throw .request
  | some selected =>
    let choice ← NaturalAffine.witness (RuntimeFormalActual.readChoice selected.val)
    let supply ← NaturalAffine.witness (RuntimeFormalActual.readSupplyAt event app transfer point.index key choice.val)
    return ⟨point,found.val.2,by with_reducible exact found.property,selected,wrapper,choice.val,
      by with_reducible exact choice.property,supply.val,by with_reducible exact supply.property⟩

def Path.positions {artifact catalogue context description graph implementations references prepared root requested checked native
    sources app original transfer start edges finish}
    (route : @Path artifact catalogue context description graph implementations references prepared root requested checked native
      sources app original transfer start edges finish) : List Nat :=
  (Nat.rec (motive := fun fuel => {start finish : Point checked native} → {edges : List SourceOperation.Edge} →
      Path transfer start edges finish → edges.length ≤ fuel → List Nat)
    (fun {_ _ _} path => by
      cases path with
      | nil => exact fun _ => []
      | cons => exact fun bound => False.elim (Nat.not_succ_le_zero _ bound))
    (fun _ next {_ _ _} path => by
      cases path with
      | nil => exact fun _ => []
      | cons step tail => exact fun bound => step.position :: next tail (Nat.le_of_succ_le_succ bound))
    edges.length) route (Nat.le_refl _)

private def initial {artifact catalogue context description graph implementations references prepared root requested checked native
    index cursor terminal}
    (originalIndex : Nat) (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) : Point checked native := ⟨originalIndex,⟨index,cursor,terminal,paired⟩⟩

structure Entry {artifact catalogue context description graph implementations references prepared root requested checked native caller
    original sourceOwner sourceName originalHeader entries environment scope genericState tokens}
    {inst : @StaticInstantiation.Checked artifact.sources sourceOwner sourceName originalHeader}
    (uses : List (OperationSourceUses.Use inst entries environment scope genericState tokens))
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app original)
    (start : @Point artifact catalogue context description graph implementations references prepared root requested checked native) where
  index : Fin uses.length
  use : OperationSourceUses.Use inst entries environment scope genericState tokens
  originalUse : uses[index.val]? = some use
  leaf : Leaf event app transfer start use.path use.formal.key
  read : Computed (readLeaf event app transfer start use.path use.formal.key) leaf
  sameHeader : use.formal.headerFormal = leaf.choice.header

def Entry.signature {artifact catalogue context description graph implementations references prepared root requested checked native caller
    original sourceOwner sourceName originalHeader entries environment scope genericState tokens}
    {inst : @StaticInstantiation.Checked artifact.sources sourceOwner sourceName originalHeader}
    {uses : List (OperationSourceUses.Use inst entries environment scope genericState tokens)}
    {event : SourceRuntimeContext.NamedEvent artifact.sources caller} {app : GenericOperation.ApplicationSource artifact.sources}
    {transfer : GenericOperationSubstitute.Checked app original}
    {start : @Point artifact catalogue context description graph implementations references prepared root requested checked native}
    (entry : Entry uses event app transfer start) : List Nat × Nat × Parameter :=
  (entry.leaf.route.positions,entry.leaf.finish.index,entry.use.formal.key)

private def occurrenceFields (occurrences : List GenericFormalPaths.Occurrence) : Nat :=
  occurrences.foldl (fun total (path,_,key) =>
    total + path.length + key.moduleName.utf8ByteSize + key.declarationName.utf8ByteSize + 1) 0

def checkCoverage (observed expected : List GenericFormalPaths.Occurrence) : WorkM (PLift (observed = expected)) := do
  exactWork (Exact.charge (16*(occurrenceFields observed+occurrenceFields expected+1)))
  if same : observed = expected then return ⟨same⟩ else throw .request

structure Checked {artifact catalogue context description graph implementations references prepared root requested checked native
    index cursor terminal caller innerCaller innerOriginal innerEvent innerApp innerTransfer innerKey innerChoice}
    (incoming : @RuntimeFormalActual.Supply artifact.sources innerCaller innerOriginal innerEvent innerApp innerTransfer innerKey innerChoice)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app innerTransfer.result.subject)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) where
  source : OperationSourceUses.Checked innerEvent.target.callerSignature.instantiation innerEvent.target.naturals.helpers.val
    innerEvent.target.naturals.environment innerEvent.scope incoming.source.checked.genericState incoming.source.actual.argument.tokens
  sourceRead : Computed (OperationSourceUses.readChecked incoming.source.checked) source
  entries : List (Entry source.uses event app transfer (initial innerTransfer.result.subject.description.root paired))
  ordered : entries.map (·.index) = List.finRange source.uses.length
  expected : List (List Nat × Nat × Parameter)
  enumerated : Computed (GenericFormalPaths.read incoming.genericActual.subject) expected
  coverage : entries.map Entry.signature = expected
  compared : Computed (checkCoverage (entries.map Entry.signature) expected) ⟨coverage⟩

/-- Every use comes from the checked source argument, including separate uses
of the same formal in one constructor. Every step compares the original header
with the header whose Op argument the native occurrence actually selected. -/
def read {artifact catalogue context description graph implementations references prepared root requested checked native
    index cursor terminal caller innerCaller innerOriginal innerEvent innerApp innerTransfer innerKey innerChoice}
    (incoming : @RuntimeFormalActual.Supply artifact.sources innerCaller innerOriginal innerEvent innerApp innerTransfer innerKey innerChoice)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app innerTransfer.result.subject)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) : WorkM (Checked incoming event app transfer paired) := do
  let sourced ← NaturalAffine.witness (OperationSourceUses.readChecked incoming.source.checked)
  let uses := sourced.val.uses
  exactWork (Exact.charge (16*(uses.length+1)))
  let values := uses.toArray
  let start := initial innerTransfer.result.subject.description.root paired
  let entries ← (List.finRange uses.length).mapM fun (index : Fin uses.length) => do
    let use := values[index.val]'(by simpa only [values,List.size_toArray] using index.isLt)
    have originalUse : uses[index.val]? = some use := by
      simpa only [use,values,List.getElem_toArray] using List.getElem?_eq_getElem index.isLt
    let leaf ← NaturalAffine.witness (readLeaf event app transfer start use.path use.formal.key)
    exactWork (Exact.charge (16*(SourceTrace.Meter.tokenFields innerEvent.target.callerSignature.original.occurrence.header+
      SourceTrace.Meter.tokenFields app.target.envelope.occurrence.header+1)))
    if same : use.formal.headerFormal = leaf.val.choice.header then
      return (⟨index,use,originalUse,leaf.val,by with_reducible exact leaf.property,same⟩ :
        Entry uses event app transfer start)
    else throw .request
  if ordered : entries.map (·.index) = List.finRange uses.length then
    let expected ← NaturalAffine.witness (GenericFormalPaths.read incoming.genericActual.subject)
    exactWork (Exact.charge (8*(entries.foldl (fun total e => total+e.use.path.length+1) 1)))
    let compared ← NaturalAffine.witness (checkCoverage (entries.map Entry.signature) expected.val)
    return ⟨sourced.val,by with_reducible exact sourced.property,entries,ordered,expected.val,
      by with_reducible exact expected.property,compared.val.down,by with_reducible exact compared.property⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeInteriorSupply
