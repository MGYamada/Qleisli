import QleisliKernel.Qirf.RuntimeOperationTree
import QleisliKernel.Qirf.RuntimeOperationOccurrenceTree
import QleisliKernel.Qirf.RuntimeGraphOperation
import QleisliKernel.SourceTypes.QuantumArms

/-! Associate original written assertions with the same checked native records.
Source paths select complete prepared occurrences, including repeated edges.
Exact list-position transport uses the actual native traversal theorem; no
whole-record equality decision, matrix cache or first equal-index lookup is used.
The native Meaning equation is retained, never recalculated by a new checker.
Complete GenericDutyQueue invocation/DutyAt/substitution association and body
preservation remain separate mandatory obligations. No source handle is issued.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSourceOperationMarkers
open QleisliKernel Finite SourceTypes

/-- Select one record from this exact successful traversal. Equality includes
the full graph, provider, original Meaning requests and all dependent receipts. -/
structure RecordAt {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (located : @RuntimeOperationOccurrenceTree.Located artifact catalogue context description graph implementations references prepared) where
  index : Fin checked.outcome.records.length
  record : @RuntimeOperationTree.Record artifact catalogue context description graph prepared.order root
  selected : checked.outcome.records[index.val]'index.isLt = record
  occurrence : record.occurrence = located.occurrence

theorem RecordAt.node {artifact catalogue context description graph implementations references prepared root requested checked located}
    (binding : @RecordAt artifact catalogue context description graph implementations references prepared root requested checked located) :
    binding.record.checked.node = located.node := by
  have original := binding.record.checked.selected
  have sameIndex : binding.record.occurrence.index = located.occurrence.index :=
    congrArg (fun occurrence => occurrence.index) binding.occurrence
  rw [sameIndex] at original
  exact Option.some.inj (original.symm.trans located.original)

def readRecordAt {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (located : @RuntimeOperationOccurrenceTree.Located artifact catalogue context description graph implementations references prepared) :
    WorkM (RecordAt checked located) := do
  exactWork (Exact.charge (16*(checked.outcome.records.length+prepared.occurrences.length+1)))
  have lengthSame : checked.outcome.records.length = prepared.occurrences.length := by
    have same := congrArg List.length checked.occurrences
    simpa only [List.length_map] using same
  let index : Fin checked.outcome.records.length :=
    ⟨located.position.val,by rw [lengthSame]; exact located.position.isLt⟩
  let record := checked.outcome.records[index.val]'index.isLt
  have sameOccurrence : record.occurrence = located.occurrence := by
    have same : (checked.outcome.records.map (·.occurrence))[located.position.val]? =
        prepared.occurrences[located.position.val]? :=
      congrArg (fun values => values[located.position.val]?) checked.occurrences
    rw [List.getElem?_map,List.getElem?_eq_getElem index.isLt,
      List.getElem?_eq_getElem located.position.isLt,Option.map_some] at same
    exact (Option.some.inj same).trans located.atPosition
  return ⟨index,record,rfl,sameOccurrence⟩

/-- The original resolver query and the native request retain different route
records. Bind their actual declaration/source, rather than equating queryRows
or trusting only a canonical name or a matrix. -/
structure MeaningOriginal {sources caller scope}
    (marker : SourceOperation.Marker sources caller scope) (request : SourceMeaning.Request sources) where
  caller : request.caller = some caller
  owner : request.moduleName = marker.selected.resolution.moduleName
  name : request.declarationName = marker.selected.resolution.declaration.name
  root : SourceMeaning.Node sources
  selected : request.meaning.graph.nodes[request.meaning.graph.root]? = some root
  original : root.owner = marker.selected.resolution.moduleName ∧
    root.name = marker.selected.resolution.declaration.name ∧
    root.original.source = marker.selected.resolution.source ∧
    root.original.declaration = marker.selected.resolution.declaration

def readMeaningOriginal {sources caller scope}
    (marker : SourceOperation.Marker sources caller scope) (request : SourceMeaning.Request sources) :
    WorkM (MeaningOriginal marker request) := do
  -- Existing source/Meaning readers pay for their original work. These are
  -- additional immutable key/source comparisons and an actual root lookup.
  let bytes := caller.utf8ByteSize+request.moduleName.utf8ByteSize+request.declarationName.utf8ByteSize+
    marker.selected.resolution.moduleName.utf8ByteSize+marker.selected.resolution.declaration.name.utf8ByteSize+
    marker.selected.resolution.source.utf8ByteSize+1
  exactWork (Exact.charge (16*(bytes+request.meaning.graph.nodes.length+1)))
  if sameCaller : request.caller = some caller then
    if sameOwner : request.moduleName = marker.selected.resolution.moduleName then
      if sameName : request.declarationName = marker.selected.resolution.declaration.name then
        match selected : request.meaning.graph.nodes[request.meaning.graph.root]? with
        | none => throw .request
        | some root =>
          exactWork (Exact.charge (16*(root.original.source.utf8ByteSize+root.owner.utf8ByteSize+root.name.utf8ByteSize+1)))
          if original : root.owner = marker.selected.resolution.moduleName ∧
              root.name = marker.selected.resolution.declaration.name ∧
              root.original.source = marker.selected.resolution.source ∧
              root.original.declaration = marker.selected.resolution.declaration then
            return ⟨sameCaller,sameOwner,sameName,root,selected,original⟩
          else throw .request
      else throw .request
    else throw .request
  else throw .request

structure Assertion {artifact catalogue context description graph implementations references prepared root requested caller scope}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (marker : SourceOperation.Marker artifact.sources caller scope)
    (target : Sigma (@RuntimeOperationOccurrenceTree.Tree artifact catalogue context description graph implementations references prepared)) where
  binding : RecordAt checked target.2.located
  child : RuntimeOperationTree.Value
  owner : String
  name : String
  written : binding.record.checked.node = .requested child.index owner name
  children : binding.record.checked.children = [child]
  requirement : RuntimePreparedOperation.Requirement artifact catalogue binding.record.occurrence.result
  original : binding.record.occurrence.requirements = [requirement]
  subject : requirement.subject = child.index
  equation : RuntimeOperationTree.Meaning child requirement root
  native : binding.record.checked.requirements =
    .requested child owner name written children requirement original subject equation
  sameOwner : owner = marker.selected.resolution.moduleName
  sameName : name = marker.selected.resolution.declaration.name
  meaning : MeaningOriginal marker requirement.request

/-- The followed source path ends at this same requested native node, whose
single child and full Meaning equation are retained above. -/
theorem Assertion.located_requested {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (assertion : @Assertion artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target) :
    target.2.located.node = .requested assertion.child.index assertion.owner assertion.name :=
  assertion.binding.node.symm.trans assertion.written

/- Bind the original marker to this exact previously retained native record. -/
def readBoundAssertion {artifact catalogue context description graph implementations references prepared root requested caller scope}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (marker : SourceOperation.Marker artifact.sources caller scope)
    (target : Sigma (@RuntimeOperationOccurrenceTree.Tree artifact catalogue context description graph implementations references prepared))
    (binding : RecordAt checked target.2.located) :
    WorkM (Assertion checked marker target) := do
  match native : binding.record.checked.requirements with
  | .none .. | .arguments .. => throw .request
  | .requested child owner name written children requirement original subject equation =>
    exactWork (Exact.charge (16*(owner.utf8ByteSize+name.utf8ByteSize+
      marker.selected.resolution.moduleName.utf8ByteSize+marker.selected.resolution.declaration.name.utf8ByteSize+1)))
    if sameOwner : owner = marker.selected.resolution.moduleName then
      if sameName : name = marker.selected.resolution.declaration.name then
        let meaning ← readMeaningOriginal marker requirement.request
        return ⟨binding,child,owner,name,written,children,requirement,original,subject,equation,
          native,sameOwner,sameName,meaning⟩
      else throw .request
    else throw .request

private def readAssertion {artifact catalogue context description graph implementations references prepared root requested caller scope}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (marker : SourceOperation.Marker artifact.sources caller scope)
    (target : Sigma (@RuntimeOperationOccurrenceTree.Tree artifact catalogue context description graph implementations references prepared)) :
    WorkM (Assertion checked marker target) := do
  let binding ← readRecordAt checked target.2.located
  readBoundAssertion checked marker target binding

/-- Pure projection of the SAME retained source read. The header-only legacy
origin cannot supply original assertion coverage. Primitive origins contain no
written checked_op. No source or Meaning reader is executed here. -/
def originalMarkers {sources owner tokens} (operation : QuantumArms.Operation sources owner tokens) :
    Option (Σ scope, List (SourceOperation.Marker sources owner scope)) :=
  match operation.original with
  | .source _ _ _ scope read _ _ => some ⟨scope,read.provenance.markers⟩
  | .instantiated _ _ _ _ _ scope read _ _ => some ⟨scope,read.provenance.markers⟩
  | .primitive .. => some ⟨[],[]⟩
  | .named .. => none

structure Entry {artifact catalogue context description graph implementations references prepared root requested caller scope}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (tree : RuntimeOperationOccurrenceTree.Checked prepared)
    (markers : List (SourceOperation.Marker artifact.sources caller scope)) where
  index : Fin markers.length
  target : Sigma (RuntimeOperationOccurrenceTree.Tree prepared)
  followed : RuntimeInterval.Computed
    (RuntimeOperationOccurrenceTree.follow ⟨tree.index,tree.tree⟩ (markers[index.val]'index.isLt).path) target
  assertion : Assertion checked (markers[index.val]'index.isLt) target

private def readEntry {artifact catalogue context description graph implementations references prepared root requested caller scope}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (tree : RuntimeOperationOccurrenceTree.Checked prepared)
    (markers : List (SourceOperation.Marker artifact.sources caller scope)) (index : Fin markers.length) :
    WorkM (Entry checked tree markers) := do
  let target ← NaturalAffine.witness
    (RuntimeOperationOccurrenceTree.follow ⟨tree.index,tree.tree⟩ (markers[index.val]'index.isLt).path)
  let assertion ← readAssertion checked (markers[index.val]'index.isLt) target.val
  return ⟨index,target.val,by with_reducible exact target.property,assertion⟩

/-- All original markers of this exact operation are associated, in order.
This covers neither a different supplying invocation nor every original queue
duty. In particular, it must not reduce SourcePendingMeaning's pending count. -/
structure Checked {artifact catalogue owner description graph implementations references}
    (originals : Option (Σ scope, List (SourceOperation.Marker artifact.sources owner scope)))
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue (.source owner) description graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested) where
  scope : List String
  markers : List (SourceOperation.Marker artifact.sources owner scope)
  original : originals = some ⟨scope,markers⟩
  tree : RuntimeOperationOccurrenceTree.Checked prepared
  traversed : RuntimeInterval.Computed (RuntimeOperationOccurrenceTree.read prepared) tree
  entries : List (Entry checked tree markers)
  every : entries.map (·.index) = List.finRange markers.length

/-- Use the same native result and original source operation. No provider,
body, catalogue or Meaning query is repeated to manufacture this association. -/
def readMarkers {artifact catalogue owner description graph implementations references}
    (originals : Option (Σ scope, List (SourceOperation.Marker artifact.sources owner scope)))
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue (.source owner) description graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested) :
    WorkM (Checked originals prepared checked) := do
  match originals with
  | none => throw .request
  | some ⟨scope,markers⟩ =>
    exactWork (Exact.charge (16*(markers.length+prepared.occurrences.length+description.nodes.length+1)^2))
    let tree ← NaturalAffine.witness (RuntimeOperationOccurrenceTree.read prepared)
    let entries ← (List.finRange markers.length).mapM (readEntry checked tree.val markers)
    if every : entries.map (·.index) = List.finRange markers.length then
      return ⟨scope,markers,rfl,tree.val,by with_reducible exact tree.property,entries,every⟩
    else throw .request

def read {artifact catalogue owner tokens implementations references}
    (operation : QuantumArms.Operation artifact.sources owner tokens)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue operation.graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested) :
    WorkM (Checked (originalMarkers operation) prepared checked) :=
  readMarkers (originalMarkers operation) prepared checked

def applicationMarkers {sources owner} (event : SourceOperationApplication.Event sources owner) :
    Option (Σ scope, List (SourceOperation.Marker sources owner scope)) :=
  some ⟨event.scope,event.operation.provenance.markers⟩

def supplyingMarkers {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (index : Fin event.target.operationActuals.sourceActuals.length) :
    Option (Σ scope, List (SourceOperation.Marker sources caller scope)) :=
  some ⟨event.scope,event.target.operationActuals.sourceActuals[index].checked.provenance.markers⟩

/-- The retained source origin selects the exact marker list.
An unlocated graph has no original assertion coverage. -/
def OriginChecked {artifact catalogue context description graph implementations references}
    (origin : @RuntimeGraphOperation.Origin artifact.sources context description graph)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested) : Type :=
  match origin with
  | .unlocated => Unit
  | .arm operation => Checked (originalMarkers operation) prepared checked
  | .application event => Checked (applicationMarkers event) prepared checked
  | .supplying event index => Checked (supplyingMarkers event index) prepared checked

/-- Consume the actual source origin carried by this same graph request.
An arm or application supplies its own original marker association. -/
def readOrigin {artifact catalogue context description graph implementations references}
    (origin : @RuntimeGraphOperation.Origin artifact.sources context description graph)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested) :
    WorkM (OriginChecked origin prepared checked) := by
  cases origin with
  | unlocated => exact do
    exactWork (Exact.charge 1)
    pure ()
  | arm operation => exact do
    exactWork (Exact.charge 1)
    read operation prepared checked
  | application event => exact do
    exactWork (Exact.charge 1)
    readMarkers (applicationMarkers event) prepared checked
  | supplying event index => exact do
    exactWork (Exact.charge (index.val+1))
    readMarkers (supplyingMarkers event index) prepared checked

end QleisliKernel.Qirf.RuntimeSourceOperationMarkers
