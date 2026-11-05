import QleisliKernel.Qirf.RuntimeSourceOperationMarkers

/-! Follow exact child positions in a checked native operation tree. Each
child cursor ties the parent's actual Value to the complete output of the
record at that occurrence. Formal projection also uses the evaluator's actual
successful computation. This supplies no generic transport or duty discharge.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNativeSubject
open QleisliKernel Finite SourceTypes
open RuntimeOperationTree (Value)
open RuntimeSourceOperationMarkers (RecordAt Assertion)
open QleisliKernel.Semantics.Exact (Matrix)

structure Cursor {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) where
  tree : Sigma (RuntimeOperationOccurrenceTree.Tree prepared)
  binding : RecordAt checked tree.2.located

def Cursor.node {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) :=
  cursor.binding.record.checked.node

def Cursor.value {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) : Value :=
  cursor.binding.record.checked.output

structure Child {artifact catalogue context description graph implementations references prepared root requested checked}
    (parent : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (position : Nat) where
  cursor : Cursor checked
  treeSelected : parent.tree.2.children[position]? = some cursor.tree
  bound : RuntimeInterval.Computed (RuntimeSourceOperationMarkers.readRecordAt checked cursor.tree.2.located) cursor.binding
  outputSelected : parent.binding.record.checked.children[position]? = some cursor.value

private theorem value_eq (a b : Value)
    (same : a.index = b.index ∧ a.input = b.input ∧ a.output = b.output ∧ a.action = b.action) : a = b := by
  cases a
  cases b
  simp_all

def readChild {artifact catalogue context description graph implementations references prepared root requested checked}
    (parent : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (position : Nat) : WorkM (Child parent position) := do
  let children := parent.tree.2.children
  let values := parent.binding.record.checked.children
  exactWork (Exact.charge (16*(children.length+values.length+1)))
  match treeSelected : children[position]?, selected : values[position]? with
  | some tree,some value =>
    let binding ← NaturalAffine.witness (RuntimeSourceOperationMarkers.readRecordAt checked tree.2.located)
    let cursor : Cursor checked := ⟨tree,binding.val⟩
    let output := cursor.value
    exactWork (Exact.charge (16*(Raw.OwnerFlow.fields [⟨0,value.input⟩,⟨0,value.output⟩,
      ⟨0,output.input⟩,⟨0,output.output⟩]+1)+value.action.entries.length+output.action.entries.length+1))
    if same : value.index = output.index ∧ value.input = output.input ∧
        value.output = output.output ∧ value.action = output.action then
      return ⟨cursor,treeSelected,by with_reducible exact binding.property,
        selected.trans (congrArg some (value_eq value output same))⟩
    else throw .equation
  | _,_ => throw .request

def ofAssertion {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (assertion : @Assertion artifact catalogue context description graph implementations references prepared root requested caller scope
      checked marker target) : Cursor checked := ⟨target,assertion.binding⟩

structure Subject {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (assertion : @Assertion artifact catalogue context description graph implementations references prepared root requested caller scope
      checked marker target) where
  child : Child (ofAssertion assertion) 0
  childRead : RuntimeInterval.Computed (readChild (ofAssertion assertion) 0) child
  same : assertion.child = child.cursor.value

def readSubject {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (assertion : @Assertion artifact catalogue context description graph implementations references prepared root requested caller scope
      checked marker target) : WorkM (Subject assertion) := do
  let held ← NaturalAffine.witness (readChild (ofAssertion assertion) 0)
  let child := held.val
  have same : assertion.child = child.cursor.value := by
    have selected := child.outputSelected
    change assertion.binding.record.checked.children[0]? = some child.cursor.value at selected
    rw [assertion.children,List.getElem?_cons_zero] at selected
    exact Option.some.inj selected
  return ⟨child,by with_reducible exact held.property,same⟩

def headerFormal {sources} (metadata : StaticOperation.Result sources) (ordinal : Nat) :
    Option StaticHeaders.Formal :=
  match metadata.formal with
  | none => none
  | some provider => match provider.signature.instantiation with
    | .closed _ => none
    | .static _ environment _ => environment.numeric.original.header.formals[ordinal]?

/-- Connect the executable formal reader's stored calculation to the exact
position on the original header. Equal-valued siblings cannot choose a position. -/
private theorem evaluated {sources} (metadata : StaticOperation.Result sources)
    (owner name : String) (bases : List (String × Semantics.FiniteCarrier.Basis))
    (naturals operations : List (String × Nat)) (ordinal : Nat) (children providers : List Matrix)
    (value : Matrix) (consumed : Nat) (formal : StaticHeaders.Formal)
    (original : headerFormal metadata ordinal = some formal)
    (calculated : RuntimeInterval.Computed (OperationIRMeaning.readNode metadata
      (.formal owner name bases naturals operations ordinal) children providers 0) (value,consumed)) :
    children[(operations.map (·.1)).idxOf formal.name]? = some value := by
  obtain ⟨before,after,ran⟩ := calculated
  obtain ⟨_,provider,args,env,sameOriginal,actual,position,present,instantiation,
    atOrdinal,_,samePosition,_,_,selected⟩ :=
    OperationIRMeaning.readNode_formal_selection metadata owner name bases naturals operations ordinal
      children providers 0 value consumed before after ran
  have actualFormal : headerFormal metadata ordinal = some actual := by
    simp only [headerFormal,present,instantiation,atOrdinal]
  have same := Option.some.inj (original.symm.trans actualFormal)
  subst actual
  simpa only [samePosition] using selected

structure Formal {artifact catalogue context description graph implementations references prepared root requested checked}
    (parent : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) where
  owner : String
  name : String
  bases : List (String × Semantics.FiniteCarrier.Basis)
  naturals : List (String × Nat)
  operations : List (String × Nat)
  ordinal : Nat
  node : parent.node = .formal owner name bases naturals operations ordinal
  provider : StaticOperation.Provider artifact.sources
  supplied : parent.binding.record.occurrence.result.formal = some provider
  providerName : provider.moduleName = owner ∧ provider.declarationName = name
  header : StaticHeaders.Formal
  original : headerFormal parent.binding.record.occurrence.result ordinal = some header
  headerOrdinal : header.ordinal = ordinal
  operation : ∃ tokens, header.kind = .operation tokens
  position : Nat
  selectedPosition : position = (operations.map (·.1)).idxOf header.name
  child : Child parent position
  childRead : RuntimeInterval.Computed (readChild parent position) child
  ports : child.cursor.value.input = parent.value.input ∧ child.cursor.value.output = parent.value.output
  action : child.cursor.value.action = parent.value.action

def Formal.formalName {artifact catalogue context description graph implementations references prepared root requested checked parent}
    (formal : @Formal artifact catalogue context description graph implementations references prepared root requested checked parent) :=
  formal.header.name

private theorem mapped_value_eq {α β : Type} (f : α → β) (xs : List α) (index : Nat) (x : α) (y : β)
    (element : xs[index]? = some x) (mapped : (xs.map f)[index]? = some y) : f x = y := by
  rw [List.getElem?_map,element,Option.map_some] at mapped
  exact Option.some.inj mapped

private theorem selectedAction {artifact catalogue context description graph implementations references prepared root requested checked}
    (parent : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    {owner name bases naturals operations ordinal} (node : parent.node = .formal owner name bases naturals operations ordinal)
    (formal : StaticHeaders.Formal) (original : headerFormal parent.binding.record.occurrence.result ordinal = some formal)
    (child : Child parent ((operations.map (·.1)).idxOf formal.name)) :
    child.cursor.value.action = parent.value.action := by
  let recd := parent.binding.record
  let run := fun n => RuntimeInterval.Computed (OperationIRMeaning.readNode recd.occurrence.result n
    (recd.checked.children.map RuntimeOperationTree.Value.action) recd.checked.provider.actions 0) (parent.value.action,recd.checked.consumedProviders)
  have calculated : run (.formal owner name bases naturals operations ordinal) :=
    (congrArg run node).mp recd.checked.calculated
  have selected := evaluated recd.occurrence.result owner name bases naturals operations ordinal
    (recd.checked.children.map RuntimeOperationTree.Value.action) recd.checked.provider.actions parent.value.action
    recd.checked.consumedProviders formal original calculated
  exact mapped_value_eq RuntimeOperationTree.Value.action recd.checked.children
    ((operations.map Prod.fst).idxOf formal.name) child.cursor.value parent.value.action child.outputSelected selected

def readFormal {artifact catalogue context description graph implementations references prepared root requested checked}
    (parent : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) :
    WorkM (Formal parent) := do
  let record := parent.binding.record
  match node : parent.node with
  | .formal owner name bases naturals operations ordinal =>
    match supplied : record.occurrence.result.formal with
    | none => throw .request
    | some provider =>
      let headerWork := SourceTrace.Meter.tokenFields provider.signature.original.occurrence.header
      exactWork (Exact.charge (16*(headerWork+(operations.map (fun op => op.1.utf8ByteSize+2)).sum+
        name.utf8ByteSize+owner.utf8ByteSize+provider.moduleName.utf8ByteSize+provider.declarationName.utf8ByteSize+1)))
      if providerName : provider.moduleName = owner ∧ provider.declarationName = name then
        match original : headerFormal record.occurrence.result ordinal with
        | none => throw .request
        | some formal =>
          if headerOrdinal : formal.ordinal = ordinal then
            match kind : formal.kind with
            | .operation tokens =>
              let position := (operations.map (·.1)).idxOf formal.name
              let held ← NaturalAffine.witness (readChild parent position)
              let child := held.val
              exactWork (Exact.charge (16*(Raw.OwnerFlow.fields [⟨0,parent.value.input⟩,⟨0,parent.value.output⟩,
                ⟨0,child.cursor.value.input⟩,⟨0,child.cursor.value.output⟩]+1)))
              if ports : child.cursor.value.input = parent.value.input ∧ child.cursor.value.output = parent.value.output then
                return ⟨owner,name,bases,naturals,operations,ordinal,node,provider,supplied,providerName,
                  formal,original,headerOrdinal,⟨tokens,kind⟩,position,rfl,child,by with_reducible exact held.property,
                  ports,selectedAction parent node formal original child⟩
              else throw .request
            | _ => throw .request
          else throw .request
      else throw .request
  | _ => throw .request

end QleisliKernel.Qirf.RuntimeNativeSubject
