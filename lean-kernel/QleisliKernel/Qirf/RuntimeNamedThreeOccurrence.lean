import QleisliKernel.Qirf.RuntimeBodyOperations
import QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence

/-! Read the middle selection from an original three-call body's stored witness.
The enclosing list has a one-primitive call on either side. All three positions
are tied to original steps, including the precise named callee's prepared block.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeNamedThreeOccurrence
open QleisliKernel Finite SourceTypes RuntimePureBody
open RuntimeSelectionSteps (Item Witness Selection Edge At)

def IsSelection {dependencies program block} : Node dependencies program block → Prop
  | .selection .. => True
  | _ => False

/-- The child block is the actual named scope's own prepared block. -/
inductive Middle {dependencies program block} : Step dependencies program block → Type where
  | named {start count inputs sources caller before childHistory childRetired ordinary}
      {event : SourceRuntimeContext.NamedEvent sources caller}
      {scope : RuntimeCallScope.Checked block start count inputs ordinary event.effect}
      {body : SourceRuntimeTrace.Body event.target.signature}
      {read : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body}
      {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before childHistory childRetired body.checked.summary.value}
      {finalOrdinary : RuntimeOrdinaryBody.State}
      (node : Node dependencies scope.program scope.prepared.block) (selection : IsSelection node) :
      Middle (.named event scope body read boundary finalOrdinary (.cons (.pure node) .nil))

private def selection? {dependencies program block} (node : Node dependencies program block) :
    Option (PLift (IsSelection node)) :=
  match node with
  | .selection .. => some ⟨True.intro⟩
  | _ => none

def middle? {dependencies program block} (step : Step dependencies program block) : Option (Middle step) :=
  match step with
  | .named _ _ _ _ _ _ (.cons (.pure node) .nil) => do
    let selected ← selection? node
    return .named node selected.down
  | _ => none

/-- This exact list shape is a bounded view, not a general-body judgment. -/
structure Three {dependencies program block} (steps : List (Step dependencies program block)) where
  pre : Step dependencies program block
  center : Step dependencies program block
  post : Step dependencies program block
  original : steps = [pre,center,post]
  prePrimitive : RuntimeNamedPrimitiveOccurrence.Occurrence pre
  centerSelection : Middle center
  postPrimitive : RuntimeNamedPrimitiveOccurrence.Occurrence post

/-- Non-three lists, extra gaps/observations, or different child shapes stay
unchanged in their original result and yield none. There is no filtered list,
name/offset lookup, matrix equality or new native validation here. -/
def inspect? {dependencies program block} (steps : List (Step dependencies program block)) : Option (Three steps) :=
  match steps with
  | [pre,center,post] => do
    let first ← RuntimeNamedPrimitiveOccurrence.inspect? pre
    let middle ← middle? center
    let last ← RuntimeNamedPrimitiveOccurrence.inspect? post
    return ⟨pre,center,post,rfl,first,middle,last⟩
  | _ => none

theorem Three.preAt {dependencies program block steps} (view : @Three dependencies program block steps) :
    steps[0]? = some view.pre := by
  cases view with
  | mk pre center post original _ _ _ => cases original; rfl

theorem Three.centerAt {dependencies program block steps} (view : @Three dependencies program block steps) :
    steps[1]? = some view.center := by
  cases view with
  | mk pre center post original _ _ _ => cases original; rfl

theorem Three.postAt {dependencies program block steps} (view : @Three dependencies program block steps) :
    steps[2]? = some view.post := by
  cases view with
  | mk pre center post original _ _ _ => cases original; rfl

private def namedEdge {sources caller} (ordinal : Nat) (event : SourceRuntimeContext.NamedEvent sources caller) : Edge :=
  .named ordinal caller event.target.callerName event.call.calleeOffset
    event.target.resolution.moduleName event.target.resolution.declaration.name

private theorem nil_count {dependencies program block ordinal count}
    (witness : @Witness dependencies (.steps (program := program) (block := block) ordinal .nil) count) : count = 0 := by
  cases witness with
  | leaf _ => rfl
  | selection original _ _ => cases original
  | child original _ => cases original
  | pair original _ _ => cases original

private theorem primitive_count {dependencies program block ordinal first size input output role kind count}
    {action : @RuntimePrimitiveAction.Checked dependencies program block first size input output role kind}
    {original : RuntimePrimitiveSource.Checked action}
    (witness : Witness (.node ordinal (.primitive action original)) count) : count = 0 := by
  cases witness with
  | leaf _ => rfl
  | selection original _ _ => cases original
  | child original _ => cases original
  | pair original _ _ => cases original

/-- A Type-side retained leaf: executable access to the SAME stored literal
and its read receipt, with the path certified by the original Witness. -/
structure SelectionAt {dependencies rootItem rootCount program block}
    (witness : @Witness dependencies rootItem rootCount)
    (node : Node dependencies program block) (ordinal : Nat) where
  literal : RuntimeSelectionWitness.Checked node
  obtained : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) literal
  one : rootCount = 1
  path : List Edge
  original : At witness 0 path ⟨program,block,ordinal,node,literal,obtained⟩

private structure ConsData {dependencies program block ordinal first rest count}
    (witness : @Witness dependencies (.steps (program := program) (block := block) ordinal (.cons first rest)) count) where
  a : Nat
  b : Nat
  head : Witness (.step ordinal first) a
  tail : Witness (.steps (ordinal+1) rest) b
  total : count = a+b
  firstLift : ∀ rank path found, At head rank path found → At witness rank (.atOrdinal ordinal :: path) found
  restLift : ∀ rank path found, At tail rank path found → At witness (a+rank) (.nextOrdinal (ordinal+1) :: path) found

private def consData {dependencies program block ordinal first rest count}
    (witness : @Witness dependencies (.steps (program := program) (block := block) ordinal (.cons first rest)) count) :
    ConsData witness := by
  cases witness with
  | leaf original => cases original
  | selection original _ _ => cases original
  | child original _ => cases original
  | pair original head tail =>
    cases original
    exact ⟨_,_,head,tail,rfl,fun _ _ _ inside => .first inside,fun _ _ _ inside => .rest inside⟩

private structure ChildData {dependencies item count} (witness : @Witness dependencies item count)
    (one : Item dependencies) (edge : Edge) where
  nested : Witness one count
  liftAt : ∀ rank path found, At nested rank path found → At witness rank (edge :: path) found

private def ChildData.edge {dependencies item count}
    {witness : @Witness dependencies item count} {one : Item dependencies} {edge : Edge}
    (_held : ChildData witness one edge) : Edge := edge

private def pureData {dependencies program block ordinal node count}
    (witness : @Witness dependencies (.step (program := program) (block := block) ordinal (.pure node)) count) :
    ChildData witness (.node ordinal node) (.pureStep ordinal) := by
  cases witness with
  | leaf original => cases original
  | selection original _ _ => cases original
  | pair original _ _ => cases original
  | child original nested =>
    cases original
    exact ⟨nested,fun _ _ _ inside => .child inside⟩

private def namedData {dependencies program block ordinal start count inputs sources caller
    before childHistory childRetired ordinary bodyCount}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    {scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary event.effect}
    {body : SourceRuntimeTrace.Body event.target.signature}
    {read : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body}
    {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before childHistory childRetired body.checked.summary.value}
    {finalOrdinary : RuntimeOrdinaryBody.State} {children : Steps dependencies scope.program scope.prepared.block}
    (witness : Witness (.step ordinal (.named event scope body read boundary finalOrdinary children)) bodyCount) :
    ChildData witness (.steps 0 children) (namedEdge ordinal event) := by
  cases witness with
  | leaf original => cases original
  | selection original _ _ => cases original
  | pair original _ _ => cases original
  | child original nested =>
    cases original
    exact ⟨nested,fun _ _ _ inside => .child inside⟩

private theorem primitive_occurrence_count {dependencies program block ordinal step count}
    (occurrence : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (witness : Witness (.step ordinal step) count) : count = 0 := by
  cases occurrence with
  | named _original _bound =>
    let child := namedData witness
    let parts := consData child.nested
    let first := pureData parts.head
    have total := parts.total
    have zeroHead := primitive_count first.nested
    have zeroTail := nil_count parts.tail
    omega

private def selectionData {dependencies program block ordinal node count}
    (selected : @IsSelection dependencies program block node)
    (witness : Witness (.node ordinal node) count) : SelectionAt witness node ordinal := by
  cases node <;> simp_all only [IsSelection]
  cases witness with
  | leaf original => cases original
  | child original _ => cases original
  | pair original _ _ => cases original
  | selection original literal obtained =>
    cases original
    exact ⟨literal,obtained,rfl,[],.selection⟩

private def singletonData {dependencies program block node count}
    (selected : @IsSelection dependencies program block node)
    (witness : Witness (.steps (program := program) (block := block) 0 (.cons (.pure node) .nil)) count) :
    SelectionAt witness node 0 := by
  let parts := consData witness
  let child := pureData parts.head
  let leaf := selectionData selected child.nested
  have total := parts.total
  have one := leaf.one
  have zero := nil_count parts.tail
  refine ⟨leaf.literal,leaf.obtained,by omega,.atOrdinal 0 :: .pureStep 0 :: leaf.path,?_⟩
  exact parts.firstLift _ _ _ (child.liftAt _ _ _ leaf.original)

def RetainedData {dependencies rootItem rootCount program block step}
    (witness : @Witness dependencies rootItem rootCount) : @Middle dependencies program block step → Type
  | .named node _ => SelectionAt witness node 0

/-- Fixed structural projections, not another recursive traversal or reader.
The path identifies this leaf in the complete stored traversal. -/
private def retainedData_three {dependencies program block steps count}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (view : Three steps) : RetainedData witness view.centerSelection := by
  cases view with
  | mk pre center post order prePrimitive middle postPrimitive =>
    subst steps
    cases middle with
    | named node selected =>
      change SelectionAt witness node 0
      change Witness (.steps 0 (.cons pre (.cons _ (.cons post .nil)))) count at witness
      let whole := consData witness
      let middle := consData whole.tail
      let final := consData middle.tail
      let child := namedData middle.head
      let leaf := singletonData selected child.nested
      have total := whole.total
      have middleCount := middle.total
      have finalCount := final.total
      have one := leaf.one
      have preCount := primitive_occurrence_count prePrimitive whole.head
      have postCount := primitive_occurrence_count postPrimitive final.head
      have endCount := nil_count final.tail
      refine ⟨leaf.literal,leaf.obtained,by omega,.nextOrdinal 1 :: .atOrdinal 1 :: child.edge :: leaf.path,?_⟩
      have atMiddle := middle.firstLift _ _ _ (child.liftAt _ _ _ leaf.original)
      have atRoot := whole.restLift _ _ _ atMiddle
      simpa only [preCount,Nat.zero_add] using atRoot

def actual_body_middle {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : Three body.checked.result.steps) : RetainedData body.selections.witness view.centerSelection :=
  retainedData_three body.selections.witness view

#print axioms actual_body_middle

end QleisliKernel.Qirf.RuntimeNamedThreeOccurrence
