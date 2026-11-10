import QleisliKernel.Qirf.RuntimeBodyOperations
import QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence

/-! Retain an original middle selection at its actual position in a body's
stored witness. The adjacent-call view ties all three positions to the original
steps and to each named callee's prepared block.
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

/-- Three adjacent named calls at a fixed position in the original body. -/
structure Adjacent {dependencies program block} (steps : List (Step dependencies program block)) where
  earlier : List (Step dependencies program block)
  pre : Step dependencies program block
  center : Step dependencies program block
  post : Step dependencies program block
  later : List (Step dependencies program block)
  original : steps = earlier ++ pre :: center :: post :: later
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

/-- A Type-side retained leaf: executable access to the SAME stored literal
and its read receipt, with the path certified by the original Witness. -/
structure SelectionAt {dependencies rootItem rootCount program block}
    (witness : @Witness dependencies rootItem rootCount)
    (node : Node dependencies program block) (ordinal : Nat) where
  literal : RuntimeSelectionWitness.Checked node
  obtained : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) literal
  rank : Nat
  path : List Edge
  original : At witness rank path ⟨program,block,ordinal,node,literal,obtained⟩

private structure ConsData {dependencies program block ordinal first rest count}
    (witness : @Witness dependencies (.steps (program := program) (block := block) ordinal (.cons first rest)) count) where
  a : Nat
  b : Nat
  head : Witness (.step ordinal first) a
  tail : Witness (.steps (ordinal+1) rest) b
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
    exact ⟨_,_,head,tail,fun _ _ _ inside => .first inside,fun _ _ _ inside => .rest inside⟩

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
    exact ⟨literal,obtained,0,[],.selection⟩

private def singletonData {dependencies program block node count}
    (selected : @IsSelection dependencies program block node)
    (witness : Witness (.steps (program := program) (block := block) 0 (.cons (.pure node) .nil)) count) :
    SelectionAt witness node 0 := by
  let parts := consData witness
  let child := pureData parts.head
  let leaf := selectionData selected child.nested
  refine ⟨leaf.literal,leaf.obtained,leaf.rank,.atOrdinal 0 :: .pureStep 0 :: leaf.path,?_⟩
  exact parts.firstLift _ _ _ (child.liftAt _ _ _ leaf.original)

def RetainedData {dependencies rootItem rootCount program block step}
    (witness : @Witness dependencies rootItem rootCount) : @Middle dependencies program block step → Type
  | .named node _ => SelectionAt witness node 0

/-- Follow the actual source prefix in the stored witness. Each preceding
step contributes its real selection count and original ordinal edge. -/
private def retainedData_at {dependencies program block step count ordinal}
    (earlier later : List (Step dependencies program block))
    (occurrence : @Middle dependencies program block step)
    (witness : @Witness dependencies (.steps ordinal (Steps.ofList (earlier ++ step :: later))) count) :
    RetainedData witness occurrence := by
  cases occurrence with
  | @named start span inputs sources caller before childHistory childRetired ordinary
      event scope body read boundary finalOrdinary node selected =>
    let target : Step dependencies program block :=
      .named event scope body read boundary finalOrdinary (.cons (.pure node) .nil)
    change SelectionAt witness node 0
    let atHead {ordinal count : Nat}
        (w : Witness (.steps ordinal (.cons target (Steps.ofList later))) count) :
        SelectionAt w node 0 := by
      let current := consData w
      let child := namedData current.head
      let leaf := singletonData selected child.nested
      refine ⟨leaf.literal,leaf.obtained,leaf.rank,.atOrdinal ordinal :: child.edge :: leaf.path,?_⟩
      exact current.firstLift _ _ _ (child.liftAt _ _ _ leaf.original)
    refine (Nat.rec (motive := fun fuel =>
      (remaining : List (Step dependencies program block)) → remaining.length ≤ fuel →
      ∀ {ordinal count : Nat}
        (w : Witness (.steps ordinal (Steps.ofList (remaining ++ target :: later))) count),
        SelectionAt w node 0) ?_ ?_ earlier.length) earlier (Nat.le_refl _) witness
    · intro remaining bound ordinal count current
      cases remaining with
      | nil => exact atHead current
      | cons head tail => exact False.elim (Nat.not_succ_le_zero tail.length bound)
    · intro fuel recurse remaining bound ordinal count current
      cases remaining with
      | nil => exact atHead current
      | cons head tail =>
        change Witness (.steps ordinal (.cons head (Steps.ofList (tail ++ target :: later)))) count at current
        let parts := consData current
        let held := recurse tail (Nat.le_of_succ_le_succ bound) parts.tail
        exact ⟨held.literal,held.obtained,parts.a+held.rank,.nextOrdinal (ordinal+1) :: held.path,
          parts.restLift _ _ _ held.original⟩

/-- Retain a selection in an exact witnessed step list. Each recursive
caller passes the list for its original body or selected branch. -/
def actual_steps_selection {dependencies program block steps count step}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (earlier later : List (Step dependencies program block))
    (occurrence : @Middle dependencies program block step)
    (split : steps = earlier ++ step :: later) : RetainedData witness occurrence := by
  subst steps
  exact retainedData_at earlier later occurrence witness

private theorem stepWitness {dependencies program block step ordinal count}
    (earlier later : List (Step dependencies program block))
    (witness : @Witness dependencies (.steps ordinal (Steps.ofList (earlier ++ step :: later))) count) :
    ∃ atOrdinal selectedCount, Nonempty (Witness (.step atOrdinal step) selectedCount) := by
  induction earlier generalizing ordinal count with
  | nil =>
    let current := consData witness
    exact ⟨ordinal,current.a,⟨current.head⟩⟩
  | cons first earlier ih =>
    let current := consData witness
    exact ih current.tail

def ConditionalWitnesses {dependencies program block} : Step dependencies program block → Prop
  | .conditional _ _ _ _ _ _ left right =>
    (∃ count, Nonempty (Witness (.steps 0 left) count)) ∧
    (∃ count, Nonempty (Witness (.steps 0 right) count))
  | _ => True

/-- The same original conditional witness gives the exact retained child
lists on both sides. This only projects data from the completed traversal. -/
theorem actual_conditional_steps {dependencies program block steps count step}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (earlier later : List (Step dependencies program block))
    (split : steps = earlier ++ step :: later) : ConditionalWitnesses step := by
  subst steps
  cases step with
  | conditional path event source branch branchRead action left right =>
    obtain ⟨_,_,⟨here⟩⟩ := stepWitness earlier later witness
    cases here with
    | leaf original => cases original
    | selection original _ _ => cases original
    | child original _ => cases original
    | pair original yes no =>
      cases original
      exact ⟨⟨_,⟨yes⟩⟩,⟨_,⟨no⟩⟩⟩
  | pure _ => trivial
  | named _ _ _ _ _ _ _ => trivial
  | gap _ => trivial
  | observation _ => trivial

/-- Retain the original selection at a specified occurrence, with its actual
global rank and path. The prefix and suffix may contain other selections. -/
def actual_body_selection {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (earlier later : List (Step body.root.dependencies body.root.program body.checked.native.block))
    {step : Step body.root.dependencies body.root.program body.checked.native.block}
    (occurrence : Middle step)
    (split : body.checked.result.steps = earlier ++ step :: later) :
    RetainedData body.selections.witness occurrence :=
  actual_steps_selection body.selections.witness earlier later occurrence split

def actual_body_middle {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : Three body.checked.result.steps) : RetainedData body.selections.witness view.centerSelection :=
  actual_body_selection body [view.pre] [view.post] view.centerSelection view.original

def actual_adjacent_middle {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : Adjacent body.checked.result.steps) : RetainedData body.selections.witness view.centerSelection :=
  actual_body_selection body (view.earlier++[view.pre]) (view.post::view.later) view.centerSelection
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using view.original)

#print axioms actual_body_selection
#print axioms actual_body_middle
#print axioms actual_conditional_steps

end QleisliKernel.Qirf.RuntimeNamedThreeOccurrence
