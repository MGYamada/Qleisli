import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeCallInterval

/-! Interpret the actual pure named call as a semantic call frame with an
empty ordinary interface. This proof view reuses the checked entry, literal
operations and return, without running a second native checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureNamedScope
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite

abbrev State := Raw.Observation.State

private def ordinaryFrame (state : State) :=
  (state.classical,state.active,state.scope,state.observe)

private theorem pureStep_frame {dependencies recurse initial final op work left}
    (read : (Raw.Observation.checkStep dependencies recurse initial (.pure op)).run work =
      (.ok final,left)) : ordinaryFrame final = ordinaryFrame initial := by
  unfold Raw.Observation.checkStep at read
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨next,_,action,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst final
  unfold Raw.Observation.checkAction at action
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ action
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  rw [(pure_success _ _ _ _ h).1]
  rfl

private theorem pureFold_frame {dependencies recurse initial final work left} {operations : List Semantics.Raw.Op}
    (read : ((operations.map Semantics.Observation.Op.pure).foldlM
      (Raw.Observation.checkStep dependencies recurse) initial).run work = (.ok final,left)) :
    ordinaryFrame final = ordinaryFrame initial := by
  induction operations generalizing initial work with
  | nil =>
    exact congrArg ordinaryFrame (pure_success _ _ _ _ read).1
  | cons op rest ih =>
    simp only [List.map_cons,List.foldlM_cons] at read
    obtain ⟨next,middle,head,tail⟩ := bind_success _ _ _ _ _ read
    exact (ih tail).trans (pureStep_frame head)

theorem pureOps_frame {dependencies fuel initial final} {operations : List Semantics.Raw.Op}
    (read : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies fuel initial (operations.map Semantics.Observation.Op.pure)) final) :
    ordinaryFrame final = ordinaryFrame initial := by
  obtain ⟨work,left,checked⟩ := read
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    unfold Raw.Observation.checkOps at checked
    obtain ⟨middle,_,folded,h⟩ := bind_success _ _ _ _ _ checked
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst final
    exact pureFold_frame folded

private theorem initial_classical {program state} (empty : program.classicalInputs = [])
    (read : RuntimeInterval.Computed (PureInterval.initial program) state) :
    state.classical = [] := by
  obtain ⟨work,left,checked⟩ := read
  unfold PureInterval.initial at checked
  obtain ⟨quantum,_,_,returned⟩ := bind_success _ _ _ _ _ checked
  rw [empty] at returned
  change (pure ({quantum} : State) : WorkM State).run _ = (.ok state,left) at returned
  rw [(pure_success _ _ _ _ returned).1]

/-- The actual caller prefix contains exactly the first pure operations in
its block. The successful prefix read preserves the empty ordinary frame. -/
theorem purePrefix_classical {dependencies program block start count} {operations : List Semantics.Raw.Op}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (initial : block.entry.classical = [])
    (literal : block.operations = operations.map Semantics.Observation.Op.pure) :
    interval.before.classical = [] := by
  have read := interval.prefixRead
  rw [literal,← List.map_take] at read
  exact (congrArg Prod.fst (pureOps_frame read)).trans initial

/-- The literal block carries the exact pure instruction shape and empty
ordinary entry needed to apply the same recursive proof at each child. -/
structure PureBlock {dependencies program} (block : RuntimeInterval.Block dependencies program) : Prop where
  empty : block.entry.classical = []
  literal : ∃ operations : List Semantics.Raw.Op, block.operations = operations.map Semantics.Observation.Op.pure

theorem PureBlock.prefix {dependencies program block start count}
    (pureBlock : @PureBlock dependencies program block)
    (interval : RuntimeInterval.Checked block start count) : interval.before.classical = [] := by
  obtain ⟨operations,literal⟩ := pureBlock.literal
  exact purePrefix_classical interval pureBlock.empty literal

theorem pureChildBlock {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs) :
    PureBlock scope.prepared.block :=
  ⟨initial_classical rfl scope.prepared.inputRead,⟨scope.operations,rfl⟩⟩

private theorem literal_exit_empty {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (entry : scope.interval.before.classical = []) :
    scope.interval.after.classical = [] := by
  have read := scope.interval.intervalRead
  rw [scope.literal] at read
  exact (congrArg Prod.fst (pureOps_frame read)).trans entry

private theorem local_exit_empty {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs) :
    scope.localAfter.classical = [] :=
  (congrArg Prod.fst (pureOps_frame scope.nativeRead)).trans (initial_classical rfl scope.entryRead)

/-- Supply the observation-frame interface to the existing call composition
proofs. Both views use exactly the original pure child program. -/
def callView {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (entry : scope.interval.before.classical = []) :
    RuntimeCallScope.Checked block start count inputs {} .unitary where
  interval := scope.interval
  selected := scope.selected
  atEntry := scope.atEntry
  visible := ⟨[],rfl,by simp [RuntimeOrdinaryBody.visibleIds,entry],by simp⟩
  localEntry := scope.localEntry
  entryRead := by
    rw [scope.literal]
    exact scope.entryRead
  localAfter := scope.localAfter
  nativeRead := by
    rw [scope.literal]
    exact scope.nativeRead
  returned := scope.returned
  complete := scope.complete
  atExit := scope.atExit
  spectators := scope.spectators
  classicalOutputs := []
  localClassical := by simp [RuntimeOrdinaryBody.visibleIds,local_exit_empty scope]
  actualClassical := by simp [RuntimeOrdinaryBody.visibleIds,literal_exit_empty scope entry]
  prepared := by
    rw [scope.literal]
    exact scope.prepared

theorem callView_program {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (entry : scope.interval.before.classical = []) :
    (callView scope entry).program = scope.program := by
  unfold RuntimeCallScope.Checked.program RuntimeCallInterval.Checked.program
  rw [scope.literal]
  rfl

theorem callView_prepared {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (entry : scope.interval.before.classical = []) :
    HEq (callView scope entry).prepared scope.prepared := by
  unfold callView
  exact cast_heq _ _

theorem callView_subject {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (entry : scope.interval.before.classical = []) :
    (⟨(callView scope entry).program,(callView scope entry).prepared⟩ :
      (p : Semantics.Observation.Program) × RuntimeInterval.Prepared dependencies p) =
      ⟨scope.program,scope.prepared⟩ :=
  Sigma.ext (callView_program scope entry) (callView_prepared scope entry)

/-- The original prepared pure program supplies both empty ordinary
interfaces to this view. No caller-provided ordinary-state equality is needed. -/
def rootCallView {dependencies program start count inputs} {operations : List Semantics.Raw.Op}
    (prepared : RuntimeInterval.Prepared dependencies program)
    (scope : RuntimeCallInterval.Checked prepared.block start count inputs)
    (empty : program.classicalInputs = [])
    (literal : program.operations = operations.map Semantics.Observation.Op.pure) :
    RuntimeCallScope.Checked prepared.block start count inputs {} .unitary :=
  callView scope (purePrefix_classical scope.interval (initial_classical empty prepared.inputRead) literal)

#print axioms pureChildBlock
#print axioms pureOps_frame
#print axioms rootCallView
#print axioms callView
#print axioms callView_program
end Qleisli.RuntimePureNamedScope
