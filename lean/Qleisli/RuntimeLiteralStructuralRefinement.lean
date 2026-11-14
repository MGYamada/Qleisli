import Qleisli.RuntimeLiteralLocalRefinement
import Qleisli.RuntimeStructuralHistory
import Qleisli.RuntimeSparseBlockEncoding

/-! Structural steps instantiate the common ordered arm induction with
independent sparse source frames. The same representation accepts the output
of each preceding structural step.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned OrdinaryRun)
open Qleisli.Semantics.ObservingAction (History run)
open Semantics.Observation (readOps)
open Qleisli.RuntimeStructuralHistory (Represents original_history)
open Qleisli.RuntimeStructuralSourceAction (sourceRegroup)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits_retains)
open Qleisli.RuntimeObservingValueRetention (run_retains_values)
open Qleisli.RuntimeOriginalObservationValues (original_gap_values_with_inherited)

def SemanticHistoryEncoding : HistoryEncoding := fun state bindings actual operator =>
  ∃ roles, ∃ checked : RuntimeOwnerMap.Checked roles state,
    checked.bindings = bindings ∧ ∃ frame : RuntimeSemanticForest.Frame bindings,
      ∀ column row, row < 2^state.quantum.frame.length →
        actual row column = RuntimeSemanticForest.action frame state.quantum.frame operator row column

def SemanticHistoryAgreesWithInherited := EncodedHistoryAgreesWithInherited SemanticHistoryEncoding

def SemanticHistoryAgrees := SemanticHistoryAgreesWithInherited none

theorem sparse_history_at_arm_entry {parent child owners ordinary source history}
    (inputs : List Nat) {inherited : Option (Nat → Prop)}
    (live : child.quantum.live = parent.quantum.live) (axes : child.quantum.frame = parent.quantum.frame)
    (issued : parent.classical ⊆ child.classical)
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs parent owners ordinary source history) :
    SemanticHistoryAgreesWithInherited inherited inputs child owners ordinary source history := by
  obtain ⟨sourceOwners,hidden,bits,values,roles,checked,bindings,input,represented⟩ := agrees
  let entry : RuntimeOwnerMap.Checked roles child :=
    ⟨checked.bindings,checked.ordered,checked.ownersDistinct,checked.tokensDistinct,live.symm ▸ checked.complete⟩
  refine ⟨sourceOwners,hidden,bits,⟨values.1,?_⟩,roles,entry,bindings,input,?_⟩
  · intro id member
    cases inherited with
    | none => exact Qleisli.RuntimeObservingPrefix.issued_mono issued (values.2 member)
    | some _ =>
      exact (values.2 member).imp (fun held => held) (Qleisli.RuntimeObservingPrefix.issued_mono issued)
  · intro column row bound
    rw [axes] at bound ⊢
    exact represented column row bound

theorem cast_represents {first second : RuntimeOwnerMap.Map}
    (same : first = second) (frame : RuntimeSemanticForest.Frame first)
    {state history operator} (represented : Represents frame state history operator) :
    Represents (same ▸ frame) state history operator := by
  cases same
  exact represented

theorem HistoryAgrees.toSemantic {inputs state owners ordinary source history}
    (agrees : HistoryAgrees inputs state owners ordinary source history) :
    SemanticHistoryAgrees inputs state owners ordinary source history := by
  obtain ⟨owners,hidden,measurements,values,_,checked,bindings,frame,represented⟩ := agrees
  exact ⟨owners,hidden,measurements,values,_,checked,bindings,bindings ▸ RuntimeSemanticForest.ofNative frame,
    cast_represents bindings _ represented⟩

private def structuralResult {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (source : SourceHistory) : Option (List SourceHistory) :=
  (sourceRegroup (event.arguments.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
    source.owners.bindings source.operator).map fun operator =>
      [{source with owners := action.after, operator}]

private noncomputable def registerResult {dependencies program sources caller block start count event before}
    (action : @RuntimeRegisterAction.Checked dependencies program sources caller block start count event before)
    (source : SourceHistory) : Option (List SourceHistory) :=
  (Qleisli.RuntimeSparseBlockEncoding.sourceRegister action source.operator).map fun operator =>
    [{source with owners := action.after, operator}]

/-- An original ordinary gap leaves the source owner/operator state as is.
Its SSA values are checked against the resulting actual history. -/
def withSparseGaps {dependencies program block}
    (other : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .gap _ => some [source]
  | _ => other prior step source

noncomputable def withSparseSteps {dependencies program block}
    (other : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.structural action) => structuralResult action source
  | .pure (.register _ action) => registerResult action source
  | _ => withSparseGaps other prior step source

def NeedsSparseSourceAction {dependencies program block} : @Step dependencies program block → Prop
  | .pure (.structural _) | .pure (.register ..) | .gap _ => False
  | _ => True

private theorem structural_refines {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.structural action)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.structural action)))
    {chunk source history outputs}
    (read : readOps block.fuel action.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (action.interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs action.interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    ∃ expected, structuralResult action source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs action.interval.after ownerAfter ordinaryAfter) expected outputs := by
  rcases owners with ⟨rfl,rfl⟩
  cases ordinary
  obtain ⟨ownerState,hidden,bits,values,_,_,_,input,represented⟩ := agrees
  obtain ⟨rfl,kept,output,operator,sourceRead,resultRepresents⟩ :=
    original_history action input inherited inputs _ history source.operator values represented read executed
  refine ⟨[{source with owners := action.after, operator}],?_,.cons
    ⟨rfl,hidden,bits,kept,_,action.afterFrame,action.resultBindings,output,resultRepresents⟩ .nil⟩
  simp only [structuralResult,ownerState,sourceRead,Option.map_some]

private theorem register_refines {dependencies program sources caller block start count event before}
    (location : RuntimeSourceEvent.Location (.registerPrimitive event) start count)
    (action : @RuntimeRegisterAction.Checked dependencies program sources caller block start count event before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.register location action)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.register location action)))
    {chunk source history outputs}
    (read : readOps block.fuel action.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (action.interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs action.interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    ∃ expected, registerResult action source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs action.interval.after ownerAfter ordinaryAfter) expected outputs := by
  rcases owners with ⟨rfl,rfl⟩
  cases ordinary
  obtain ⟨_,hidden,bits,values,_,_,_,input,represented⟩ := agrees
  obtain ⟨frames,rfl,kept⟩ := Qleisli.RuntimeLiteralHistory.register_history location action
    inherited inputs _ history values read executed
  obtain ⟨output,whole⟩ := Qleisli.RuntimeSparseBlockEncoding.original_register_action action input frames
  obtain ⟨operator,sourceRead,corresponds⟩ := whole source.operator
  refine ⟨[{source with owners := action.after, operator}],?_,.cons
    ⟨rfl,hidden,bits,kept,_,action.afterFrame,action.sameFrame,output,?_⟩ .nil⟩
  · simp only [registerResult,sourceRead,Option.map_some]
  · intro column row bounded
    have originalBound : row < 2^action.interval.before.quantum.frame.length := by simpa only [frames] using bounded
    exact (represented column row originalBound).trans (corresponds row column)

private theorem gap_refines {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.gap gap))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.gap gap))
    {chunk source history outputs}
    (read : readOps block.fuel gap.checked.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (gap.checked.interval.after.quantum.reference,chunk))
    (writes : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) chunk)
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs gap.checked.interval.before
      ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs gap.checked.interval.after
      ownerAfter ordinaryAfter) [source] outputs := by
  rcases owners with ⟨rfl,rfl⟩
  rcases ordinary with ⟨rfl,rfl⟩
  obtain ⟨ownerState,hidden,bits,values,_,_,_,input,represented⟩ := agrees
  have gapStep : ∃ result, run dependencies block.fuel chunk history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      ScopedOrdinaryAgrees inherited inputs gap.checked.interval.after gap.ssa result := by
    cases inherited with
    | none =>
      obtain ⟨result,ran,kept,unchanged,ordinary,support⟩ :=
        original_gap_values_with_inherited gap inputs history (fun _ => False) values.1
          (fun _ member => .inr (values.2 member)) read (fun _ _ _ _ impossible => impossible)
      exact ⟨result,ran,kept,unchanged,ordinary,fun _ member => (support member).resolve_left id⟩
    | some holds =>
      exact original_gap_values_with_inherited gap inputs history holds values.1 values.2 read writes
  obtain ⟨result,ran,hiddenKept,operatorKept,valuesAfter⟩ := gapStep
  have results := Option.some.inj (executed.symm.trans ran)
  subst outputs
  have retains := run_retains_values _ _ _ _ ran result List.mem_cons_self
  have bindings := RuntimeBoundaryOwnerEvidence.check_bindings gap.afterFrame gap.afterRead
  refine .cons ⟨ownerState,hiddenKept.trans hidden,measurementBits_retains _ retains bits,
    valuesAfter,_,gap.afterFrame,bindings,input,?_⟩ .nil
  intro column row bound
  rw [operatorKept,gap.quantum]
  exact represented column row (by simpa only [gap.quantum] using bound)

/-- Connect all four structural constructors to the same ordered arm
induction used for the other source steps. -/
theorem sourceStep_with_scoped_structure {dependencies program block}
    (steps : List (@Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : Step dependencies program block → Prop)
    (other : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsSparseSourceAction step)
      other (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withSparseSteps other) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case gap gap =>
    exact ⟨[source],rfl,gap_refines gap inputs inherited owners ordinary read writes agrees executed⟩
  case pure node =>
    cases node
    case structural action =>
      exact structural_refines action inputs inherited owners ordinary read agrees executed
    case register location action =>
      exact register_refines location action inputs inherited owners ordinary read agrees executed
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

/-- Connect all four structural constructors to the same ordered arm
induction used for the other source steps. -/
theorem sourceStep_with_sparse_structure {dependencies program block}
    (steps : List (@Step dependencies program block)) (inputs : List Nat)
    (certifies : Step dependencies program block → Prop)
    (other : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsSparseSourceAction step)
      other (fun _ => SemanticHistoryAgrees inputs)) :
    StepRefinement steps certifies (withSparseSteps other) (fun _ => SemanticHistoryAgrees inputs) :=
  sourceStep_with_scoped_structure steps inputs none certifies other remaining

/-- Every actual step in a structural sequence or ordinary gap uses the same
sparse invariant, including after an intermediate structural join. -/
theorem Execution.sparse_structure_refinement {dependencies program block initial final steps events incoming results}
    (execution : @Execution dependencies program block initial steps final events incoming results)
    {ownerStart ownerEnd : RuntimeStructuralAction.SourceState}
    {ordinaryStart ordinaryEnd : RuntimeOrdinaryBody.State}
    (owners : RuntimeNamedSourceFlow.Run ownerStart steps ownerEnd)
    (ordinary : OrdinaryRun ordinaryStart steps ordinaryEnd)
    (inputs : List Nat) {sourceIncoming : List SourceHistory}
    (structural : ∀ first ∈ steps, ¬ NeedsSparseSourceAction first)
    (starts : List.Forall₂ (SemanticHistoryAgrees inputs initial ownerStart ordinaryStart) sourceIncoming incoming) :
    ∃ expected, runSourceHistories (withSparseSteps (fun _ _ _ => none)) [] steps sourceIncoming = some expected ∧
      List.Forall₂ (SemanticHistoryAgrees inputs final ownerEnd ordinaryEnd) expected results := by
  have remaining : StepRefinement steps
      (fun step => (¬ NeedsSparseSourceAction step) ∧ NeedsSparseSourceAction step)
      (fun _ _ _ => none) (fun _ => SemanticHistoryAgrees inputs) := by
    intro _ _ _ _ impossible
    exact False.elim (impossible.1 impossible.2)
  exact execution.ordered_refinement owners ordinary (withSparseSteps (fun _ _ _ => none))
    (fun _ => SemanticHistoryAgrees inputs) [] (fun step => ¬ NeedsSparseSourceAction step)
    structural (sourceStep_with_sparse_structure steps inputs _ _ remaining) starts

/-- The written return order reindexes the same sparse source operator on
every finite physical row and retains its original history. -/
theorem sparse_return_refines {state roles before ordinary}
    (inputs : List Nat) {inherited : Option (Nat → Prop)}
    (returned : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered roles state before.bindings) returned)
    {source history}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs state before ordinary source history) :
    SemanticHistoryAgreesWithInherited inherited inputs state {before with bindings := returned.bindings} ordinary
      (returnHistory returned.bindings source) history := by
  obtain ⟨owners,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
  have readBound : RuntimeInterval.Computed
      (RuntimePureBody.reordered roles state checked.bindings) returned := bindings.symm ▸ read
  have permutation : returned.bindings.Perm before.bindings :=
    bindings ▸ RuntimeLiteralHistory.return_permutation checked returned readBound
  have unique : before.bindings.Nodup := bindings ▸
    (List.Pairwise.of_map (fun binding : RuntimeOwnerMap.Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun b : RuntimeOwnerMap.Binding => b.port.token) same))
      checked.tokensDistinct)
  obtain ⟨output⟩ := RuntimeSemanticForest.frame_exists (fun binding member => input.available binding
    (permutation.subset member))
  refine ⟨by simp [returnHistory,owners],hidden,bits,values,_,returned,rfl,output,?_⟩
  intro column row bound
  have original := represented column row bound
  have order := RuntimeSemanticForest.regroup_action input output permutation.symm unique state.quantum.frame
    source.operator row column
  simpa only [returnHistory,owners,RuntimeLiteralHistory.sourceReturn] using original.trans order

def sparseArmEncodingLaws (inputs : List Nat) (inherited : Option (Nat → Prop) := none) :
    ArmEncodingLaws SemanticHistoryEncoding inputs inherited :=
  ⟨sparse_history_at_arm_entry inputs (inherited := inherited),
    sparse_return_refines inputs (inherited := inherited)⟩

#print axioms HistoryAgrees.toSemantic
#print axioms sourceStep_with_scoped_structure
#print axioms sourceStep_with_sparse_structure
#print axioms Execution.sparse_structure_refinement
#print axioms sparse_return_refines
end Qleisli.RuntimeLiteralBody
