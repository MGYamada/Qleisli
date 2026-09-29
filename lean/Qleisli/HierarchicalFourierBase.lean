import Qleisli.HierarchicalFourierStage
import QleisliKernel.Hierarchical.FourierBase

/-! Constructed semantics of the actual one-bit recursive Fourier base.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The empty register remains an owner. Inserting a mathematical identity into
the coefficient proof does not insert a node into the checked artifact. -/

namespace Qleisli.HierarchicalFourierBase
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary
open HierarchicalDiagonal HierarchicalGradient HierarchicalFourier
open HierarchicalFourierStage
open scoped BigOperators Matrix

noncomputable def realize (s : FourierStage.Step) (h : Operator) : Operator :=
  apply s.root.interface .sequence
    [apply s.enter.interface (.rewire (Structural.axisMap s.enter.interface)) [],
     apply s.first.interface .tensor [h,idle s.idleLow],
     apply s.last.interface .tensor [idle s.idleHigh,idle s.child],
     apply s.leave.interface (.rewire (Structural.axisMap s.leave.interface)) []]

theorem realize_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index fuel : Nat) (s : FourierStage.Step) (h : Operator)
    (bound : FourierBase.Bound artifact index s) (valid : FourierBase.shape s = true)
    (he : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.hIndex = some h) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) index = some (realize s h) := by
  obtain ⟨root,rootBody,enter,first,last,leave,_,low,high,child,enterBody,firstBody,lastBody,leaveBody⟩ := bound
  simp only [FourierBase.shape,FourierStage.shape,Bool.and_eq_true] at valid
  have hMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.hIndex h he (fuel+1) (by omega)
  have lowEval := idle_evaluates leaves artifact s.idleLowIndex fuel s.idleLow low (by tauto)
  have highEval := idle_evaluates leaves artifact s.idleHighIndex fuel s.idleHigh high (by tauto)
  have childEval := idle_evaluates leaves artifact s.childIndex fuel s.child child (by tauto)
  have firstEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.firstIndex s.first .tensor [s.hIndex,s.idleLowIndex] first (by simp [physicalCode,firstBody])
  have lastEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.lastIndex s.last .tensor [s.idleHighIndex,s.childIndex] last (by simp [physicalCode,lastBody])
  have enterEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.enterIndex s.enter (.rewire (Structural.axisMap s.enter.interface)) [] enter (by simp [physicalCode,enterBody])
  have leaveEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.leaveIndex s.leave (.rewire (Structural.axisMap s.leave.interface)) [] leave (by simp [physicalCode,leaveBody])
  have rootEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+2)
    index s.root .sequence [s.enterIndex,s.firstIndex,s.lastIndex,s.leaveIndex]
    root (by simp [physicalCode,rootBody])
  simp only [HierarchicalFiniteEvaluation.physical] at *
  simp only [List.mapM_nil,bind,Option.bind,pure] at enterEval leaveEval
  simp [hMore,lowEval] at firstEval
  simp [highEval,childEval] at lastEval
  simp [enterEval,firstEval,lastEval,leaveEval] at rootEval
  exact rootEval

theorem insert_identity (s : FourierStage.Step) (h : Operator)
    (valid : FourierStage.shape 0 s = true) :
    matrixAt 1 1 (realize s h) =
      matrixAt 1 1 (HierarchicalFourierStage.realize s h (idle s.first) (idle s.child)) := by
  have g := HierarchicalFourierStage.shape_geometry 0 s valid
  let enter := apply s.enter.interface (.rewire (Structural.axisMap s.enter.interface)) []
  let first := apply s.first.interface .tensor [h,idle s.idleLow]
  let last := apply s.last.interface .tensor [idle s.idleHigh,idle s.child]
  let leave := apply s.leave.interface (.rewire (Structural.axisMap s.leave.interface)) []
  have ew : enter.inputWidth = 1 ∧ enter.outputWidth = 1 := ⟨g.enterInput,g.enterOutput⟩
  have fw : first.inputWidth = 1 ∧ first.outputWidth = 1 := ⟨g.firstInput,g.firstOutput⟩
  have lw : last.inputWidth = 1 ∧ last.outputWidth = 1 := by
    change width s.last.interface.inputs = 1 ∧ width s.last.interface.outputs = 1
    rw [g.lastInterface]
    exact ⟨g.firstInput,g.firstOutput⟩
  have xw : leave.inputWidth = 1 ∧ leave.outputWidth = 1 := ⟨g.leaveInput,g.leaveOutput⟩
  have middle := idle_at s.first 1 g.firstInput g.firstOutput
  have four : ∀ c ∈ [enter,first,last,leave], c.inputWidth = 1 ∧ c.outputWidth = 1 := by
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> assumption
  have five : ∀ c ∈ [enter,first,idle s.first,last,leave], c.inputWidth = 1 ∧ c.outputWidth = 1 := by
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ew
    · exact fw
    · exact ⟨middle.1,middle.2.1⟩
    · exact lw
    · exact xw
  change matrixAt 1 1 (apply s.root.interface .sequence [enter,first,last,leave]) =
    matrixAt 1 1 (apply s.root.interface .sequence [enter,first,idle s.first,last,leave])
  rw [apply_sequence_matrix _ 1 _ g.rootInput g.rootOutput four,
    apply_sequence_matrix _ 1 _ g.rootInput g.rootOutput five]
  simp [middle.2.2]

theorem realize_fourier (s : FourierStage.Step) (h : Operator)
    (valid : FourierBase.shape s = true) (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input) :
    matrixAt 1 1 (realize s h) = reversedFourier 1 := by
  have both : FourierStage.shape 0 s = true ∧ FourierStage.identity s.child = true := by
    simpa only [FourierBase.shape,Bool.and_eq_true] using valid
  have stage := both.1
  have g := HierarchicalFourierStage.shape_geometry 0 s stage
  have childValid : Gradient.register s.child 0 = true := by
    simp only [FourierStage.shape,Bool.and_eq_true] at stage
    tauto
  have childWidths := register_widths s.child 0 childValid
  have child := idle_at s.child 0 childWidths.1 childWidths.2
  have childMatrix : matrixAt 0 0 (idle s.child) = reversedFourier 0 := by
    rw [child.2.2]
    ext output input
    have same : output = input := Subsingleton.elim _ _
    simp [reversedFourier,number,phase_zero,same]
  have diagonal : At 1 (idle s.first) (fun bits : Fin 1 → Bool => if bits 0 then
      phase (number 0 (fun i => bits i.succ)) 1 else 1) := by
    simpa only [number,phase_zero,ite_self] using idle_at s.first 1 g.firstInput g.firstOutput
  rw [insert_identity s h stage]
  exact HierarchicalFourierStage.realize_fourier 0 s h (idle s.first) (idle s.child)
    stage hi ho hentry diagonal childMatrix

theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index remaining fuel : Nat) (pending : FourierStage.Pending)
    (accepted : FourierBase.inspect artifact index remaining = .ok pending)
    (h : Operator)
    (he : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel pending.step.hIndex = some h)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) index = some actual ∧
      actual.inputWidth = 1 ∧ actual.outputWidth = 1 ∧ matrixAt 1 1 actual = reversedFourier 1 := by
  obtain ⟨_,_,bound,valid⟩ := FourierBase.inspect_sound artifact index remaining pending accepted
  have both : FourierStage.shape 0 pending.step = true ∧ FourierStage.identity pending.step.child = true := by
    simpa only [FourierBase.shape,Bool.and_eq_true] using valid
  have g := HierarchicalFourierStage.shape_geometry 0 pending.step both.1
  exact ⟨realize pending.step h,realize_evaluates leaves artifact index fuel pending.step h bound valid he,
    g.rootInput,g.rootOutput,realize_fourier pending.step h valid hi ho hentry⟩

end Qleisli.HierarchicalFourierBase
