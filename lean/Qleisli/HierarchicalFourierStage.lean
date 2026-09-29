import Qleisli.HierarchicalFourier
import QleisliKernel.Hierarchical.FourierStage

/-! Coefficients of inspected actual five-node Fourier stages.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The remaining H, controlled-gradient and recursive-child equations refer to
actual physical evaluations at the bound indices. There is no whole-graph
semantic environment, probability-only equality or producer matrix premise. -/

namespace Qleisli.HierarchicalFourierStage
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary
open HierarchicalDiagonal HierarchicalGradient HierarchicalFourier
open scoped BigOperators Matrix

theorem closed_bit_widths (d : Definition) (valid : FourierStage.closedBit d = true) :
    width d.interface.inputs = 1 ∧ width d.interface.outputs = 1 := by
  simp only [FourierStage.closedBit,Bool.and_eq_true,beq_iff_eq] at valid
  exact ⟨valid.2,by rw [← valid.1.1.2]; exact valid.2⟩

structure Geometry (n : Nat) (s : FourierStage.Step) : Prop where
  rootInput : width s.root.interface.inputs = n+1
  rootOutput : width s.root.interface.outputs = n+1
  enterInput : width s.enter.interface.inputs = n+1
  enterOutput : width s.enter.interface.outputs = n+1
  firstInput : width s.first.interface.inputs = n+1
  firstOutput : width s.first.interface.outputs = n+1
  leaveInput : width s.leave.interface.inputs = n+1
  leaveOutput : width s.leave.interface.outputs = n+1
  hInput : width s.h.interface.inputs = 1
  hOutput : width s.h.interface.outputs = 1
  idleLowInput : width s.idleLow.interface.inputs = n
  idleLowOutput : width s.idleLow.interface.outputs = n
  idleHighInput : width s.idleHigh.interface.inputs = 1
  idleHighOutput : width s.idleHigh.interface.outputs = 1
  lastInterface : s.last.interface = s.first.interface
  forward : Structural.axisMap s.enter.interface = Gradient.highAxes n
  backward : Structural.axisMap s.leave.interface = Gradient.lowAxes n

theorem shape_geometry (n : Nat) (s : FourierStage.Step)
    (valid : FourierStage.shape n s = true) : Geometry n s := by
  simp only [FourierStage.shape,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at valid
  have root := register_widths s.root (n+1) (by tauto)
  have child := register_widths s.child n (by tauto)
  have low := register_widths s.idleLow n (by tauto)
  have h := closed_bit_widths s.h (by tauto)
  have high := closed_bit_widths s.idleHigh (by tauto)
  have ei : s.enter.interface.inputs = s.root.interface.inputs := by tauto
  have eo : s.enter.interface.outputs = NodeTyping.append s.h.interface.inputs s.child.interface.inputs := by tauto
  have first : s.first.interface = ⟨s.enter.interface.outputs,s.enter.interface.outputs⟩ := by tauto
  have leave : s.leave.interface = Structural.swapped s.enter.interface := by tauto
  have entry : width s.enter.interface.inputs = n+1 := by rw [ei,root.1]
  have exit : width s.enter.interface.outputs = n+1 := by
    rw [eo,HierarchicalTyping.width_append,h.1,child.1,Nat.add_comm]
  exact ⟨root.1,root.2,entry,exit,by simpa [first] using exit,by simpa [first] using exit,
    by simpa [leave,Structural.swapped] using exit,by simpa [leave,Structural.swapped] using entry,
    h.1,h.2,low.1,low.2,high.1,high.2,by tauto,by tauto,by tauto⟩

noncomputable def idle (d : Definition) : Operator := apply d.interface .identity []

theorem idle_at (d : Definition) (n : Nat)
    (hi : width d.interface.inputs = n) (ho : width d.interface.outputs = n) :
    At n (idle d) (fun _ => 1) := by
  refine ⟨hi,ho,?_⟩
  ext output input
  simp [idle,matrixAt,apply,bounded,raw,hi,ho,Matrix.diagonal_apply,List.ofFn_inj]

theorem idle_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index fuel : Nat) (d : Definition)
    (found : artifact.definitions[index]? = some d) (valid : FourierStage.identity d = true) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+1) index = some (idle d) := by
  cases body : d.body <;> simp only [FourierStage.identity,body,Bool.false_eq_true] at valid
  rename_i map
  have code : physicalCode d = some (.rewire map.axes.toList,[]) := by simp [physicalCode,body]
  rw [HierarchicalFiniteEvaluation.physical_step algebra leaves artifact fuel index d _ [] found code]
  simp only [List.mapM_nil,bind,Option.bind,pure]
  exact congrArg some (identity_rewire d.interface map valid)

noncomputable def realize (s : FourierStage.Step) (h gradient child : Operator) : Operator :=
  apply s.root.interface .sequence
    [apply s.enter.interface (.rewire (Structural.axisMap s.enter.interface)) [],
     apply s.first.interface .tensor [h,idle s.idleLow],gradient,
     apply s.last.interface .tensor [idle s.idleHigh,child],
     apply s.leave.interface (.rewire (Structural.axisMap s.leave.interface)) []]

theorem realize_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index fuel : Nat) (s : FourierStage.Step) (h gradient child : Operator)
    (bound : FourierStage.Bound artifact index s)
    (lowIdentity : FourierStage.identity s.idleLow = true)
    (highIdentity : FourierStage.identity s.idleHigh = true)
    (he : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.hIndex = some h)
    (ge : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.gradientIndex = some gradient)
    (ce : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.childIndex = some child) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) index = some (realize s h gradient child) := by
  obtain ⟨root,rootBody,enter,first,_,last,leave,_,low,high,_,enterBody,firstBody,lastBody,leaveBody⟩ := bound
  have hMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.hIndex h he (fuel+1) (by omega)
  have gMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.gradientIndex gradient ge (fuel+2) (by omega)
  have cMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.childIndex child ce (fuel+1) (by omega)
  have lowEval := idle_evaluates leaves artifact s.idleLowIndex fuel s.idleLow low lowIdentity
  have highEval := idle_evaluates leaves artifact s.idleHighIndex fuel s.idleHigh high highIdentity
  have firstEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.firstIndex s.first .tensor [s.hIndex,s.idleLowIndex] first (by simp [physicalCode,firstBody])
  have lastEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.lastIndex s.last .tensor [s.idleHighIndex,s.childIndex] last (by simp [physicalCode,lastBody])
  have enterEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.enterIndex s.enter (.rewire (Structural.axisMap s.enter.interface)) [] enter (by simp [physicalCode,enterBody])
  have leaveEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1)
    s.leaveIndex s.leave (.rewire (Structural.axisMap s.leave.interface)) [] leave (by simp [physicalCode,leaveBody])
  have rootEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+2)
    index s.root .sequence [s.enterIndex,s.firstIndex,s.gradientIndex,s.lastIndex,s.leaveIndex]
    root (by simp [physicalCode,rootBody])
  simp only [HierarchicalFiniteEvaluation.physical] at *
  simp only [List.mapM_nil,bind,Option.bind,pure] at enterEval leaveEval
  simp [hMore,lowEval] at firstEval
  simp [highEval,cMore] at lastEval
  simp [enterEval,firstEval,gMore,lastEval,leaveEval] at rootEval
  exact rootEval

/-- Exact coefficient law for the actual bound stage, conditional only on its
three nontrivial actual children. Inspection alone cannot satisfy these premises. -/
theorem realize_fourier (n : Nat) (s : FourierStage.Step) (h gradient child : Operator)
    (valid : FourierStage.shape n s = true)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input)
    (diagonal : At (n+1) gradient (fun bits => if bits 0 then
      phase (number n (fun i => bits i.succ)) (n+1) else 1))
    (recursive : matrixAt n n child = reversedFourier n) :
    matrixAt (n+1) (n+1) (realize s h gradient child) = reversedFourier (n+1) := by
  have g := shape_geometry n s valid
  have checked := routed_stage_fourier s.root.interface s.enter.interface s.first.interface s.leave.interface
    n h (idle s.idleLow) gradient (idle s.idleHigh) child
    g.rootInput g.rootOutput g.enterInput g.enterOutput g.firstInput g.firstOutput g.leaveInput g.leaveOutput
    hi ho hentry (idle_at _ n g.idleLowInput g.idleLowOutput)
    (idle_at _ 1 g.idleHighInput g.idleHighOutput) diagonal recursive
  simpa only [realize,routedStage,g.forward,g.backward,g.lastInterface] using checked

theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (n index remaining fuel : Nat) (pending : FourierStage.Pending)
    (accepted : FourierStage.inspect artifact n index remaining = .ok pending)
    (h gradient child : Operator)
    (he : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel pending.step.hIndex = some h)
    (ge : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel pending.step.gradientIndex = some gradient)
    (ce : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel pending.step.childIndex = some child)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input)
    (diagonal : At (n+1) gradient (fun bits => if bits 0 then
      phase (number n (fun i => bits i.succ)) (n+1) else 1))
    (recursive : matrixAt n n child = reversedFourier n) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) index = some actual ∧
      actual.inputWidth = n+1 ∧ actual.outputWidth = n+1 ∧
      matrixAt (n+1) (n+1) actual = reversedFourier (n+1) := by
  obtain ⟨_,_,_,_,bound,valid⟩ := FourierStage.inspect_sound artifact n index remaining pending accepted
  have low : FourierStage.identity pending.step.idleLow = true := by
    simp only [FourierStage.shape,Bool.and_eq_true] at valid
    tauto
  have high : FourierStage.identity pending.step.idleHigh = true := by
    simp only [FourierStage.shape,Bool.and_eq_true] at valid
    tauto
  have g := shape_geometry n pending.step valid
  exact ⟨realize pending.step h gradient child,
    realize_evaluates leaves artifact index fuel pending.step h gradient child bound low high he ge ce,
    g.rootInput,g.rootOutput,realize_fourier n pending.step h gradient child valid hi ho hentry diagonal recursive⟩

end Qleisli.HierarchicalFourierStage
