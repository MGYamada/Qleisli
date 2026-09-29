import Qleisli.HierarchicalFourierStage
import QleisliKernel.Hierarchical.Hadamard

/-! Exact H requests bound to actual finite bytes and owner renaming.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The finite-reader equation is an explicit transitional obligation. Unitarity,
probabilities, a producer's matrix or a serialized success flag cannot replace it. -/

namespace Qleisli.HierarchicalHadamard
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary
open HierarchicalFourier HierarchicalFourierStage
open scoped Matrix

def IsHadamard (h : Operator) : Prop :=
  h.inputWidth = 1 ∧ h.outputWidth = 1 ∧
    ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input

/-- Every requested byte and interface is consumed by the actual partial reader.
The independent target includes H's sign and global phase. -/
def Equation (leaves : HierarchicalFiniteEvaluation.Leaves Operator) (r : Hadamard.Request) : Prop :=
  ∃ h, leaves.implementation r.leaf.interface r.program = some h ∧ IsHadamard h

structure Geometry (r : Hadamard.Request) : Prop where
  rootInput : width r.root.interface.inputs = 1
  rootOutput : width r.root.interface.outputs = 1
  renameInput : width r.rename.interface.inputs = 1
  renameOutput : width r.rename.interface.outputs = 1
  axes : r.routing.axes = #[0]

theorem shape_geometry (r : Hadamard.Request) (valid : Hadamard.shape r = true) : Geometry r := by
  simp only [Hadamard.shape,Bool.and_eq_true,beq_iff_eq] at valid
  have root := closed_bit_widths r.root (by tauto)
  have ri : r.rename.interface.inputs = r.leaf.interface.outputs := by tauto
  have ro : r.rename.interface.outputs = r.root.interface.outputs := by tauto
  have lo : width r.leaf.interface.outputs = 1 := by
    change (wires r.leaf.interface.outputs).size = 1
    tauto
  exact ⟨root.1,root.2,by rw [ri,lo],by rw [ro,root.2],by tauto⟩

theorem rewire_one_matrix (interface : Interface)
    (hi : width interface.inputs = 1) (ho : width interface.outputs = 1) :
    matrixAt 1 1 (apply interface (.rewire [0]) []) = 1 := by
  ext output input
  have equal : output = input ↔ output 0 = input 0 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; rw [Fin.eq_zero i]; exact h
  simp [matrixAt,apply,bounded,raw,hi,ho,List.ofFn_succ,Matrix.one_apply,equal]

noncomputable def realize (r : Hadamard.Request) (h : Operator) : Operator :=
  apply r.root.interface .sequence [h,apply r.rename.interface (.rewire r.routing.axes.toList) []]

theorem realize_hadamard (r : Hadamard.Request) (h : Operator)
    (valid : Hadamard.shape r = true) (hmodel : IsHadamard h) : IsHadamard (realize r h) := by
  have g := shape_geometry r valid
  refine ⟨g.rootInput,g.rootOutput,?_⟩
  have ready : ∀ c ∈ [h,apply r.rename.interface (.rewire r.routing.axes.toList) []],
      c.inputWidth = 1 ∧ c.outputWidth = 1 := by
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨hmodel.1,hmodel.2.1⟩
    · exact ⟨g.renameInput,g.renameOutput⟩
  have matrix : matrixAt 1 1 (realize r h) = matrixAt 1 1 h := by
    rw [realize,apply_sequence_matrix _ 1 _ g.rootInput g.rootOutput ready]
    simp only [List.foldl_cons,List.foldl_nil,g.axes,
      rewire_one_matrix _ g.renameInput g.renameOutput,Matrix.mul_one,Matrix.one_mul]
  intro output input
  rw [matrix]
  exact hmodel.2.2 output input

theorem bound_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index : Nat) (r : Hadamard.Request)
    (bound : Hadamard.Bound artifact index r) (valid : Hadamard.shape r = true)
    (equation : Equation leaves r) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact 2 index = some actual ∧
      IsHadamard actual := by
  obtain ⟨root,rootBody,leaf,rename,leafBody,renameBody⟩ := bound
  obtain ⟨h,read,hmodel⟩ := equation
  have leafEval : HierarchicalFiniteEvaluation.physical algebra leaves artifact 1 r.leafIndex = some h := by
    simp [HierarchicalFiniteEvaluation.physical,HierarchicalFiniteEvaluation.evaluate,
      HierarchicalFiniteEvaluation.definition,leaf,leafBody,read]
  have renameEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact 0 r.renameIndex r.rename
    (.rewire r.routing.axes.toList) [] rename (by simp [physicalCode,renameBody])
  have rootEval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact 1 index r.root
    .sequence [r.leafIndex,r.renameIndex] root (by simp [physicalCode,rootBody])
  simp only [List.mapM_nil,bind,Option.bind,pure] at renameEval
  simp [leafEval,renameEval] at rootEval
  exact ⟨realize r h,rootEval,realize_hadamard r h valid hmodel⟩

theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index remaining : Nat) (pending : Hadamard.Pending)
    (accepted : Hadamard.inspect artifact index remaining = .ok pending)
    (equation : Equation leaves pending.request) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact 2 index = some actual ∧
      IsHadamard actual := by
  obtain ⟨_,_,bound,valid,_⟩ := Hadamard.inspect_sound artifact index remaining pending accepted
  exact bound_evaluates leaves artifact index pending.request bound valid equation

end Qleisli.HierarchicalHadamard
